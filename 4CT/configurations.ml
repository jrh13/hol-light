(* ========================================================================= *)
(* 4CT/configurations.ml                                                     *)
(*                                                                           *)
(* configurations.v: the 633 reducible configurations.  Each cfNNN :         *)
(* (cpstep)list # (num)list is a construction program with its contract (Coq *)
(* cfprog, cfcontract_ref); the_configs lists them in Coq's order,           *)
(* the_configs_sym gives the symmetry flags (the starred Config entries of   *)
(* the Coq file), and LENGTH_THE_CONFIGS says there are 633.  The hypothesis *)
(* reducibility of four_color.ml is !cf. MEM cf the_configs ==>              *)
(* check_reducible cf, discharged by the Part 2 computation.  The data is    *)
(* generated and should not be edited by hand.                               *)
(* ========================================================================= *)

needs "4CT/cfmap.ml";;

let cf001 = new_definition
 `cf001 = ([CpH; CpR 3; CpH; CpR 5; CpH; CpR 5; CpY; CpR 4; CpH;
            CpR 4; CpY; CpR 2;
     CpY; CpR 1; CpY],
     [13])`;;
let cf002 = new_definition
 `cf002 = ([CpH; CpR 2; CpH; CpR 6; CpY; CpR 4; CpH; CpR 1; CpY;
            CpR 4; CpH; CpR 4;
     CpY; CpR 2; CpY; CpY],
     [6])`;;
let cf003 = new_definition
 `cf003 = ([CpH; CpR 1; CpH; CpR 6; CpH; CpR 1; CpY; CpR 4; CpH;
            CpR 6; CpH; CpR 6;
     CpH; CpR 6; CpY; CpY; CpR 4; CpH; CpR 1; CpY; CpR 3; CpY; CpR 1; CpY],
     [17])`;;
let cf004 = new_definition
 `cf004 = ([CpH; CpR 2; CpH; CpR 7; CpY; CpR 5; CpH; CpR 1; CpY;
            CpR 4; CpH; CpR 1;
     CpY; CpR 4; CpY; CpR 2; CpY; CpR 2; CpY],
     [1; 2; 12; 13])`;;
let cf005 = new_definition
 `cf005 = ([CpH; CpR 6; CpH; CpR 1; CpY; CpR 5; CpH; CpR 1; CpY;
            CpR 4; CpH; CpR 1;
     CpY; CpR 4; CpH; CpR 4; CpY; CpR 2; CpY; CpY],
     [10])`;;
let cf006 = new_definition
 `cf006 = ([CpH; CpR 2; CpH; CpR 8; CpY; CpR 4; CpH; CpR 7; CpH;
            CpR 2; CpH; CpR 7;
     CpY; CpR 6; CpH; CpR 1; CpY; CpR 1; CpY; CpR 2; CpH; CpR 4; CpY; CpR 2;
     CpY; CpY],
     [19])`;;
let cf007 = new_definition
 `cf007 = ([CpH; CpR 3; CpH; CpR 8; CpH; CpR 8; CpY; CpR 6; CpH;
            CpR 1; CpY; CpR 5;
     CpH; CpR 1; CpY; CpR 5; CpY; CpR 3; CpY; CpR 2; CpY; CpY],
     [17])`;;
let cf008 = new_definition
 `cf008 = ([CpH; CpR 2; CpH; CpR 7; CpY; CpR 3; CpH; CpR 6; CpY;
            CpR 2; CpH; CpR 1;
     CpH; CpR 1; CpY; CpH; CpR 4; CpY; CpY; CpR 1; CpY],
     [6])`;;
let cf009 = new_definition
 `cf009 = ([CpH; CpR 8; CpH; CpR 1; CpY; CpR 7; CpH; CpR 7; CpH;
            CpR 1; CpY; CpR 5;
     CpH; CpR 7; CpY; CpR 3; CpH; CpR 6; CpH; CpR 6; CpY; CpY; CpY; CpR 3;
     CpY; CpY],
     [26])`;;
let cf010 = new_definition
 `cf010 = ([CpH; CpR 2; CpH; CpR 9; CpY; CpR 4; CpH; CpR 2; CpH;
            CpR 8; CpY; CpR 3;
     CpH; CpR 1; CpY; CpR 6; CpH; CpR 1; CpY; CpR 1; CpY; CpR 2; CpH; CpR 4;
     CpY; CpR 2; CpY; CpY],
     [20])`;;
let cf011 = new_definition
 `cf011 = ([CpH; CpR 8; CpH; CpR 1; CpY; CpR 7; CpH; CpR 1; CpY;
            CpR 5; CpH; CpR 1;
     CpH; CpR 6; CpH; CpR 1; CpY; CpR 2; CpH; CpR 6; CpY; CpY; CpY; CpR 3;
     CpY; CpR 2; CpY],
     [1; 2; 8; 9])`;;
let cf012 = new_definition
 `cf012 = ([CpH; CpR 2; CpH; CpR 8; CpY; CpR 3; CpH; CpR 7; CpY;
            CpR 3; CpH; CpR 6;
     CpY; CpR 2; CpH; CpR 1; CpY; CpH; CpR 4; CpY; CpY; CpR 1; CpY],
     [6])`;;
let cf013 = new_definition
 `cf013 = ([CpH; CpR 3; CpH; CpR 9; CpH; CpR 9; CpY; CpR 7; CpH;
            CpR 1; CpY; CpR 5;
     CpH; CpR 2; CpH; CpR 7; CpY; CpR 6; CpY; CpR 4; CpY; CpR 3; CpY; CpR 2;
     CpY; CpR 1; CpY],
     [23])`;;
let cf014 = new_definition
 `cf014 = ([CpH; CpR 8; CpH; CpR 1; CpY; CpR 7; CpH; CpR 1; CpY;
            CpR 6; CpH; CpR 1;
     CpY; CpR 5; CpH; CpR 1; CpY; CpR 5; CpH; CpR 5; CpY; CpR 2; CpY; CpR 3;
     CpY; CpR 1; CpY],
     [14])`;;
let cf015 = new_definition
 `cf015 = ([CpH; CpR 9; CpH; CpR 1; CpY; CpR 8; CpH; CpR 8; CpH;
            CpR 1; CpY; CpR 7;
     CpH; CpR 1; CpY; CpR 6; CpH; CpR 7; CpY; CpR 2; CpH; CpR 6; CpY; CpY;
     CpY; CpR 3; CpY; CpR 2; CpY],
     [8; 9; 15; 16])`;;
let cf016 = new_definition
 `cf016 = ([CpH; CpR 2; CpH; CpR 10; CpY; CpR 3; CpH; CpR 9; CpY;
            CpR 5; CpH; CpR 8;
     CpH; CpR 2; CpH; CpR 8; CpY; CpR 6; CpH; CpR 1; CpH; CpR 1; CpY; CpR 1;
     CpY; CpR 1; CpY; CpR 3; CpY; CpR 2; CpY; CpR 1; CpY],
     [30])`;;
let cf017 = new_definition
 `cf017 = ([CpH; CpR 2; CpH; CpR 10; CpY; CpR 4; CpH; CpR 8; CpH;
            CpR 1; CpY; CpR 3;
     CpH; CpR 8; CpY; CpR 4; CpH; CpR 7; CpH; CpR 7; CpY; CpR 3; CpY; CpR 4;
     CpY; CpR 3; CpY; CpY; CpR 1; CpY],
     [26])`;;
let cf018 = new_definition
 `cf018 = ([CpH; CpR 9; CpH; CpR 1; CpY; CpR 8; CpH; CpR 1; CpY;
            CpR 6; CpH; CpR 2;
     CpH; CpR 8; CpY; CpR 6; CpH; CpR 1; CpY; CpR 6; CpH; CpR 6; CpY; CpR 3;
     CpY; CpR 3; CpY; CpY; CpR 1; CpY],
     [26])`;;
let cf019 = new_definition
 `cf019 = ([CpH; CpR 2; CpH; CpR 9; CpY; CpR 3; CpH; CpR 8; CpY;
            CpR 3; CpH; CpR 7;
     CpY; CpR 2; CpH; CpR 1; CpH; CpR 1; CpY; CpH; CpR 5; CpY; CpY; CpY;
     CpR 1; CpY],
     [6])`;;
let cf020 = new_definition
 `cf020 = ([CpH; CpR 10; CpH; CpR 1; CpY; CpR 9; CpH; CpR 1; CpY;
            CpR 8; CpH; CpR 7;
     CpH; CpR 2; CpH; CpR 9; CpY; CpR 5; CpY; CpR 3; CpH; CpR 7; CpH; CpR 7;
     CpY; CpY; CpY; CpR 3; CpY; CpR 1; CpY; CpR 2; CpY],
     [1; 2; 8; 9])`;;
let cf021 = new_definition
 `cf021 = ([CpH; CpR 2; CpH; CpR 10; CpY; CpR 3; CpH; CpR 9; CpY;
            CpR 3; CpH; CpR 8;
     CpY; CpR 3; CpH; CpR 7; CpY; CpR 2; CpH; CpR 1; CpY; CpH; CpR 5; CpY;
     CpY; CpY; CpR 1; CpY],
     [6])`;;
let cf022 = new_definition
 `cf022 = ([CpH; CpR 2; CpH; CpR 11; CpY; CpR 3; CpH; CpR 10; CpY; CpR 4; CpH;
     CpR 8; CpH; CpR 1; CpY; CpR 3; CpH; CpR 8; CpY; CpR 2; CpH; CpR 1; CpH;
     CpR 1; CpY; CpR 5; CpY; CpR 3; CpY; CpR 1; CpY; CpY; CpR 1; CpY],
     [29])`;;
let cf023 = new_definition
 `cf023 = ([CpH; CpR 2; CpH; CpR 12; CpY; CpR 3; CpH; CpR 11; CpY; CpR 3; CpH;
     CpR 2; CpH; CpR 10; CpY; CpR 3; CpH; CpR 9; CpY; CpR 5; CpY; CpR 6; CpH;
     CpR 1; CpH; CpR 1; CpY; CpR 1; CpY; CpR 1; CpY; CpR 3; CpY; CpR 2; CpY;
     CpR 1; CpY],
     [1; 2; 8; 9])`;;
let cf024 = new_definition
 `cf024 = ([CpH; CpR 2; CpH; CpR 7; CpY; CpR 5; CpH; CpR 1; CpY;
            CpR 5; CpH; CpR 5;
     CpH; CpR 5; CpY; CpR 3; CpY; CpY; CpY],
     [6])`;;
let cf025 = new_definition
 `cf025 = ([CpH; CpR 3; CpH; CpR 7; CpH; CpR 1; CpY; CpR 4; CpH;
            CpR 1; CpH; CpR 1;
     CpH; CpR 1; CpY; CpR 1; CpY; CpR 1; CpY; CpR 2; CpH; CpR 4; CpY; CpR 2;
     CpY; CpR 1; CpY],
     [25])`;;
let cf026 = new_definition
 `cf026 = ([CpH; CpR 7; CpH; CpR 1; CpY; CpR 3; CpH; CpR 7; CpY;
            CpR 4; CpH; CpR 5;
     CpH; CpR 1; CpY; CpR 2; CpY; CpR 3; CpY; CpR 1; CpY; CpR 2; CpY],
     [19])`;;
let cf027 = new_definition
 `cf027 = ([CpH; CpR 2; CpH; CpR 8; CpY; CpR 6; CpH; CpR 1; CpY;
            CpR 4; CpH; CpR 6;
     CpY; CpR 3; CpH; CpR 1; CpY; CpR 4; CpH; CpR 1; CpY; CpR 3; CpY; CpR 1;
     CpY],
     [6])`;;
let cf028 = new_definition
 `cf028 = ([CpH; CpR 2; CpH; CpR 9; CpY; CpR 4; CpH; CpR 3; CpH;
            CpR 7; CpH; CpR 1;
     CpY; CpR 5; CpH; CpR 1; CpH; CpR 1; CpY; CpR 1; CpY; CpR 1; CpY; CpR 1;
     CpY; CpR 2; CpY; CpR 1; CpY],
     [26])`;;
let cf029 = new_definition
 `cf029 = ([CpH; CpR 8; CpH; CpR 1; CpY; CpR 7; CpH; CpR 1; CpY;
            CpR 5; CpH; CpR 1;
     CpH; CpR 6; CpH; CpR 1; CpY; CpR 6; CpH; CpR 1; CpY; CpR 1; CpY; CpR 1;
     CpY; CpR 1; CpY; CpR 2; CpY],
     [4; 5; 21; 25])`;;
let cf030 = new_definition
 `cf030 = ([CpH; CpR 2; CpH; CpR 9; CpY; CpR 4; CpH; CpR 8; CpH;
            CpR 2; CpH; CpR 8;
     CpY; CpR 7; CpH; CpR 1; CpY; CpR 1; CpY; CpR 3; CpH; CpR 5; CpH; CpR 5;
     CpY; CpR 3; CpY; CpY; CpY],
     [19])`;;
let cf031 = new_definition
 `cf031 = ([CpH; CpR 2; CpH; CpR 9; CpY; CpR 6; CpH; CpR 8; CpH;
            CpR 2; CpH; CpR 8;
     CpY; CpR 2; CpH; CpR 7; CpY; CpY; CpR 5; CpH; CpR 1; CpY; CpR 4; CpH;
     CpR 1; CpY; CpR 3; CpY; CpR 1; CpY],
     [18])`;;
let cf032 = new_definition
 `cf032 = ([CpH; CpR 2; CpH; CpR 9; CpY; CpR 7; CpH; CpR 1; CpY;
            CpR 4; CpH; CpR 3;
     CpH; CpR 7; CpH; CpR 7; CpY; CpR 6; CpY; CpR 4; CpY; CpY; CpR 3; CpY;
     CpR 1; CpY],
     [23])`;;
let cf033 = new_definition
 `cf033 = ([CpH; CpR 3; CpH; CpR 9; CpH; CpR 9; CpY; CpR 6; CpH;
            CpR 2; CpH; CpR 8;
     CpY; CpR 6; CpH; CpR 1; CpY; CpR 6; CpY; CpR 4; CpY; CpY; CpR 2; CpY;
     CpR 2; CpY],
     [24])`;;
let cf034 = new_definition
 `cf034 = ([CpH; CpR 8; CpH; CpR 1; CpY; CpR 7; CpH; CpR 1; CpY;
            CpR 5; CpH; CpR 2;
     CpH; CpR 7; CpY; CpR 5; CpH; CpR 1; CpY; CpR 4; CpY; CpR 3; CpY; CpY;
     CpR 2; CpY],
     [15])`;;
let cf035 = new_definition
 `cf035 = ([CpH; CpR 2; CpH; CpR 9; CpY; CpR 7; CpH; CpR 1; CpY;
            CpR 6; CpH; CpR 1;
     CpY; CpR 5; CpH; CpR 6; CpY; CpR 4; CpY; CpR 4; CpH; CpR 4; CpY; CpR 2;
     CpY; CpY],
     [6])`;;
let cf036 = new_definition
 `cf036 = ([CpH; CpR 7; CpH; CpR 1; CpH; CpR 1; CpY; CpR 3; CpH;
            CpR 8; CpY; CpR 4;
     CpH; CpR 6; CpH; CpR 1; CpY; CpR 2; CpY; CpR 3; CpY; CpR 1; CpY; CpR 1;
     CpY; CpR 2; CpY],
     [23])`;;
let cf037 = new_definition
 `cf037 = ([CpH; CpR 2; CpH; CpR 9; CpY; CpR 7; CpH; CpR 1; CpY;
            CpR 5; CpH; CpR 2;
     CpH; CpR 7; CpY; CpR 6; CpH; CpR 6; CpY; CpR 4; CpY; CpR 2; CpY; CpR 2;
     CpY; CpR 1; CpY],
     [23])`;;
let cf038 = new_definition
 `cf038 = ([CpH; CpR 2; CpH; CpR 8; CpY; CpR 3; CpH; CpR 7; CpY;
            CpR 3; CpH; CpR 6;
     CpY; CpR 2; CpH; CpR 1; CpH; CpR 1; CpY; CpH; CpR 4; CpY; CpY; CpR 1;
     CpY],
     [10])`;;
let cf039 = new_definition
 `cf039 = ([CpH; CpR 2; CpH; CpR 10; CpY; CpR 3; CpH; CpR 9; CpY;
            CpR 3; CpH; CpR 3;
     CpH; CpR 7; CpH; CpR 1; CpY; CpR 6; CpH; CpR 1; CpY; CpR 1; CpY; CpR 1;
     CpY; CpR 1; CpY; CpR 2; CpY; CpR 1; CpY],
     [1; 2; 8; 9])`;;
let cf040 = new_definition
 `cf040 = ([CpH; CpR 2; CpH; CpR 10; CpY; CpR 4; CpH; CpR 2; CpH;
            CpR 9; CpY; CpR 3;
     CpH; CpR 8; CpY; CpR 5; CpH; CpR 1; CpH; CpR 1; CpY; CpR 1; CpY; CpR 1;
     CpY; CpR 1; CpY; CpR 2; CpY; CpR 1; CpY],
     [11; 12; 21; 26])`;;
let cf041 = new_definition
 `cf041 = ([CpH; CpR 2; CpH; CpR 10; CpY; CpR 5; CpH; CpR 2; CpH;
            CpR 9; CpY; CpR 3;
     CpH; CpR 1; CpY; CpR 7; CpH; CpR 1; CpY; CpR 1; CpY; CpR 3; CpH; CpR 5;
     CpH; CpR 5; CpY; CpR 3; CpY; CpY; CpY],
     [20])`;;
let cf042 = new_definition
 `cf042 = ([CpH; CpR 2; CpH; CpR 10; CpY; CpR 3; CpH; CpR 9; CpY;
            CpR 4; CpH; CpR 8;
     CpH; CpR 2; CpH; CpR 8; CpY; CpR 7; CpH; CpR 1; CpY; CpR 1; CpY; CpR 2;
     CpH; CpR 5; CpY; CpY; CpR 1; CpY; CpR 2; CpY],
     [23])`;;
let cf043 = new_definition
 `cf043 = ([CpH; CpR 8; CpH; CpR 2; CpH; CpR 10; CpY; CpR 8; CpH;
            CpR 1; CpY; CpR 6;
     CpH; CpR 1; CpH; CpR 7; CpH; CpR 1; CpY; CpR 2; CpH; CpR 7; CpY; CpY;
     CpY; CpR 3; CpY; CpR 1; CpY; CpR 2; CpY],
     [30])`;;
let cf044 = new_definition
 `cf044 = ([CpH; CpR 2; CpH; CpR 10; CpY; CpR 4; CpH; CpR 8; CpH;
            CpR 1; CpY; CpR 4;
     CpH; CpR 8; CpH; CpR 2; CpH; CpR 8; CpY; CpR 2; CpH; CpR 7; CpY; CpY;
     CpY; CpY; CpR 3; CpY; CpR 1; CpY],
     [25])`;;
let cf045 = new_definition
 `cf045 = ([CpH; CpR 6; CpH; CpR 3; CpH; CpR 9; CpH; CpR 9; CpY;
            CpR 6; CpH; CpR 1;
     CpH; CpR 7; CpH; CpR 1; CpY; CpR 2; CpH; CpR 7; CpY; CpY; CpY; CpR 4;
     CpH; CpR 4; CpY; CpR 2; CpY; CpY],
     [24])`;;
let cf046 = new_definition
 `cf046 = ([CpH; CpR 8; CpH; CpR 1; CpY; CpR 6; CpH; CpR 1; CpH;
            CpR 7; CpH; CpR 1;
     CpY; CpR 2; CpH; CpR 7; CpY; CpY; CpR 4; CpH; CpR 1; CpH; CpR 1; CpY;
     CpH; CpR 4; CpY; CpY; CpR 1; CpY],
     [18])`;;
let cf047 = new_definition
 `cf047 = ([CpH; CpR 3; CpH; CpR 10; CpH; CpR 10; CpY; CpR 8; CpH; CpR 1; CpY;
     CpR 7; CpH; CpR 1; CpY; CpR 6; CpH; CpR 1; CpY; CpR 6; CpY; CpR 4; CpY;
     CpR 2; CpY; CpR 3; CpY; CpY],
     [25])`;;
let cf048 = new_definition
 `cf048 = ([CpH; CpR 2; CpH; CpR 9; CpY; CpR 3; CpH; CpR 8; CpY;
            CpR 3; CpH; CpR 7;
     CpY; CpR 4; CpH; CpR 5; CpH; CpR 1; CpY; CpH; CpR 5; CpY; CpY; CpR 1;
     CpY; CpR 2; CpY],
     [27])`;;
let cf049 = new_definition
 `cf049 = ([CpH; CpR 2; CpH; CpR 10; CpY; CpR 3; CpH; CpR 9; CpY;
            CpR 3; CpH; CpR 8;
     CpY; CpR 4; CpH; CpR 6; CpH; CpR 1; CpY; CpR 2; CpH; CpR 1; CpY; CpR 5;
     CpY; CpR 4; CpY; CpR 3; CpY; CpY],
     [28])`;;
let cf050 = new_definition
 `cf050 = ([CpH; CpR 9; CpH; CpR 1; CpY; CpR 7; CpH; CpR 2; CpH;
            CpR 9; CpY; CpR 7;
     CpH; CpR 1; CpY; CpR 6; CpH; CpR 1; CpY; CpR 6; CpH; CpR 6; CpY; CpR 2;
     CpY; CpR 2; CpY; CpR 2; CpY; CpR 1; CpY],
     [27])`;;
let cf051 = new_definition
 `cf051 = ([CpH; CpR 9; CpH; CpR 1; CpY; CpR 8; CpH; CpR 1; CpY;
            CpR 7; CpH; CpR 1;
     CpY; CpR 6; CpH; CpR 1; CpY; CpR 6; CpH; CpR 6; CpH; CpR 6; CpY; CpR 3;
     CpY; CpY; CpR 3; CpY; CpR 1; CpY],
     [14])`;;
let cf052 = new_definition
 `cf052 = ([CpH; CpR 3; CpH; CpR 9; CpH; CpR 1; CpY; CpR 3; CpH;
            CpR 9; CpY; CpR 3;
     CpH; CpR 8; CpY; CpR 3; CpH; CpR 7; CpY; CpR 2; CpH; CpR 1; CpY; CpR 1;
     CpY; CpR 3; CpY; CpR 3; CpY; CpY],
     [24])`;;
let cf053 = new_definition
 `cf053 = ([CpH; CpR 9; CpH; CpR 1; CpY; CpR 6; CpH; CpR 3; CpH;
            CpR 9; CpH; CpR 9;
     CpY; CpR 7; CpH; CpR 1; CpY; CpR 6; CpH; CpR 1; CpY; CpR 5; CpY; CpY;
     CpR 3; CpY; CpR 1; CpY; CpR 1; CpY],
     [23])`;;
let cf054 = new_definition
 `cf054 = ([CpH; CpR 3; CpH; CpR 10; CpH; CpR 10; CpY; CpR 7; CpH; CpR 2; CpH;
     CpR 9; CpY; CpR 6; CpH; CpR 2; CpH; CpR 8; CpY; CpR 7; CpY; CpR 5; CpY;
     CpY; CpR 3; CpY; CpR 2; CpY; CpY],
     [28])`;;
let cf055 = new_definition
 `cf055 = ([CpH; CpR 9; CpH; CpR 1; CpY; CpR 8; CpH; CpR 1; CpY;
            CpR 6; CpH; CpR 2;
     CpH; CpR 8; CpY; CpR 6; CpH; CpR 1; CpY; CpR 4; CpY; CpR 2; CpH; CpR 1;
     CpY; CpR 1; CpY; CpY; CpR 2; CpY],
     [28])`;;
let cf056 = new_definition
 `cf056 = ([CpH; CpR 9; CpH; CpR 1; CpY; CpR 8; CpH; CpR 1; CpY;
            CpR 5; CpH; CpR 3;
     CpH; CpR 8; CpH; CpR 8; CpY; CpR 6; CpH; CpR 1; CpY; CpR 5; CpY; CpR 3;
     CpY; CpR 1; CpY; CpR 2; CpY; CpY],
     [28])`;;
let cf057 = new_definition
 `cf057 = ([CpH; CpR 3; CpH; CpR 10; CpH; CpR 10; CpY; CpR 8; CpH; CpR 1; CpY;
     CpR 7; CpH; CpR 1; CpY; CpR 6; CpH; CpR 7; CpY; CpR 5; CpY; CpR 4; CpH;
     CpR 5; CpY; CpR 3; CpY; CpY; CpY],
     [7])`;;
let cf058 = new_definition
 `cf058 = ([CpH; CpR 3; CpH; CpR 10; CpH; CpR 10; CpY; CpR 8; CpH; CpR 1; CpY;
     CpR 5; CpH; CpR 3; CpH; CpR 8; CpH; CpR 8; CpY; CpR 7; CpY; CpR 5; CpY;
     CpY; CpY; CpR 3; CpY; CpR 1; CpY],
     [26])`;;
let cf059 = new_definition
 `cf059 = ([CpH; CpR 9; CpH; CpR 1; CpY; CpR 7; CpH; CpR 2; CpH;
            CpR 9; CpY; CpR 7;
     CpH; CpR 1; CpY; CpR 6; CpH; CpR 1; CpY; CpR 6; CpH; CpR 6; CpY; CpY;
     CpY; CpR 2; CpY; CpR 2; CpY],
     [28])`;;
let cf060 = new_definition
 `cf060 = ([CpH; CpR 2; CpH; CpR 10; CpY; CpR 7; CpH; CpR 2; CpH;
            CpR 9; CpY; CpR 5;
     CpH; CpR 3; CpH; CpR 8; CpH; CpR 8; CpY; CpR 7; CpY; CpR 4; CpY; CpR 1;
     CpY; CpR 3; CpY; CpR 2; CpY; CpY],
     [21])`;;
let cf061 = new_definition
 `cf061 = ([CpH; CpR 2; CpH; CpR 10; CpY; CpR 8; CpH; CpR 1; CpY;
            CpR 7; CpH; CpR 1;
     CpY; CpR 5; CpH; CpR 7; CpY; CpR 2; CpH; CpR 1; CpH; CpR 1; CpY; CpR 1;
     CpY; CpY; CpR 3; CpY; CpR 1; CpY],
     [6])`;;
let cf062 = new_definition
 `cf062 = ([CpH; CpR 2; CpH; CpR 11; CpY; CpR 3; CpH; CpR 2; CpH; CpR 10; CpY;
     CpR 3; CpH; CpR 9; CpY; CpY; CpR 4; CpH; CpR 7; CpH; CpR 7; CpH; CpR 7;
     CpY; CpY; CpY; CpR 4; CpY; CpY; CpY],
     [8; 9; 15; 16])`;;
let cf063 = new_definition
 `cf063 = ([CpH; CpR 10; CpH; CpR 1; CpY; CpR 9; CpH; CpR 8; CpH; CpR 2; CpH;
     CpR 10; CpY; CpR 8; CpH; CpR 1; CpY; CpR 7; CpH; CpR 8; CpY; CpR 2; CpH;
     CpR 7; CpY; CpY; CpY; CpR 3; CpY; CpR 1; CpY; CpR 2; CpY],
     [31])`;;
let cf064 = new_definition
 `cf064 = ([CpH; CpR 2; CpH; CpR 11; CpY; CpR 3; CpH; CpR 10; CpY; CpR 3; CpH;
     CpR 2; CpH; CpR 9; CpY; CpR 3; CpH; CpR 8; CpY; CpR 6; CpH; CpR 7; CpY;
     CpY; CpY; CpR 4; CpH; CpR 1; CpY; CpR 3; CpY; CpR 1; CpY],
     [4; 5; 22; 27])`;;
let cf065 = new_definition
 `cf065 = ([CpH; CpR 2; CpH; CpR 11; CpY; CpR 4; CpH; CpR 2; CpH; CpR 10; CpY;
     CpR 4; CpH; CpR 8; CpH; CpR 1; CpY; CpR 8; CpY; CpR 6; CpH; CpR 1; CpH;
     CpR 1; CpY; CpR 1; CpY; CpR 1; CpY; CpR 1; CpY; CpR 2; CpY; CpR 1; CpY],
     [31])`;;
let cf066 = new_definition
 `cf066 = ([CpH; CpR 2; CpH; CpR 11; CpY; CpR 3; CpH; CpR 10; CpY; CpR 4; CpH;
     CpR 3; CpH; CpR 8; CpH; CpR 1; CpY; CpR 7; CpH; CpR 1; CpY; CpR 7; CpH;
     CpR 1; CpY; CpR 1; CpY; CpR 1; CpY; CpR 1; CpY; CpR 2; CpY; CpR 1; CpY],
     [1; 2; 8; 9])`;;
let cf067 = new_definition
 `cf067 = ([CpH; CpR 10; CpH; CpR 1; CpY; CpR 8; CpH; CpR 2; CpH; CpR 10; CpY;
     CpR 6; CpH; CpR 1; CpH; CpR 8; CpH; CpR 1; CpY; CpR 3; CpH; CpR 8; CpH;
     CpR 8; CpY; CpY; CpY; CpR 3; CpY; CpR 1; CpY; CpR 3; CpY; CpY],
     [34])`;;
let cf068 = new_definition
 `cf068 = ([CpH; CpR 9; CpH; CpR 2; CpH; CpR 11; CpY; CpR 9; CpH;
            CpR 1; CpY; CpR 6;
     CpH; CpR 1; CpH; CpR 8; CpH; CpR 1; CpY; CpR 8; CpH; CpR 1; CpY; CpR 1;
     CpY; CpR 2; CpH; CpR 6; CpY; CpR 5; CpY; CpR 3; CpY; CpR 1; CpY; CpR 1;
     CpY],
     [32])`;;
let cf069 = new_definition
 `cf069 = ([CpH; CpR 10; CpH; CpR 1; CpY; CpR 9; CpH; CpR 9; CpH;
            CpR 1; CpY; CpR 7;
     CpH; CpR 1; CpH; CpR 8; CpH; CpR 1; CpY; CpR 2; CpH; CpR 8; CpY; CpY;
     CpY; CpR 4; CpH; CpR 1; CpY; CpR 4; CpY; CpR 2; CpY; CpY],
     [25])`;;
let cf070 = new_definition
 `cf070 = ([CpH; CpR 2; CpH; CpR 10; CpY; CpR 3; CpH; CpR 2; CpH;
            CpR 9; CpY; CpR 5;
     CpH; CpR 8; CpH; CpR 7; CpH; CpR 1; CpH; CpR 1; CpH; CpR 1; CpY; CpR 1;
     CpY; CpY; CpR 1; CpY; CpR 1; CpY; CpR 2; CpY; CpR 1; CpY],
     [33])`;;
let cf071 = new_definition
 `cf071 = ([CpH; CpR 9; CpH; CpR 1; CpY; CpR 7; CpH; CpR 8; CpH;
            CpR 1; CpY; CpR 6;
     CpH; CpR 1; CpH; CpR 1; CpH; CpR 8; CpH; CpR 8; CpY; CpY; CpR 1; CpY;
     CpY; CpR 4; CpH; CpR 1; CpY; CpR 3; CpY; CpR 1; CpY],
     [21])`;;
let cf072 = new_definition
 `cf072 = ([CpH; CpR 9; CpH; CpR 1; CpY; CpR 8; CpH; CpR 6; CpH;
            CpR 3; CpH; CpR 9;
     CpH; CpR 9; CpY; CpR 7; CpH; CpR 8; CpY; CpR 2; CpH; CpR 7; CpY; CpY;
     CpY; CpR 4; CpH; CpR 4; CpY; CpR 2; CpY; CpY],
     [25])`;;
let cf073 = new_definition
 `cf073 = ([CpH; CpR 2; CpH; CpR 11; CpY; CpR 3; CpH; CpR 10; CpY; CpR 3; CpH;
     CpR 9; CpY; CpR 3; CpH; CpR 8; CpY; CpR 3; CpH; CpR 7; CpY; CpR 2; CpH;
     CpR 1; CpY; CpR 4; CpY; CpR 3; CpY; CpR 1; CpY; CpY],
     [25])`;;
let cf074 = new_definition
 `cf074 = ([CpH; CpR 10; CpH; CpR 1; CpY; CpR 9; CpH; CpR 1; CpY;
            CpR 7; CpH; CpR 2;
     CpH; CpR 9; CpY; CpR 7; CpH; CpR 1; CpY; CpR 6; CpH; CpR 1; CpY; CpR 5;
     CpY; CpR 3; CpY; CpR 3; CpY; CpR 3; CpY; CpR 1; CpY],
     [15])`;;
let cf075 = new_definition
 `cf075 = ([CpH; CpR 3; CpH; CpR 11; CpH; CpR 11; CpY; CpR 9; CpH; CpR 1; CpY;
     CpR 8; CpH; CpR 1; CpY; CpR 6; CpH; CpR 2; CpH; CpR 8; CpY; CpR 7; CpY;
     CpR 5; CpY; CpR 3; CpY; CpR 3; CpY; CpY; CpY],
     [15; 29])`;;
let cf076 = new_definition
 `cf076 = ([CpH; CpR 10; CpH; CpR 1; CpY; CpR 9; CpH; CpR 1; CpY;
            CpR 8; CpH; CpR 1;
     CpY; CpR 7; CpH; CpR 1; CpY; CpR 6; CpH; CpR 1; CpY; CpR 6; CpH; CpR 6;
     CpY; CpR 2; CpY; CpR 4; CpY; CpY; CpY],
     [27])`;;
let cf077 = new_definition
 `cf077 = ([CpH; CpR 2; CpH; CpR 9; CpY; CpR 3; CpH; CpR 8; CpY;
            CpR 3; CpH; CpR 7;
     CpY; CpR 3; CpH; CpR 6; CpY; CpR 2; CpH; CpR 1; CpH; CpR 1; CpY; CpH;
     CpR 4; CpY; CpY; CpR 1; CpY],
     [14])`;;
let cf078 = new_definition
 `cf078 = ([CpH; CpR 2; CpH; CpR 10; CpY; CpR 3; CpH; CpR 9; CpY;
            CpR 3; CpH; CpR 8;
     CpY; CpR 3; CpH; CpR 7; CpY; CpR 2; CpH; CpR 1; CpH; CpR 1; CpY; CpR 1;
     CpY; CpR 4; CpH; CpR 1; CpY; CpR 3; CpY; CpR 1; CpY],
     [14])`;;
let cf079 = new_definition
 `cf079 = ([CpH; CpR 2; CpH; CpR 11; CpY; CpR 3; CpH; CpR 10; CpY; CpR 3; CpH;
     CpR 9; CpY; CpR 3; CpH; CpR 8; CpY; CpR 3; CpH; CpR 7; CpY; CpR 3; CpH;
     CpR 5; CpH; CpR 1; CpY; CpR 2; CpY; CpR 1; CpY; CpY; CpY],
     [18])`;;
let cf080 = new_definition
 `cf080 = ([CpH; CpR 3; CpH; CpR 10; CpH; CpR 1; CpY; CpR 3; CpH; CpR 10; CpY;
     CpR 3; CpH; CpR 9; CpY; CpR 3; CpH; CpR 8; CpY; CpR 2; CpH; CpR 1; CpH;
     CpR 1; CpY; CpR 1; CpY; CpR 4; CpY; CpR 3; CpY; CpY; CpY],
     [27])`;;
let cf081 = new_definition
 `cf081 = ([CpH; CpR 10; CpH; CpR 1; CpY; CpR 9; CpH; CpR 1; CpY;
            CpR 6; CpH; CpR 3;
     CpH; CpR 9; CpH; CpR 9; CpY; CpR 7; CpH; CpR 1; CpY; CpR 7; CpH; CpR 7;
     CpY; CpR 3; CpY; CpR 1; CpY; CpR 3; CpY; CpY; CpR 1; CpY],
     [30])`;;
let cf082 = new_definition
 `cf082 = ([CpH; CpR 9; CpH; CpR 1; CpY; CpR 8; CpH; CpR 1; CpY;
            CpR 7; CpH; CpR 1;
     CpY; CpR 6; CpH; CpR 1; CpY; CpR 5; CpH; CpR 1; CpH; CpR 1; CpY; CpH;
     CpR 5; CpY; CpY; CpY; CpR 1; CpY],
     [14])`;;
let cf083 = new_definition
 `cf083 = ([CpH; CpR 11; CpH; CpR 1; CpY; CpR 10; CpH; CpR 1; CpY; CpR 9; CpH;
     CpR 9; CpH; CpR 1; CpY; CpR 8; CpH; CpR 1; CpY; CpR 8; CpH; CpR 8; CpH;
     CpR 8; CpY; CpY; CpY; CpY; CpR 3; CpY; CpR 1; CpY; CpR 1; CpY],
     [4; 5; 25; 30])`;;
let cf084 = new_definition
 `cf084 = ([CpH; CpR 10; CpH; CpR 1; CpY; CpR 9; CpH; CpR 1; CpY;
            CpR 7; CpH; CpR 8;
     CpH; CpR 1; CpY; CpR 7; CpH; CpR 1; CpY; CpR 3; CpH; CpR 1; CpH; CpR 1;
     CpY; CpR 1; CpY; CpY; CpR 3; CpY; CpR 1; CpY; CpR 1; CpY],
     [20])`;;
let cf085 = new_definition
 `cf085 = ([CpH; CpR 10; CpH; CpR 1; CpY; CpR 9; CpH; CpR 1; CpY;
            CpR 6; CpH; CpR 3;
     CpH; CpR 9; CpH; CpR 9; CpY; CpR 7; CpH; CpR 1; CpY; CpR 7; CpH; CpR 1;
     CpY; CpR 1; CpY; CpY; CpR 3; CpY; CpR 1; CpY; CpY],
     [30])`;;
let cf086 = new_definition
 `cf086 = ([CpH; CpR 10; CpH; CpR 1; CpY; CpR 9; CpH; CpR 1; CpY;
            CpR 5; CpH; CpR 4;
     CpH; CpR 9; CpH; CpR 9; CpH; CpR 9; CpY; CpR 7; CpH; CpR 1; CpY; CpR 5;
     CpY; CpR 4; CpY; CpR 1; CpY; CpR 3; CpY; CpY; CpY],
     [26])`;;
let cf087 = new_definition
 `cf087 = ([CpH; CpR 11; CpH; CpR 1; CpY; CpR 10; CpH; CpR 1; CpY; CpR 8; CpH;
     CpR 9; CpH; CpR 1; CpY; CpR 3; CpH; CpR 1; CpY; CpR 1; CpY; CpR 7; CpH;
     CpR 1; CpY; CpR 1; CpY; CpR 3; CpH; CpR 5; CpH; CpR 5; CpY; CpR 3; CpY;
     CpY; CpY],
     [25])`;;
let cf088 = new_definition
 `cf088 = ([CpH; CpR 11; CpH; CpR 1; CpY; CpR 10; CpH; CpR 10; CpH; CpR 1; CpY;
     CpR 8; CpH; CpR 2; CpH; CpR 10; CpY; CpR 7; CpH; CpR 9; CpY; CpR 3; CpH;
     CpR 8; CpH; CpR 8; CpY; CpY; CpY; CpR 3; CpY; CpR 1; CpY; CpR 3; CpY;
     CpY],
     [35])`;;
let cf089 = new_definition
 `cf089 = ([CpH; CpR 10; CpH; CpR 1; CpY; CpR 9; CpH; CpR 9; CpH;
            CpR 1; CpY; CpR 8;
     CpH; CpR 1; CpY; CpR 6; CpH; CpR 1; CpH; CpR 1; CpH; CpR 8; CpH; CpR 8;
     CpY; CpY; CpR 1; CpY; CpY; CpY; CpR 3; CpY; CpR 1; CpY],
     [8; 9; 15; 16])`;;
let cf090 = new_definition
 `cf090 = ([CpH; CpR 8; CpH; CpR 3; CpH; CpR 11; CpH; CpR 11; CpY; CpR 9; CpH;
     CpR 9; CpH; CpR 1; CpY; CpR 8; CpH; CpR 1; CpY; CpR 6; CpH; CpR 8; CpY;
     CpR 3; CpH; CpR 7; CpY; CpY; CpY; CpY; CpR 3; CpY; CpR 1; CpY],
     [14; 15; 21; 22])`;;
let cf091 = new_definition
 `cf091 = ([CpH; CpR 11; CpH; CpR 1; CpY; CpR 9; CpH; CpR 2; CpH; CpR 11; CpY;
     CpR 9; CpH; CpR 1; CpY; CpR 7; CpH; CpR 1; CpH; CpR 8; CpH; CpR 1; CpY;
     CpR 8; CpH; CpR 1; CpY; CpR 1; CpY; CpR 2; CpH; CpR 6; CpY; CpY; CpY;
     CpY; CpY],
     [34])`;;
let cf092 = new_definition
 `cf092 = ([CpH; CpR 8; CpH; CpR 3; CpH; CpR 11; CpH; CpR 11; CpY; CpR 9; CpH;
     CpR 1; CpY; CpR 7; CpH; CpR 1; CpH; CpR 8; CpH; CpR 1; CpY; CpR 2; CpH;
     CpR 8; CpY; CpY; CpY; CpR 5; CpH; CpR 5; CpY; CpR 2; CpY; CpR 3; CpY;
     CpR 1; CpY],
     [28])`;;
let cf093 = new_definition
 `cf093 = ([CpH; CpR 10; CpH; CpR 1; CpY; CpR 9; CpH; CpR 1; CpY;
            CpR 7; CpH; CpR 1;
     CpH; CpR 8; CpH; CpR 1; CpY; CpR 2; CpH; CpR 8; CpY; CpY; CpR 5; CpH;
     CpR 1; CpH; CpR 1; CpY; CpH; CpR 5; CpY; CpY; CpY; CpR 1; CpY],
     [22])`;;
let cf094 = new_definition
 `cf094 = ([CpH; CpR 10; CpH; CpR 1; CpY; CpR 9; CpH; CpR 9; CpH;
            CpR 1; CpY; CpR 8;
     CpH; CpR 1; CpY; CpR 6; CpH; CpR 1; CpH; CpR 1; CpH; CpR 8; CpH; CpR 8;
     CpY; CpY; CpR 1; CpY; CpY; CpR 4; CpH; CpR 1; CpY; CpR 3; CpY; CpR 1;
     CpY],
     [25])`;;
let cf095 = new_definition
 `cf095 = ([CpH; CpR 2; CpH; CpR 12; CpY; CpR 3; CpH; CpR 11; CpY; CpR 3; CpH;
     CpR 10; CpY; CpR 3; CpH; CpR 9; CpY; CpR 3; CpH; CpR 8; CpY; CpR 2; CpH;
     CpR 1; CpH; CpR 1; CpY; CpR 5; CpY; CpR 3; CpY; CpR 1; CpY; CpY; CpY],
     [28])`;;
let cf096 = new_definition
 `cf096 = ([CpH; CpR 11; CpH; CpR 1; CpY; CpR 10; CpH; CpR 1; CpY; CpR 8; CpH;
     CpR 2; CpH; CpR 10; CpY; CpR 8; CpH; CpR 1; CpY; CpR 7; CpH; CpR 1; CpY;
     CpR 7; CpH; CpR 7; CpY; CpR 3; CpY; CpR 4; CpY; CpY; CpR 1; CpY; CpY],
     [27])`;;
let cf097 = new_definition
 `cf097 = ([CpH; CpR 2; CpH; CpR 11; CpY; CpR 3; CpH; CpR 10; CpY; CpR 3; CpH;
     CpR 9; CpY; CpR 3; CpH; CpR 8; CpY; CpR 4; CpH; CpR 7; CpH; CpR 7; CpY;
     CpY; CpR 2; CpH; CpR 1; CpY; CpR 1; CpY; CpR 1; CpY; CpY],
     [26])`;;
let cf098 = new_definition
 `cf098 = ([CpH; CpR 3; CpH; CpR 11; CpH; CpR 11; CpY; CpR 9; CpH; CpR 1; CpY;
     CpR 8; CpH; CpR 1; CpY; CpR 6; CpH; CpR 2; CpH; CpR 8; CpY; CpR 7; CpY;
     CpR 1; CpY; CpR 5; CpH; CpR 5; CpY; CpY; CpY; CpR 1; CpY],
     [26])`;;
let cf099 = new_definition
 `cf099 = ([CpH; CpR 10; CpH; CpR 1; CpY; CpR 9; CpH; CpR 1; CpY;
            CpR 8; CpH; CpR 1;
     CpY; CpR 7; CpH; CpR 1; CpY; CpR 6; CpH; CpR 1; CpY; CpR 6; CpH; CpR 1;
     CpY; CpH; CpR 5; CpY; CpY; CpY; CpR 1; CpY],
     [18])`;;
let cf100 = new_definition
 `cf100 = ([CpH; CpR 2; CpH; CpR 11; CpY; CpR 3; CpH; CpR 10; CpY; CpR 3; CpH;
     CpR 9; CpY; CpR 3; CpH; CpR 8; CpY; CpR 2; CpH; CpR 1; CpH; CpR 1; CpY;
     CpH; CpR 6; CpY; CpY; CpY; CpY; CpY],
     [27])`;;
let cf101 = new_definition
 `cf101 = ([CpH; CpR 3; CpH; CpR 12; CpH; CpR 12; CpY; CpR 10; CpH; CpR 1; CpY;
     CpR 9; CpH; CpR 1; CpY; CpR 8; CpH; CpR 8; CpH; CpR 1; CpY; CpR 8; CpY;
     CpR 6; CpY; CpR 5; CpH; CpR 6; CpY; CpR 3; CpY; CpY; CpR 3; CpY; CpR 1;
     CpY],
     [31])`;;
let cf102 = new_definition
 `cf102 = ([CpH; CpR 11; CpH; CpR 1; CpY; CpR 10; CpH; CpR 1; CpY; CpR 8; CpH;
     CpR 2; CpH; CpR 10; CpY; CpR 8; CpH; CpR 1; CpY; CpR 6; CpH; CpR 1; CpH;
     CpR 1; CpY; CpR 6; CpY; CpR 3; CpY; CpR 4; CpY; CpY; CpR 3; CpY; CpR 1;
     CpY],
     [31])`;;
let cf103 = new_definition
 `cf103 = ([CpH; CpR 11; CpH; CpR 1; CpY; CpR 10; CpH; CpR 1; CpY; CpR 9; CpH;
     CpR 1; CpY; CpR 7; CpH; CpR 2; CpH; CpR 9; CpY; CpR 7; CpH; CpR 1; CpY;
     CpR 7; CpH; CpR 7; CpY; CpR 3; CpY; CpR 4; CpY; CpY; CpY; CpY],
     [33])`;;
let cf104 = new_definition
 `cf104 = ([CpH; CpR 3; CpH; CpR 12; CpH; CpR 12; CpY; CpR 10; CpH; CpR 1; CpY;
     CpR 8; CpH; CpR 2; CpH; CpR 10; CpY; CpR 7; CpH; CpR 2; CpH; CpR 9; CpY;
     CpR 8; CpY; CpR 5; CpY; CpR 4; CpY; CpR 4; CpY; CpY; CpY; CpY],
     [31; 33])`;;
let cf105 = new_definition
 `cf105 = ([CpH; CpR 9; CpH; CpR 1; CpY; CpR 8; CpH; CpR 1; CpY;
            CpR 7; CpH; CpR 1;
     CpY; CpR 6; CpH; CpR 1; CpY; CpR 5; CpH; CpR 1; CpH; CpR 6; CpH; CpR 1;
     CpH; CpR 1; CpY; CpR 1; CpY; CpR 1; CpY; CpY; CpY],
     [6])`;;
let cf106 = new_definition
 `cf106 = ([CpH; CpR 2; CpH; CpR 12; CpY; CpR 3; CpH; CpR 11; CpY; CpR 4; CpH;
     CpR 2; CpH; CpR 10; CpY; CpR 3; CpH; CpR 9; CpY; CpR 6; CpH; CpR 1; CpH;
     CpR 1; CpY; CpR 1; CpY; CpY; CpR 2; CpH; CpR 1; CpY; CpR 1; CpY; CpR 1;
     CpY; CpR 1; CpY],
     [33])`;;
let cf107 = new_definition
 `cf107 = ([CpH; CpR 11; CpH; CpR 1; CpY; CpR 10; CpH; CpR 10; CpH; CpR 1; CpY;
     CpR 7; CpH; CpR 3; CpH; CpR 10; CpH; CpR 10; CpY; CpR 8; CpH; CpR 9;
     CpY; CpR 2; CpH; CpR 8; CpY; CpY; CpY; CpR 3; CpH; CpR 1; CpY; CpR 1;
     CpY; CpR 1; CpY; CpY],
     [29])`;;
let cf108 = new_definition
 `cf108 = ([CpH; CpR 11; CpH; CpR 1; CpY; CpR 8; CpH; CpR 10; CpH; CpR 1; CpY;
     CpR 9; CpH; CpR 1; CpY; CpR 8; CpH; CpR 9; CpY; CpR 2; CpH; CpR 8; CpY;
     CpY; CpR 5; CpH; CpR 1; CpH; CpR 1; CpY; CpH; CpR 5; CpY; CpY; CpY;
     CpR 1; CpY],
     [23])`;;
let cf109 = new_definition
 `cf109 = ([CpH; CpR 10; CpH; CpR 1; CpY; CpR 9; CpH; CpR 1; CpY;
            CpR 8; CpH; CpR 1;
     CpY; CpR 7; CpH; CpR 1; CpY; CpR 5; CpH; CpR 2; CpH; CpR 7; CpY; CpH;
     CpR 1; CpH; CpR 1; CpY; CpR 1; CpY; CpR 1; CpY; CpY; CpY],
     [6])`;;
let cf110 = new_definition
 `cf110 = ([CpH; CpR 12; CpH; CpR 1; CpY; CpR 11; CpH; CpR 1; CpY; CpR 9; CpH;
     CpR 2; CpH; CpR 11; CpY; CpR 9; CpH; CpR 1; CpY; CpR 8; CpH; CpR 1; CpY;
     CpR 7; CpH; CpR 8; CpY; CpR 2; CpH; CpR 1; CpY; CpR 5; CpY; CpY; CpR 3;
     CpY; CpR 1; CpY; CpR 1; CpY],
     [32])`;;
let cf111 = new_definition
 `cf111 = ([CpH; CpR 8; CpH; CpR 1; CpY; CpR 6; CpH; CpR 2; CpH;
            CpR 8; CpY; CpR 6;
     CpH; CpR 1; CpY; CpR 5; CpH; CpR 1; CpY; CpR 4; CpY; CpY; CpR 3; CpY;
     CpY],
     [23])`;;
let cf112 = new_definition
 `cf112 = ([CpH; CpR 2; CpH; CpR 9; CpY; CpR 7; CpH; CpR 1; CpY;
            CpR 6; CpH; CpR 6;
     CpH; CpR 1; CpY; CpR 6; CpY; CpR 3; CpH; CpR 1; CpY; CpR 4; CpY; CpR 1;
     CpY; CpR 2; CpY],
     [23])`;;
let cf113 = new_definition
 `cf113 = ([CpH; CpR 8; CpH; CpR 1; CpY; CpR 3; CpH; CpR 8; CpY;
            CpR 5; CpH; CpR 1;
     CpY; CpR 4; CpH; CpR 6; CpY; CpR 3; CpH; CpR 5; CpH; CpR 5; CpY; CpR 3;
     CpY; CpY; CpY],
     [6])`;;
let cf114 = new_definition
 `cf114 = ([CpH; CpR 2; CpH; CpR 10; CpY; CpR 3; CpH; CpR 9; CpY;
            CpR 4; CpH; CpR 8;
     CpH; CpR 2; CpH; CpR 8; CpY; CpR 3; CpH; CpR 7; CpH; CpR 7; CpY; CpY;
     CpY; CpY; CpR 3; CpY; CpY],
     [25])`;;
let cf115 = new_definition
 `cf115 = ([CpH; CpR 2; CpH; CpR 10; CpY; CpR 4; CpH; CpR 9; CpH;
            CpR 2; CpH; CpR 9;
     CpY; CpR 3; CpH; CpR 8; CpH; CpR 8; CpY; CpY; CpY; CpR 4; CpH; CpR 5;
     CpH; CpR 5; CpY; CpR 3; CpY; CpY; CpY],
     [25])`;;
let cf116 = new_definition
 `cf116 = ([CpH; CpR 9; CpH; CpR 1; CpY; CpR 3; CpH; CpR 9; CpY;
            CpR 4; CpH; CpR 7;
     CpH; CpR 1; CpY; CpR 3; CpH; CpR 7; CpY; CpR 2; CpY; CpR 3; CpY; CpR 4;
     CpY; CpR 3; CpY; CpY],
     [1; 2; 19; 24])`;;
let cf117 = new_definition
 `cf117 = ([CpH; CpR 8; CpH; CpR 1; CpY; CpR 7; CpH; CpR 1; CpY;
            CpR 6; CpH; CpR 1;
     CpY; CpR 6; CpH; CpR 6; CpH; CpR 6; CpY; CpR 1; CpH; CpR 1; CpY; CpR 1;
     CpY; CpY; CpR 2; CpY],
     [14])`;;
let cf118 = new_definition
 `cf118 = ([CpH; CpR 9; CpH; CpR 1; CpY; CpR 7; CpH; CpR 2; CpH;
            CpR 9; CpY; CpR 7;
     CpH; CpR 1; CpY; CpR 6; CpH; CpR 1; CpY; CpR 4; CpY; CpY; CpR 2; CpH;
     CpR 1; CpY; CpR 1; CpY; CpY],
     [23])`;;
let cf119 = new_definition
 `cf119 = ([CpH; CpR 9; CpH; CpR 1; CpY; CpR 3; CpH; CpR 9; CpY;
            CpR 4; CpH; CpR 2;
     CpH; CpR 8; CpY; CpR 2; CpY; CpR 4; CpH; CpR 6; CpY; CpR 2; CpH; CpR 5;
     CpY; CpR 3; CpY; CpY; CpY],
     [6])`;;
let cf120 = new_definition
 `cf120 = ([CpH; CpR 9; CpH; CpR 1; CpY; CpR 3; CpH; CpR 9; CpY;
            CpR 6; CpH; CpR 5;
     CpH; CpR 1; CpH; CpR 1; CpH; CpR 1; CpY; CpR 2; CpY; CpR 3; CpY; CpR 1;
     CpY; CpR 3; CpY; CpY; CpY],
     [6])`;;
let cf121 = new_definition
 `cf121 = ([CpH; CpR 3; CpH; CpR 9; CpH; CpR 1; CpY; CpR 3; CpH;
            CpR 9; CpY; CpR 3;
     CpH; CpR 8; CpY; CpR 4; CpH; CpR 7; CpH; CpR 7; CpY; CpR 3; CpY; CpR 1;
     CpY; CpR 3; CpY; CpR 1; CpY; CpR 2; CpY],
     [28])`;;
let cf122 = new_definition
 `cf122 = ([CpH; CpR 3; CpH; CpR 10; CpH; CpR 10; CpY; CpR 6; CpH; CpR 3; CpH;
     CpR 9; CpH; CpR 9; CpY; CpR 7; CpH; CpR 1; CpY; CpR 7; CpY; CpR 5; CpY;
     CpY; CpY; CpR 3; CpY; CpY],
     [27])`;;
let cf123 = new_definition
 `cf123 = ([CpH; CpR 2; CpH; CpR 10; CpY; CpR 3; CpH; CpR 9; CpY;
            CpR 3; CpH; CpR 8;
     CpY; CpR 3; CpH; CpR 1; CpH; CpR 1; CpY; CpR 5; CpH; CpR 1; CpY; CpR 5;
     CpY; CpR 1; CpY; CpR 2; CpY; CpR 1; CpY],
     [27])`;;
let cf124 = new_definition
 `cf124 = ([CpH; CpR 2; CpH; CpR 10; CpY; CpR 3; CpH; CpR 9; CpY;
            CpR 3; CpH; CpR 8;
     CpY; CpR 4; CpH; CpR 6; CpH; CpR 1; CpY; CpR 4; CpY; CpR 5; CpH; CpR 5;
     CpY; CpY; CpR 1; CpY; CpR 2; CpY],
     [12; 13; 28])`;;
let cf125 = new_definition
 `cf125 = ([CpH; CpR 3; CpH; CpR 10; CpH; CpR 10; CpY; CpR 8; CpH; CpR 1; CpY;
     CpR 7; CpH; CpR 7; CpH; CpR 1; CpY; CpR 7; CpY; CpR 5; CpY; CpR 5; CpH;
     CpR 5; CpY; CpR 2; CpY; CpY; CpR 2; CpY],
     [26])`;;
let cf126 = new_definition
 `cf126 = ([CpH; CpR 9; CpH; CpR 1; CpY; CpR 7; CpH; CpR 2; CpH;
            CpR 9; CpY; CpR 7;
     CpH; CpR 1; CpY; CpR 5; CpH; CpR 1; CpH; CpR 1; CpY; CpR 5; CpY; CpY;
     CpY; CpR 3; CpY; CpY],
     [13])`;;
let cf127 = new_definition
 `cf127 = ([CpH; CpR 3; CpH; CpR 10; CpH; CpR 1; CpY; CpR 3; CpH;
            CpR 3; CpH; CpR 9;
     CpH; CpR 1; CpY; CpR 3; CpH; CpR 9; CpY; CpR 2; CpH; CpR 1; CpY; CpR 1;
     CpY; CpR 1; CpY; CpR 1; CpY; CpR 3; CpY; CpY; CpY],
     [31])`;;
let cf128 = new_definition
 `cf128 = ([CpH; CpR 2; CpH; CpR 11; CpY; CpR 3; CpH; CpR 10; CpY; CpR 5; CpH;
     CpR 2; CpH; CpR 9; CpY; CpR 2; CpH; CpR 1; CpY; CpR 1; CpY; CpR 1; CpY;
     CpR 3; CpH; CpR 5; CpH; CpR 5; CpY; CpR 3; CpY; CpY; CpY],
     [4; 5; 18; 23])`;;
let cf129 = new_definition
 `cf129 = ([CpH; CpR 2; CpH; CpR 11; CpY; CpR 5; CpH; CpR 2; CpH; CpR 10; CpY;
     CpR 3; CpH; CpR 9; CpY; CpR 5; CpH; CpR 8; CpY; CpR 3; CpH; CpR 7; CpH;
     CpR 7; CpY; CpY; CpY; CpY; CpR 3; CpY; CpY],
     [26])`;;
let cf130 = new_definition
 `cf130 = ([CpH; CpR 9; CpH; CpR 1; CpY; CpR 3; CpH; CpR 9; CpY;
            CpR 3; CpH; CpR 8;
     CpY; CpR 4; CpH; CpR 1; CpY; CpR 6; CpH; CpR 1; CpY; CpR 4; CpH; CpR 5;
     CpY; CpR 1; CpH; CpR 1; CpY; CpR 1; CpY; CpY],
     [6])`;;
let cf131 = new_definition
 `cf131 = ([CpH; CpR 2; CpH; CpR 11; CpY; CpR 3; CpH; CpR 10; CpY; CpR 4; CpH;
     CpR 9; CpH; CpR 2; CpH; CpR 9; CpY; CpR 3; CpH; CpR 8; CpH; CpR 8; CpY;
     CpY; CpY; CpR 3; CpH; CpR 5; CpY; CpR 3; CpY; CpY; CpY],
     [29])`;;
let cf132 = new_definition
 `cf132 = ([CpH; CpR 4; CpH; CpR 9; CpH; CpR 1; CpH; CpR 1; CpY; CpR 3;
            CpH; CpR 10;
     CpY; CpR 4; CpH; CpR 9; CpH; CpR 2; CpH; CpR 9; CpY; CpR 2; CpH; CpR 8;
     CpY; CpY; CpY; CpR 2; CpY; CpR 3; CpY; CpY; CpY],
     [32])`;;
let cf133 = new_definition
 `cf133 = ([CpH; CpR 9; CpH; CpR 2; CpH; CpR 11; CpY; CpR 9; CpH;
            CpR 1; CpY; CpR 7;
     CpH; CpR 1; CpH; CpR 8; CpH; CpR 1; CpY; CpR 2; CpH; CpR 8; CpY; CpY;
     CpR 6; CpH; CpR 1; CpY; CpR 5; CpY; CpR 1; CpY; CpR 3; CpY; CpY],
     [34])`;;
let cf134 = new_definition
 `cf134 = ([CpH; CpR 2; CpH; CpR 10; CpY; CpR 4; CpH; CpR 9; CpH;
            CpR 2; CpH; CpR 9;
     CpY; CpR 8; CpH; CpR 1; CpY; CpR 1; CpY; CpR 2; CpH; CpR 6; CpY; CpR 2;
     CpH; CpR 1; CpH; CpR 1; CpY; CpR 4; CpH; CpR 1; CpY; CpR 3; CpY; CpR 1;
     CpY],
     [19])`;;
let cf135 = new_definition
 `cf135 = ([CpH; CpR 8; CpH; CpR 1; CpH; CpR 1; CpY; CpR 3; CpH;
            CpR 9; CpY; CpR 3;
     CpH; CpR 8; CpY; CpR 3; CpH; CpR 7; CpY; CpR 2; CpY; CpR 2; CpH; CpR 1;
     CpY; CpR 4; CpY; CpR 1; CpY; CpR 2; CpY],
     [13])`;;
let cf136 = new_definition
 `cf136 = ([CpH; CpR 9; CpH; CpR 1; CpY; CpR 8; CpH; CpR 1; CpY;
            CpR 7; CpH; CpR 1;
     CpY; CpR 6; CpH; CpR 1; CpY; CpR 6; CpH; CpR 6; CpY; CpR 1; CpH; CpR 1;
     CpY; CpR 1; CpY; CpY; CpR 2; CpY],
     [14])`;;
let cf137 = new_definition
 `cf137 = ([CpH; CpR 10; CpH; CpR 1; CpY; CpR 9; CpH; CpR 1; CpY;
            CpR 8; CpH; CpR 1;
     CpY; CpR 7; CpH; CpR 1; CpY; CpR 6; CpH; CpR 1; CpY; CpR 6; CpH; CpR 6;
     CpY; CpR 2; CpY; CpR 2; CpY; CpR 2; CpY; CpR 1; CpY],
     [29])`;;
let cf138 = new_definition
 `cf138 = ([CpH; CpR 10; CpH; CpR 1; CpY; CpR 3; CpH; CpR 10; CpY; CpR 5; CpH;
     CpR 7; CpH; CpR 1; CpH; CpR 1; CpY; CpR 3; CpH; CpR 8; CpY; CpR 2; CpY;
     CpR 3; CpY; CpR 1; CpY; CpR 3; CpY; CpY; CpY],
     [18; 19; 29])`;;
let cf139 = new_definition
 `cf139 = ([CpH; CpR 3; CpH; CpR 11; CpH; CpR 11; CpY; CpR 8; CpH; CpR 2; CpH;
     CpR 10; CpY; CpR 8; CpH; CpR 1; CpY; CpR 7; CpH; CpR 1; CpY; CpR 7; CpY;
     CpR 5; CpY; CpY; CpR 3; CpY; CpR 2; CpY; CpR 2; CpY],
     [7])`;;
let cf140 = new_definition
 `cf140 = ([CpH; CpR 2; CpH; CpR 11; CpY; CpR 3; CpH; CpR 10; CpY; CpR 3; CpH;
     CpR 9; CpY; CpR 3; CpH; CpR 8; CpY; CpR 3; CpH; CpR 7; CpY; CpR 4; CpY;
     CpR 5; CpH; CpR 5; CpY; CpY; CpR 1; CpY; CpR 2; CpY],
     [12; 13; 29])`;;
let cf141 = new_definition
 `cf141 = ([CpH; CpR 10; CpH; CpR 1; CpY; CpR 3; CpH; CpR 10; CpY; CpR 3; CpH;
     CpR 9; CpY; CpR 3; CpH; CpR 2; CpH; CpR 8; CpY; CpR 2; CpY; CpR 3; CpY;
     CpR 4; CpY; CpR 4; CpH; CpR 4; CpY; CpR 2; CpY; CpY],
     [29])`;;
let cf142 = new_definition
 `cf142 = ([CpH; CpR 3; CpH; CpR 11; CpH; CpR 11; CpY; CpR 9; CpH; CpR 1; CpY;
     CpR 8; CpH; CpR 1; CpY; CpR 7; CpH; CpR 1; CpY; CpR 7; CpH; CpR 7; CpY;
     CpR 5; CpY; CpR 2; CpY; CpR 2; CpY; CpR 2; CpY; CpR 2; CpY],
     [29])`;;
let cf143 = new_definition
 `cf143 = ([CpH; CpR 9; CpH; CpR 1; CpH; CpR 1; CpY; CpR 3; CpH;
            CpR 10; CpY; CpR 4;
     CpH; CpR 8; CpH; CpR 1; CpY; CpR 3; CpH; CpR 8; CpY; CpR 2; CpY; CpR 3;
     CpY; CpR 5; CpY; CpR 4; CpY; CpR 3; CpY; CpR 1; CpY],
     [17; 22; 23; 28])`;;
let cf144 = new_definition
 `cf144 = ([CpH; CpR 2; CpH; CpR 11; CpY; CpR 3; CpH; CpR 10; CpY; CpR 3; CpH;
     CpR 9; CpY; CpR 3; CpH; CpR 8; CpY; CpR 4; CpH; CpR 7; CpH; CpR 7; CpY;
     CpR 3; CpY; CpR 4; CpY; CpR 1; CpY; CpR 2; CpY; CpR 1; CpY],
     [14])`;;
let cf145 = new_definition
 `cf145 = ([CpH; CpR 3; CpH; CpR 11; CpH; CpR 11; CpY; CpR 9; CpH; CpR 1; CpY;
     CpR 7; CpH; CpR 2; CpH; CpR 9; CpY; CpR 7; CpH; CpR 1; CpY; CpR 7; CpY;
     CpR 5; CpY; CpY; CpY; CpR 3; CpY; CpY],
     [5; 19; 27; 29])`;;
let cf146 = new_definition
 `cf146 = ([CpH; CpR 9; CpH; CpR 2; CpH; CpR 11; CpY; CpR 9; CpH;
            CpR 1; CpY; CpR 7;
     CpH; CpR 2; CpH; CpR 9; CpY; CpR 7; CpH; CpR 1; CpY; CpR 7; CpH; CpR 7;
     CpY; CpY; CpR 3; CpY; CpR 1; CpY; CpR 2; CpY; CpR 1; CpY],
     [26])`;;
let cf147 = new_definition
 `cf147 = ([CpH; CpR 8; CpH; CpR 3; CpH; CpR 11; CpH; CpR 11; CpY; CpR 9; CpH;
     CpR 1; CpY; CpR 8; CpH; CpR 1; CpY; CpR 6; CpH; CpR 1; CpH; CpR 1; CpY;
     CpR 6; CpY; CpY; CpY; CpR 3; CpY; CpR 1; CpY; CpY],
     [30])`;;
let cf148 = new_definition
 `cf148 = ([CpH; CpR 10; CpH; CpR 1; CpY; CpR 8; CpH; CpR 2; CpH; CpR 10; CpY;
     CpR 8; CpH; CpR 1; CpY; CpR 7; CpH; CpR 1; CpY; CpR 6; CpH; CpR 7; CpY;
     CpY; CpY; CpR 2; CpH; CpR 1; CpY; CpR 1; CpY; CpY],
     [13])`;;
let cf149 = new_definition
 `cf149 = ([CpH; CpR 9; CpH; CpR 1; CpH; CpR 1; CpY; CpR 3; CpH;
            CpR 10; CpY; CpR 6;
     CpH; CpR 6; CpH; CpR 1; CpH; CpR 1; CpH; CpR 1; CpY; CpR 2; CpY; CpR 3;
     CpY; CpR 1; CpY; CpR 1; CpY; CpR 3; CpY; CpY; CpY],
     [29])`;;
let cf150 = new_definition
 `cf150 = ([CpH; CpR 10; CpH; CpR 1; CpY; CpR 9; CpH; CpR 1; CpY;
            CpR 8; CpH; CpR 8;
     CpH; CpR 1; CpY; CpR 7; CpH; CpR 1; CpY; CpR 7; CpH; CpR 7; CpY; CpR 5;
     CpH; CpR 6; CpY; CpR 3; CpY; CpY; CpY; CpR 2; CpY],
     [32])`;;
let cf151 = new_definition
 `cf151 = ([CpH; CpR 10; CpH; CpR 1; CpY; CpR 9; CpH; CpR 1; CpY;
            CpR 7; CpH; CpR 2;
     CpH; CpR 9; CpY; CpR 7; CpH; CpR 1; CpY; CpR 7; CpH; CpR 7; CpH; CpR 7;
     CpY; CpY; CpY; CpY; CpR 3; CpY; CpY],
     [31])`;;
let cf152 = new_definition
 `cf152 = ([CpH; CpR 2; CpH; CpR 12; CpY; CpR 3; CpH; CpR 11; CpY; CpR 4; CpH;
     CpR 2; CpH; CpR 10; CpY; CpR 3; CpH; CpR 9; CpY; CpR 2; CpH; CpR 1; CpY;
     CpR 1; CpY; CpR 1; CpY; CpR 2; CpH; CpR 5; CpY; CpR 3; CpY; CpY; CpY],
     [4; 5; 22; 27])`;;
let cf153 = new_definition
 `cf153 = ([CpH; CpR 3; CpH; CpR 11; CpH; CpR 11; CpY; CpR 9; CpH; CpR 1; CpY;
     CpR 8; CpH; CpR 1; CpY; CpR 6; CpH; CpR 8; CpY; CpR 6; CpY; CpR 4; CpH;
     CpR 1; CpH; CpR 1; CpY; CpR 4; CpY; CpY; CpR 1; CpY; CpR 1; CpY],
     [32])`;;
let cf154 = new_definition
 `cf154 = ([CpH; CpR 9; CpH; CpR 2; CpH; CpR 11; CpY; CpR 9; CpH;
            CpR 1; CpY; CpR 6;
     CpH; CpR 3; CpH; CpR 9; CpH; CpR 9; CpY; CpR 7; CpH; CpR 1; CpY; CpR 5;
     CpY; CpR 1; CpY; CpR 3; CpY; CpR 1; CpY; CpY; CpR 1; CpY],
     [29])`;;
let cf155 = new_definition
 `cf155 = ([CpH; CpR 4; CpH; CpR 11; CpH; CpR 11; CpH; CpR 11; CpY; CpR 9; CpH;
     CpR 1; CpY; CpR 8; CpH; CpR 1; CpY; CpR 7; CpH; CpR 8; CpY; CpR 5; CpY;
     CpR 1; CpY; CpR 4; CpH; CpR 5; CpY; CpY; CpR 1; CpY; CpR 1; CpY],
     [26])`;;
let cf156 = new_definition
 `cf156 = ([CpH; CpR 4; CpH; CpR 11; CpH; CpR 11; CpH; CpR 11; CpY; CpR 9; CpH;
     CpR 1; CpY; CpR 6; CpH; CpR 3; CpH; CpR 9; CpH; CpR 9; CpY; CpR 8; CpY;
     CpR 5; CpY; CpR 1; CpY; CpR 3; CpY; CpY; CpR 1; CpY; CpR 1; CpY],
     [29])`;;
let cf157 = new_definition
 `cf157 = ([CpH; CpR 10; CpH; CpR 1; CpY; CpR 3; CpH; CpR 10; CpY; CpR 3; CpH;
     CpR 9; CpY; CpR 5; CpH; CpR 1; CpY; CpR 7; CpH; CpR 7; CpH; CpR 7; CpH;
     CpR 7; CpY; CpY; CpR 1; CpY; CpR 3; CpY; CpY; CpY],
     [6])`;;
let cf158 = new_definition
 `cf158 = ([CpH; CpR 10; CpH; CpR 1; CpY; CpR 3; CpH; CpR 10; CpY; CpR 3; CpH;
     CpR 9; CpY; CpR 5; CpH; CpR 1; CpY; CpR 5; CpH; CpR 7; CpY; CpR 3; CpH;
     CpR 1; CpY; CpR 5; CpH; CpR 1; CpY; CpR 3; CpY; CpR 1; CpY; CpR 1; CpY],
     [6])`;;
let cf159 = new_definition
 `cf159 = ([CpH; CpR 10; CpH; CpR 1; CpY; CpR 9; CpH; CpR 1; CpY;
            CpR 8; CpH; CpR 1;
     CpY; CpR 5; CpH; CpR 3; CpH; CpR 8; CpH; CpR 8; CpY; CpR 7; CpH; CpR 1;
     CpY; CpR 1; CpY; CpY; CpR 3; CpY; CpR 1; CpY; CpR 2; CpY],
     [1; 2; 32])`;;
let cf160 = new_definition
 `cf160 = ([CpH; CpR 2; CpH; CpR 12; CpY; CpR 3; CpH; CpR 11; CpY; CpR 3; CpH;
     CpR 2; CpH; CpR 10; CpY; CpR 2; CpH; CpR 9; CpY; CpR 3; CpH; CpR 8; CpH;
     CpR 8; CpY; CpY; CpY; CpR 3; CpH; CpR 5; CpY; CpR 3; CpY; CpY; CpY],
     [30])`;;
let cf161 = new_definition
 `cf161 = ([CpH; CpR 2; CpH; CpR 12; CpY; CpR 3; CpH; CpR 11; CpY; CpR 4; CpH;
     CpR 2; CpH; CpR 10; CpY; CpR 9; CpH; CpR 1; CpY; CpR 3; CpH; CpR 8; CpH;
     CpR 8; CpY; CpY; CpY; CpR 3; CpH; CpR 5; CpY; CpR 3; CpY; CpY; CpY],
     [30])`;;
let cf162 = new_definition
 `cf162 = ([CpH; CpR 4; CpH; CpR 10; CpH; CpR 1; CpH; CpR 1; CpY; CpR 3; CpH;
     CpR 11; CpY; CpR 3; CpH; CpR 2; CpH; CpR 10; CpY; CpR 2; CpH; CpR 9;
     CpY; CpR 2; CpH; CpR 8; CpY; CpY; CpY; CpR 2; CpY; CpR 3; CpY; CpY; CpY],
     [33])`;;
let cf163 = new_definition
 `cf163 = ([CpH; CpR 4; CpH; CpR 10; CpH; CpR 1; CpH; CpR 1; CpY; CpR 3; CpH;
     CpR 11; CpY; CpR 4; CpH; CpR 2; CpH; CpR 10; CpY; CpR 9; CpH; CpR 1;
     CpY; CpR 2; CpH; CpR 8; CpY; CpY; CpY; CpR 2; CpY; CpR 3; CpY; CpY; CpY],
     [33])`;;
let cf164 = new_definition
 `cf164 = ([CpH; CpR 3; CpH; CpR 11; CpH; CpR 1; CpY; CpR 4; CpH; CpR 3; CpH;
     CpR 10; CpH; CpR 1; CpY; CpR 3; CpH; CpR 10; CpY; CpR 2; CpH; CpR 1;
     CpY; CpR 3; CpH; CpR 8; CpY; CpY; CpR 1; CpY; CpR 1; CpY; CpR 3; CpY;
     CpY; CpY],
     [35])`;;
let cf165 = new_definition
 `cf165 = ([CpH; CpR 11; CpH; CpR 1; CpY; CpR 10; CpH; CpR 1; CpY; CpR 8; CpH;
     CpR 9; CpH; CpR 1; CpY; CpR 8; CpH; CpR 1; CpY; CpR 8; CpH; CpR 8; CpY;
     CpR 4; CpH; CpR 7; CpY; CpY; CpR 1; CpY; CpR 2; CpH; CpR 1; CpY; CpR 3;
     CpY; CpR 1; CpY],
     [36])`;;
let cf166 = new_definition
 `cf166 = ([CpH; CpR 10; CpH; CpR 2; CpH; CpR 12; CpY; CpR 8; CpH; CpR 10; CpH;
     CpR 1; CpY; CpR 9; CpH; CpR 1; CpY; CpR 1; CpY; CpR 8; CpH; CpR 1; CpY;
     CpR 1; CpY; CpR 3; CpH; CpR 6; CpH; CpR 6; CpY; CpR 5; CpY; CpR 4; CpY;
     CpY; CpY],
     [11; 12; 18; 19])`;;
let cf167 = new_definition
 `cf167 = ([CpH; CpR 10; CpH; CpR 2; CpH; CpR 12; CpY; CpR 10; CpH; CpR 1; CpY;
     CpR 9; CpH; CpR 1; CpY; CpR 7; CpH; CpR 1; CpH; CpR 8; CpH; CpR 1; CpY;
     CpR 8; CpH; CpR 1; CpY; CpR 1; CpY; CpR 1; CpY; CpR 5; CpY; CpR 4; CpY;
     CpY; CpY],
     [33])`;;
let cf168 = new_definition
 `cf168 = ([CpH; CpR 2; CpH; CpR 12; CpY; CpR 3; CpH; CpR 2; CpH; CpR 11; CpY;
     CpR 4; CpH; CpR 9; CpH; CpR 1; CpY; CpR 4; CpH; CpR 1; CpY; CpR 7; CpH;
     CpR 1; CpH; CpR 1; CpY; CpR 1; CpY; CpR 1; CpY; CpR 4; CpY; CpR 1; CpY;
     CpR 3; CpY; CpY],
     [35])`;;
let cf169 = new_definition
 `cf169 = ([CpH; CpR 10; CpH; CpR 2; CpH; CpR 12; CpY; CpR 9; CpH; CpR 10; CpH;
     CpR 1; CpY; CpR 9; CpH; CpR 1; CpY; CpR 1; CpY; CpR 7; CpH; CpR 1; CpH;
     CpR 1; CpY; CpR 1; CpY; CpR 2; CpH; CpR 6; CpY; CpR 4; CpY; CpR 1; CpY;
     CpR 3; CpY; CpY],
     [11; 12; 18; 19])`;;
let cf170 = new_definition
 `cf170 = ([CpH; CpR 4; CpH; CpR 10; CpH; CpR 1; CpH; CpR 1; CpY; CpR 3; CpH;
     CpR 11; CpY; CpR 5; CpH; CpR 10; CpH; CpR 2; CpH; CpR 10; CpY; CpR 2;
     CpH; CpR 9; CpY; CpY; CpR 7; CpH; CpR 1; CpY; CpR 2; CpY; CpR 4; CpY;
     CpY; CpY; CpY],
     [38])`;;
let cf171 = new_definition
 `cf171 = ([CpH; CpR 2; CpH; CpR 12; CpY; CpR 4; CpH; CpR 2; CpH; CpR 11; CpY;
     CpR 4; CpH; CpR 10; CpH; CpR 2; CpH; CpR 10; CpY; CpR 9; CpH; CpR 1;
     CpY; CpR 1; CpY; CpR 1; CpY; CpR 4; CpH; CpR 6; CpH; CpR 6; CpY; CpR 3;
     CpY; CpY; CpR 3; CpY; CpR 1; CpY],
     [26])`;;
let cf172 = new_definition
 `cf172 = ([CpH; CpR 2; CpH; CpR 12; CpY; CpR 3; CpH; CpR 11; CpY; CpR 4; CpH;
     CpR 10; CpH; CpR 2; CpH; CpR 10; CpY; CpR 9; CpH; CpR 1; CpY; CpR 1;
     CpY; CpR 3; CpH; CpR 7; CpH; CpR 7; CpY; CpR 3; CpH; CpR 6; CpY; CpY;
     CpR 3; CpY; CpY; CpY],
     [34])`;;
let cf173 = new_definition
 `cf173 = ([CpH; CpR 10; CpH; CpR 1; CpY; CpR 9; CpH; CpR 9; CpH;
            CpR 1; CpY; CpR 5;
     CpH; CpR 1; CpH; CpR 3; CpH; CpR 9; CpH; CpR 9; CpH; CpR 9; CpH; CpR 9;
     CpY; CpY; CpR 1; CpY; CpY; CpY; CpR 4; CpY; CpY; CpY],
     [36])`;;
let cf174 = new_definition
 `cf174 = ([CpH; CpR 10; CpH; CpR 1; CpY; CpR 7; CpH; CpR 9; CpH;
            CpR 1; CpY; CpR 9;
     CpH; CpR 9; CpH; CpR 1; CpH; CpR 1; CpY; CpR 4; CpH; CpR 8; CpH; CpR 8;
     CpH; CpR 8; CpY; CpY; CpY; CpY; CpR 4; CpY; CpY; CpY],
     [36])`;;
let cf175 = new_definition
 `cf175 = ([CpH; CpR 2; CpH; CpR 11; CpY; CpR 3; CpH; CpR 2; CpH; CpR 10; CpY;
     CpR 2; CpH; CpR 9; CpY; CpR 8; CpH; CpR 1; CpY; CpR 1; CpY; CpR 2; CpH;
     CpR 6; CpY; CpR 2; CpH; CpR 1; CpH; CpR 1; CpY; CpH; CpR 4; CpY; CpY;
     CpR 1; CpY],
     [20])`;;
let cf176 = new_definition
 `cf176 = ([CpH; CpR 2; CpH; CpR 11; CpY; CpR 6; CpH; CpR 2; CpH; CpR 10; CpY;
     CpR 3; CpH; CpR 1; CpY; CpR 8; CpH; CpR 1; CpY; CpR 1; CpY; CpR 2; CpH;
     CpR 6; CpY; CpR 2; CpH; CpR 1; CpH; CpR 1; CpY; CpR 4; CpH; CpR 1; CpY;
     CpR 3; CpY; CpR 1; CpY],
     [20])`;;
let cf177 = new_definition
 `cf177 = ([CpH; CpR 8; CpH; CpR 3; CpH; CpR 11; CpH; CpR 11; CpY; CpR 9; CpH;
     CpR 9; CpH; CpR 1; CpY; CpR 4; CpH; CpR 1; CpY; CpR 7; CpH; CpR 1; CpY;
     CpR 1; CpY; CpR 1; CpY; CpR 3; CpH; CpR 5; CpH; CpR 5; CpY; CpR 3; CpY;
     CpY; CpY],
     [26])`;;
let cf178 = new_definition
 `cf178 = ([CpH; CpR 11; CpH; CpR 1; CpY; CpR 10; CpH; CpR 1; CpY; CpR 9; CpH;
     CpR 1; CpY; CpR 7; CpH; CpR 2; CpH; CpR 9; CpY; CpR 7; CpH; CpR 1; CpY;
     CpR 7; CpH; CpR 7; CpY; CpR 6; CpY; CpR 4; CpY; CpY; CpR 1; CpY; CpY],
     [29])`;;
let cf179 = new_definition
 `cf179 = ([CpH; CpR 4; CpH; CpR 11; CpH; CpR 11; CpH; CpR 11; CpY; CpR 9; CpH;
     CpR 1; CpY; CpR 8; CpH; CpR 1; CpY; CpR 7; CpH; CpR 1; CpY; CpR 7; CpY;
     CpR 6; CpH; CpR 6; CpY; CpR 3; CpY; CpR 3; CpY; CpY; CpR 1; CpY],
     [32])`;;
let cf180 = new_definition
 `cf180 = ([CpH; CpR 3; CpH; CpR 12; CpH; CpR 12; CpY; CpR 9; CpH; CpR 2; CpH;
     CpR 11; CpY; CpR 8; CpH; CpR 2; CpH; CpR 10; CpY; CpR 8; CpH; CpR 1;
     CpY; CpR 8; CpY; CpR 6; CpY; CpY; CpR 4; CpY; CpR 2; CpY; CpR 3; CpY;
     CpY],
     [7])`;;
let cf181 = new_definition
 `cf181 = ([CpH; CpR 10; CpH; CpR 1; CpH; CpR 1; CpY; CpR 4; CpH; CpR 10; CpH;
     CpR 1; CpY; CpR 4; CpH; CpR 9; CpH; CpR 1; CpY; CpR 3; CpH; CpR 9; CpY;
     CpR 2; CpY; CpR 3; CpY; CpR 1; CpY; CpR 4; CpY; CpR 3; CpY; CpR 2; CpY;
     CpY],
     [7; 29; 32])`;;
let cf182 = new_definition
 `cf182 = ([CpH; CpR 10; CpH; CpR 2; CpH; CpR 12; CpY; CpR 10; CpH; CpR 1; CpY;
     CpR 9; CpH; CpR 1; CpY; CpR 8; CpH; CpR 1; CpY; CpR 7; CpH; CpR 1; CpY;
     CpR 7; CpH; CpR 7; CpY; CpY; CpR 3; CpY; CpR 3; CpY; CpY; CpR 2; CpY],
     [27])`;;
let cf183 = new_definition
 `cf183 = ([CpH; CpR 3; CpH; CpR 12; CpH; CpR 12; CpY; CpR 10; CpH; CpR 1; CpY;
     CpR 9; CpH; CpR 1; CpY; CpR 8; CpH; CpR 1; CpY; CpR 7; CpH; CpR 1; CpY;
     CpR 4; CpY; CpR 3; CpH; CpR 6; CpY; CpR 2; CpY; CpR 3; CpY; CpR 3; CpY;
     CpY],
     [16; 32])`;;
let cf184 = new_definition
 `cf184 = ([CpH; CpR 10; CpH; CpR 1; CpH; CpR 1; CpY; CpR 3; CpH; CpR 11; CpY;
     CpR 3; CpH; CpR 2; CpH; CpR 10; CpY; CpR 3; CpH; CpR 9; CpY; CpR 2; CpY;
     CpR 3; CpY; CpR 6; CpY; CpR 3; CpH; CpR 1; CpY; CpR 4; CpY; CpR 2; CpY;
     CpY],
     [33])`;;
let cf185 = new_definition
 `cf185 = ([CpH; CpR 2; CpH; CpR 12; CpY; CpR 3; CpH; CpR 11; CpY; CpR 4; CpH;
     CpR 9; CpH; CpR 1; CpY; CpR 3; CpH; CpR 9; CpY; CpR 4; CpH; CpR 8; CpH;
     CpR 8; CpY; CpR 3; CpY; CpR 4; CpY; CpR 1; CpY; CpR 1; CpY; CpR 2; CpY;
     CpR 1; CpY],
     [8; 31; 33])`;;
let cf186 = new_definition
 `cf186 = ([CpH; CpR 2; CpH; CpR 12; CpY; CpR 3; CpH; CpR 11; CpY; CpR 3; CpH;
     CpR 10; CpY; CpR 3; CpH; CpR 9; CpY; CpR 3; CpH; CpR 8; CpY; CpR 3; CpH;
     CpR 1; CpY; CpR 6; CpH; CpR 6; CpY; CpY; CpR 1; CpY; CpR 2; CpY; CpR 1;
     CpY],
     [14])`;;
let cf187 = new_definition
 `cf187 = ([CpH; CpR 11; CpH; CpR 1; CpY; CpR 9; CpH; CpR 2; CpH; CpR 11; CpY;
     CpR 9; CpH; CpR 1; CpY; CpR 8; CpH; CpR 1; CpY; CpR 6; CpH; CpR 1; CpH;
     CpR 1; CpY; CpR 6; CpY; CpY; CpY; CpR 3; CpY; CpR 1; CpY; CpY],
     [25; 30; 33])`;;
let cf188 = new_definition
 `cf188 = ([CpH; CpR 10; CpH; CpR 1; CpH; CpR 1; CpY; CpR 3; CpH; CpR 11; CpY;
     CpR 3; CpH; CpR 10; CpY; CpR 5; CpH; CpR 7; CpH; CpR 1; CpH; CpR 1; CpY;
     CpR 2; CpY; CpR 3; CpY; CpR 5; CpY; CpY; CpR 3; CpY; CpR 1; CpY; CpR 1;
     CpY],
     [32])`;;
let cf189 = new_definition
 `cf189 = ([CpH; CpR 11; CpH; CpR 1; CpY; CpR 10; CpH; CpR 1; CpY; CpR 9; CpH;
     CpR 1; CpY; CpR 8; CpH; CpR 1; CpY; CpR 6; CpH; CpR 2; CpH; CpR 8; CpY;
     CpR 7; CpH; CpR 7; CpY; CpR 2; CpY; CpR 2; CpY; CpR 3; CpY; CpY; CpR 2;
     CpY],
     [33])`;;
let cf190 = new_definition
 `cf190 = ([CpH; CpR 2; CpH; CpR 12; CpY; CpR 3; CpH; CpR 11; CpY; CpR 4; CpH;
     CpR 9; CpH; CpR 1; CpY; CpR 3; CpH; CpR 9; CpY; CpR 3; CpH; CpR 8; CpY;
     CpR 2; CpH; CpR 1; CpY; CpR 6; CpY; CpR 5; CpY; CpR 3; CpY; CpR 1; CpY;
     CpR 1; CpY],
     [30])`;;
let cf191 = new_definition
 `cf191 = ([CpH; CpR 2; CpH; CpR 12; CpY; CpR 3; CpH; CpR 11; CpY; CpR 3; CpH;
     CpR 10; CpY; CpR 3; CpH; CpR 9; CpY; CpR 3; CpH; CpR 8; CpY; CpR 2; CpH;
     CpR 1; CpH; CpR 1; CpY; CpR 5; CpY; CpR 1; CpY; CpR 2; CpY; CpR 1; CpY;
     CpR 1; CpY],
     [31])`;;
let cf192 = new_definition
 `cf192 = ([CpH; CpR 11; CpH; CpR 1; CpY; CpR 9; CpH; CpR 2; CpH; CpR 11; CpY;
     CpR 9; CpH; CpR 1; CpY; CpR 8; CpH; CpR 1; CpY; CpR 7; CpH; CpR 1; CpY;
     CpR 7; CpH; CpR 7; CpY; CpY; CpY; CpR 3; CpY; CpR 2; CpY; CpR 2; CpY],
     [27])`;;
let cf193 = new_definition
 `cf193 = ([CpH; CpR 11; CpH; CpR 1; CpY; CpR 4; CpH; CpR 10; CpH; CpR 1; CpY;
     CpR 5; CpH; CpR 8; CpH; CpR 1; CpH; CpR 1; CpY; CpR 3; CpH; CpR 9; CpY;
     CpR 2; CpY; CpR 4; CpY; CpY; CpR 4; CpY; CpR 3; CpY; CpR 2; CpY; CpY],
     [18; 21; 30; 33])`;;
let cf194 = new_definition
 `cf194 = ([CpH; CpR 4; CpH; CpR 12; CpH; CpR 12; CpH; CpR 12; CpY; CpR 9; CpH;
     CpR 2; CpH; CpR 11; CpY; CpR 9; CpH; CpR 1; CpY; CpR 8; CpH; CpR 1; CpY;
     CpR 8; CpY; CpR 5; CpY; CpR 1; CpY; CpR 3; CpY; CpR 3; CpY; CpY; CpR 2;
     CpY],
     [6; 10; 19; 33])`;;
let cf195 = new_definition
 `cf195 = ([CpH; CpR 10; CpH; CpR 2; CpH; CpR 12; CpY; CpR 10; CpH; CpR 1; CpY;
     CpR 8; CpH; CpR 2; CpH; CpR 10; CpY; CpR 8; CpH; CpR 1; CpY; CpR 7; CpH;
     CpR 1; CpY; CpR 5; CpY; CpR 1; CpY; CpR 3; CpY; CpR 1; CpY; CpY; CpR 1;
     CpY],
     [18])`;;
let cf196 = new_definition
 `cf196 = ([CpH; CpR 4; CpH; CpR 12; CpH; CpR 12; CpH; CpR 12; CpY;
            CpR 10; CpH;
     CpR 1; CpY; CpR 9; CpH; CpR 1; CpY; CpR 7; CpH; CpR 2; CpH; CpR 9; CpY;
     CpR 8; CpY; CpR 5; CpY; CpR 1; CpY; CpR 3; CpY; CpY; CpR 1; CpY; CpR 1;
     CpY],
     [32])`;;
let cf197 = new_definition
 `cf197 = ([CpH; CpR 11; CpH; CpR 1; CpY; CpR 3; CpH; CpR 11; CpY; CpR 3; CpH;
     CpR 10; CpY; CpR 4; CpH; CpR 2; CpH; CpR 9; CpY; CpR 2; CpY; CpR 6; CpH;
     CpR 7; CpH; CpR 7; CpY; CpY; CpR 1; CpY; CpR 3; CpY; CpY; CpY],
     [24])`;;
let cf198 = new_definition
 `cf198 = ([CpH; CpR 11; CpH; CpR 1; CpY; CpR 3; CpH; CpR 11; CpY; CpR 3; CpH;
     CpR 10; CpY; CpR 4; CpH; CpR 2; CpH; CpR 9; CpY; CpR 2; CpY; CpR 5; CpH;
     CpR 7; CpY; CpR 4; CpY; CpR 3; CpY; CpR 2; CpH; CpR 4; CpY; CpR 2; CpY;
     CpY],
     [33])`;;
let cf199 = new_definition
 `cf199 = ([CpH; CpR 11; CpH; CpR 1; CpY; CpR 3; CpH; CpR 11; CpY; CpR 3; CpH;
     CpR 10; CpY; CpR 6; CpH; CpR 6; CpH; CpR 1; CpH; CpR 1; CpH; CpR 1; CpY;
     CpR 2; CpY; CpR 4; CpY; CpR 4; CpY; CpY; CpR 3; CpY; CpR 1; CpY; CpR 1;
     CpY],
     [21; 24; 30; 33])`;;
let cf200 = new_definition
 `cf200 = ([CpH; CpR 3; CpH; CpR 12; CpH; CpR 12; CpY; CpR 10; CpH; CpR 1; CpY;
     CpR 7; CpH; CpR 3; CpH; CpR 10; CpH; CpR 10; CpY; CpR 8; CpH; CpR 1;
     CpY; CpR 8; CpY; CpR 5; CpY; CpR 1; CpY; CpY; CpY; CpR 3; CpY; CpY],
     [23])`;;
let cf201 = new_definition
 `cf201 = ([CpH; CpR 11; CpH; CpR 1; CpY; CpR 10; CpH; CpR 1; CpY; CpR 9; CpH;
     CpR 1; CpY; CpR 6; CpH; CpR 3; CpH; CpR 9; CpH; CpR 9; CpY; CpR 7; CpH;
     CpR 1; CpY; CpR 5; CpY; CpR 4; CpY; CpR 1; CpY; CpR 3; CpY; CpR 2; CpY;
     CpR 1; CpY],
     [1; 2; 32])`;;
let cf202 = new_definition
 `cf202 = ([CpH; CpR 9; CpH; CpR 1; CpY; CpR 8; CpH; CpR 1; CpY;
            CpR 7; CpH; CpR 1;
     CpY; CpR 6; CpH; CpR 1; CpY; CpR 5; CpH; CpR 1; CpH; CpR 2; CpH; CpR 6;
     CpY; CpH; CpR 1; CpY; CpR 3; CpY; CpR 1; CpY; CpR 1; CpY],
     [10])`;;
let cf203 = new_definition
 `cf203 = ([CpH; CpR 2; CpH; CpR 13; CpY; CpR 3; CpH; CpR 12; CpY; CpR 3; CpH;
     CpR 2; CpH; CpR 11; CpY; CpR 3; CpH; CpR 10; CpY; CpY; CpR 3; CpH;
     CpR 8; CpH; CpR 8; CpY; CpY; CpY; CpR 3; CpH; CpR 5; CpY; CpR 3; CpY;
     CpY; CpY],
     [12; 13; 19; 20])`;;
let cf204 = new_definition
 `cf204 = ([CpH; CpR 11; CpH; CpR 1; CpY; CpR 9; CpH; CpR 2; CpH; CpR 11; CpY;
     CpR 7; CpH; CpR 3; CpH; CpR 10; CpH; CpR 10; CpY; CpR 7; CpH; CpR 1;
     CpH; CpR 1; CpY; CpR 7; CpY; CpR 6; CpY; CpR 5; CpY; CpR 1; CpY; CpR 3;
     CpY; CpY; CpR 2; CpY],
     [36])`;;
let cf205 = new_definition
 `cf205 = ([CpH; CpR 3; CpH; CpR 12; CpH; CpR 12; CpY; CpR 9; CpH; CpR 2; CpH;
     CpR 11; CpY; CpR 9; CpH; CpR 1; CpY; CpR 8; CpH; CpR 9; CpH; CpR 9; CpY;
     CpR 7; CpY; CpR 7; CpY; CpR 6; CpH; CpR 6; CpY; CpY; CpR 3; CpY; CpR 2;
     CpY; CpR 1; CpY],
     [35])`;;
let cf206 = new_definition
 `cf206 = ([CpH; CpR 11; CpH; CpR 1; CpY; CpR 10; CpH; CpR 1; CpY; CpR 8; CpH;
     CpR 9; CpH; CpR 1; CpY; CpR 7; CpH; CpR 1; CpH; CpR 1; CpY; CpR 7; CpY;
     CpR 5; CpH; CpR 1; CpH; CpR 1; CpY; CpR 4; CpY; CpR 1; CpY; CpY; CpR 1;
     CpY; CpR 1; CpY],
     [36])`;;
let cf207 = new_definition
 `cf207 = ([CpH; CpR 11; CpH; CpR 2; CpH; CpR 13; CpY; CpR 10; CpH; CpR 2; CpH;
     CpR 12; CpY; CpR 10; CpH; CpR 10; CpH; CpR 1; CpY; CpR 9; CpH; CpR 1;
     CpY; CpR 1; CpY; CpR 8; CpH; CpR 1; CpY; CpR 1; CpY; CpR 1; CpY; CpR 5;
     CpY; CpR 4; CpY; CpY; CpY],
     [18; 19; 25; 26])`;;
let cf208 = new_definition
 `cf208 = ([CpH; CpR 4; CpH; CpR 12; CpH; CpR 12; CpH; CpR 12; CpY;
            CpR 10; CpH;
     CpR 10; CpH; CpR 1; CpY; CpR 8; CpH; CpR 2; CpH; CpR 10; CpY; CpR 9;
     CpY; CpR 5; CpH; CpR 1; CpY; CpR 1; CpY; CpR 6; CpY; CpR 4; CpY; CpR 3;
     CpY; CpR 2; CpY; CpR 1; CpY],
     [35])`;;
let cf209 = new_definition
 `cf209 = ([CpH; CpR 4; CpH; CpR 12; CpH; CpR 12; CpH; CpR 12; CpY;
            CpR 10; CpH;
     CpR 1; CpY; CpR 8; CpH; CpR 9; CpH; CpR 1; CpY; CpR 9; CpY; CpR 6; CpY;
     CpR 1; CpY; CpR 6; CpH; CpR 6; CpH; CpR 6; CpY; CpY; CpY; CpR 1; CpY;
     CpR 1; CpY],
     [26])`;;
let cf210 = new_definition
 `cf210 = ([CpH; CpR 11; CpH; CpR 1; CpY; CpR 8; CpH; CpR 10; CpH; CpR 1; CpY;
     CpR 9; CpH; CpR 1; CpY; CpR 8; CpH; CpR 1; CpY; CpR 6; CpH; CpR 8; CpH;
     CpR 8; CpH; CpR 8; CpY; CpY; CpR 1; CpY; CpR 4; CpY; CpY; CpY; CpY],
     [35])`;;
let cf211 = new_definition
 `cf211 = ([CpH; CpR 11; CpH; CpR 1; CpY; CpR 8; CpH; CpR 3; CpH; CpR 11; CpH;
     CpR 11; CpY; CpR 9; CpH; CpR 1; CpY; CpR 8; CpH; CpR 1; CpY; CpR 5; CpY;
     CpR 2; CpH; CpR 7; CpY; CpY; CpY; CpR 2; CpH; CpR 1; CpY; CpR 1; CpY;
     CpY],
     [31])`;;
let cf212 = new_definition
 `cf212 = ([CpH; CpR 5; CpH; CpR 9; CpH; CpR 1; CpH; CpR 1; CpH;
            CpR 1; CpY; CpR 3;
     CpH; CpR 11; CpY; CpR 3; CpH; CpR 10; CpY; CpR 3; CpH; CpR 9; CpY;
     CpR 2; CpH; CpR 1; CpY; CpR 1; CpY; CpY; CpR 3; CpY; CpR 1; CpY; CpR 1;
     CpY; CpR 2; CpY],
     [35])`;;
let cf213 = new_definition
 `cf213 = ([CpH; CpR 2; CpH; CpR 13; CpY; CpR 3; CpH; CpR 12; CpY; CpR 3; CpH;
     CpR 2; CpH; CpR 11; CpY; CpR 3; CpH; CpR 10; CpY; CpR 9; CpH; CpR 1;
     CpY; CpR 3; CpH; CpR 8; CpH; CpR 8; CpY; CpY; CpY; CpR 3; CpH; CpR 5;
     CpY; CpR 3; CpY; CpY; CpY],
     [34])`;;
let cf214 = new_definition
 `cf214 = ([CpH; CpR 11; CpH; CpR 1; CpY; CpR 10; CpH; CpR 1; CpY; CpR 8; CpH;
     CpR 9; CpH; CpR 1; CpY; CpR 9; CpH; CpR 9; CpH; CpR 1; CpH; CpR 1; CpY;
     CpR 3; CpH; CpR 8; CpH; CpR 8; CpY; CpY; CpY; CpY; CpR 4; CpY; CpY; CpY],
     [37])`;;
let cf215 = new_definition
 `cf215 = ([CpH; CpR 2; CpH; CpR 13; CpY; CpR 4; CpH; CpR 2; CpH; CpR 12; CpY;
     CpR 3; CpH; CpR 2; CpH; CpR 11; CpY; CpR 2; CpH; CpR 10; CpY; CpR 9;
     CpH; CpR 1; CpY; CpR 1; CpY; CpR 1; CpY; CpR 4; CpH; CpR 1; CpY; CpR 5;
     CpH; CpR 1; CpY; CpR 4; CpY; CpY; CpR 1; CpY],
     [27])`;;
let cf216 = new_definition
 `cf216 = ([CpH; CpR 2; CpH; CpR 13; CpY; CpR 3; CpH; CpR 2; CpH; CpR 12; CpY;
     CpR 3; CpH; CpR 11; CpY; CpY; CpR 4; CpH; CpR 9; CpH; CpR 9; CpH; CpR 9;
     CpY; CpY; CpY; CpR 5; CpH; CpR 6; CpH; CpR 6; CpY; CpY; CpR 3; CpY; CpY;
     CpY],
     [8; 9; 15; 16])`;;
let cf217 = new_definition
 `cf217 = ([CpH; CpR 12; CpH; CpR 1; CpY; CpR 10; CpH; CpR 11; CpH; CpR 1; CpY;
     CpR 10; CpH; CpR 1; CpY; CpR 1; CpY; CpR 7; CpH; CpR 1; CpH; CpR 1; CpH;
     CpR 1; CpY; CpR 1; CpY; CpR 2; CpH; CpR 7; CpY; CpR 4; CpH; CpR 1; CpY;
     CpR 1; CpY; CpR 4; CpY; CpY; CpY],
     [8; 9; 15; 16])`;;
let cf218 = new_definition
 `cf218 = ([CpH; CpR 3; CpH; CpR 12; CpH; CpR 12; CpY; CpR 10; CpH; CpR 1; CpY;
     CpR 9; CpH; CpR 1; CpY; CpR 8; CpH; CpR 1; CpY; CpR 7; CpH; CpR 1; CpY;
     CpR 7; CpY; CpR 1; CpY; CpR 5; CpH; CpR 5; CpY; CpY; CpY; CpR 1; CpY],
     [33])`;;
let cf219 = new_definition
 `cf219 = ([CpH; CpR 12; CpH; CpR 1; CpY; CpR 11; CpH; CpR 1; CpY; CpR 10; CpH;
     CpR 1; CpY; CpR 9; CpH; CpR 1; CpY; CpR 8; CpH; CpR 1; CpY; CpR 7; CpH;
     CpR 1; CpY; CpR 7; CpH; CpR 7; CpY; CpR 3; CpY; CpR 4; CpY; CpY; CpY;
     CpR 2; CpY],
     [28])`;;
let cf220 = new_definition
 `cf220 = ([CpH; CpR 11; CpH; CpR 1; CpY; CpR 10; CpH; CpR 1; CpY; CpR 9; CpH;
     CpR 1; CpY; CpR 8; CpH; CpR 1; CpY; CpR 5; CpH; CpR 3; CpH; CpR 8; CpH;
     CpR 8; CpY; CpR 1; CpH; CpR 1; CpY; CpR 5; CpY; CpR 3; CpY; CpR 1; CpY;
     CpY; CpR 2; CpY],
     [36])`;;
let cf221 = new_definition
 `cf221 = ([CpH; CpR 3; CpH; CpR 12; CpH; CpR 1; CpY; CpR 3; CpH; CpR 12; CpY;
     CpR 4; CpH; CpR 10; CpH; CpR 1; CpY; CpR 3; CpH; CpR 10; CpY; CpR 3;
     CpH; CpR 9; CpY; CpR 2; CpH; CpR 1; CpY; CpR 1; CpY; CpR 5; CpY; CpR 3;
     CpY; CpR 1; CpY; CpR 2; CpY; CpY],
     [31])`;;
let cf222 = new_definition
 `cf222 = ([CpH; CpR 2; CpH; CpR 13; CpY; CpR 3; CpH; CpR 12; CpY; CpR 5; CpH;
     CpR 9; CpH; CpR 1; CpH; CpR 1; CpY; CpR 3; CpH; CpR 10; CpY; CpR 4; CpH;
     CpR 9; CpH; CpR 9; CpY; CpR 3; CpY; CpR 6; CpY; CpY; CpY; CpR 3; CpY;
     CpR 1; CpY; CpR 1; CpY],
     [34])`;;
let cf223 = new_definition
 `cf223 = ([CpH; CpR 12; CpH; CpR 1; CpY; CpR 11; CpH; CpR 11; CpH; CpR 1; CpY;
     CpR 10; CpH; CpR 1; CpY; CpR 9; CpH; CpR 1; CpY; CpR 8; CpH; CpR 1; CpY;
     CpR 8; CpH; CpR 8; CpY; CpR 2; CpY; CpR 5; CpH; CpR 6; CpY; CpR 2; CpY;
     CpR 4; CpY; CpR 1; CpY; CpR 2; CpY],
     [37])`;;
let cf224 = new_definition
 `cf224 = ([CpH; CpR 12; CpH; CpR 1; CpY; CpR 11; CpH; CpR 1; CpY; CpR 10; CpH;
     CpR 1; CpY; CpR 9; CpH; CpR 1; CpY; CpR 8; CpH; CpR 1; CpY; CpR 7; CpH;
     CpR 8; CpH; CpR 8; CpY; CpR 3; CpH; CpR 7; CpY; CpR 2; CpY; CpR 4; CpY;
     CpY; CpR 3; CpY; CpY],
     [36])`;;
let cf225 = new_definition
 `cf225 = ([CpH; CpR 2; CpH; CpR 13; CpY; CpR 3; CpH; CpR 12; CpY; CpR 3; CpH;
     CpR 11; CpY; CpR 3; CpH; CpR 10; CpY; CpR 3; CpH; CpR 9; CpY; CpR 3;
     CpH; CpR 8; CpY; CpR 3; CpH; CpR 6; CpH; CpR 1; CpY; CpR 6; CpY; CpR 1;
     CpY; CpR 2; CpY; CpR 1; CpY; CpR 1; CpY],
     [35])`;;
let cf226 = new_definition
 `cf226 = ([CpH; CpR 12; CpH; CpR 1; CpY; CpR 10; CpH; CpR 2; CpH; CpR 12; CpY;
     CpR 10; CpH; CpR 1; CpY; CpR 8; CpH; CpR 2; CpH; CpR 10; CpY; CpR 8;
     CpH; CpR 1; CpY; CpR 8; CpH; CpR 8; CpY; CpR 6; CpY; CpR 5; CpY; CpR 4;
     CpY; CpY; CpR 2; CpY; CpR 1; CpY],
     [35; 37])`;;
let cf227 = new_definition
 `cf227 = ([CpH; CpR 12; CpH; CpR 1; CpY; CpR 10; CpH; CpR 2; CpH; CpR 12; CpY;
     CpR 9; CpH; CpR 2; CpH; CpR 11; CpY; CpR 9; CpH; CpR 1; CpY; CpR 8; CpH;
     CpR 1; CpY; CpR 8; CpH; CpR 8; CpY; CpY; CpY; CpR 4; CpY; CpR 2; CpY;
     CpR 3; CpY; CpY],
     [30])`;;
let cf228 = new_definition
 `cf228 = ([CpH; CpR 11; CpH; CpR 2; CpH; CpR 13; CpY; CpR 11; CpH; CpR 1; CpY;
     CpR 9; CpH; CpR 2; CpH; CpR 11; CpY; CpR 9; CpH; CpR 1; CpY; CpR 7; CpH;
     CpR 1; CpH; CpR 1; CpY; CpR 7; CpY; CpR 7; CpY; CpR 4; CpY; CpR 4; CpY;
     CpR 3; CpY; CpY; CpR 1; CpY],
     [35])`;;
let cf229 = new_definition
 `cf229 = ([CpH; CpR 3; CpH; CpR 13; CpH; CpR 13; CpY; CpR 10; CpH; CpR 2; CpH;
     CpR 12; CpY; CpR 10; CpH; CpR 1; CpY; CpR 7; CpH; CpR 3; CpH; CpR 10;
     CpH; CpR 10; CpY; CpR 9; CpY; CpR 7; CpY; CpR 3; CpY; CpR 4; CpY; CpR 3;
     CpY; CpR 1; CpY; CpR 2; CpY; CpY],
     [36])`;;
let cf230 = new_definition
 `cf230 = ([CpH; CpR 4; CpH; CpR 13; CpH; CpR 13; CpH; CpR 13; CpY;
            CpR 10; CpH;
     CpR 2; CpH; CpR 12; CpY; CpR 9; CpH; CpR 2; CpH; CpR 11; CpY; CpR 9;
     CpH; CpR 1; CpY; CpR 9; CpY; CpR 6; CpY; CpR 1; CpY; CpR 4; CpY; CpR 3;
     CpY; CpY; CpR 3; CpY; CpY],
     [7])`;;
let cf231 = new_definition
 `cf231 = ([CpH; CpR 10; CpH; CpR 1; CpH; CpR 1; CpH; CpR 1; CpY; CpR 4; CpH;
     CpR 11; CpH; CpR 1; CpY; CpR 4; CpH; CpR 10; CpH; CpR 1; CpY; CpR 3;
     CpH; CpR 10; CpY; CpR 2; CpY; CpR 4; CpY; CpY; CpR 5; CpY; CpR 3; CpY;
     CpR 1; CpY; CpR 2; CpY; CpY],
     [19])`;;
let cf232 = new_definition
 `cf232 = ([CpH; CpR 2; CpH; CpR 13; CpY; CpR 5; CpH; CpR 10; CpH; CpR 1; CpH;
     CpR 1; CpY; CpR 3; CpH; CpR 11; CpY; CpR 4; CpH; CpR 9; CpH; CpR 1; CpY;
     CpR 3; CpH; CpR 9; CpY; CpR 6; CpY; CpR 1; CpY; CpR 1; CpY; CpR 3; CpY;
     CpR 1; CpY; CpY; CpR 1; CpY],
     [11; 33; 37])`;;
let cf233 = new_definition
 `cf233 = ([CpH; CpR 3; CpH; CpR 13; CpH; CpR 13; CpY; CpR 11; CpH; CpR 1; CpY;
     CpR 9; CpH; CpR 2; CpH; CpR 11; CpY; CpR 8; CpH; CpR 2; CpH; CpR 10;
     CpY; CpR 9; CpH; CpR 9; CpY; CpR 6; CpY; CpR 5; CpY; CpY; CpR 4; CpY;
     CpY; CpY; CpR 2; CpY],
     [35])`;;
let cf234 = new_definition
 `cf234 = ([CpH; CpR 2; CpH; CpR 13; CpY; CpR 10; CpH; CpR 2; CpH; CpR 12; CpY;
     CpR 7; CpH; CpR 4; CpH; CpR 11; CpH; CpR 11; CpH; CpR 11; CpY; CpR 9;
     CpH; CpR 1; CpY; CpR 9; CpY; CpR 6; CpY; CpY; CpR 5; CpY; CpR 3; CpY;
     CpY; CpR 3; CpY; CpY],
     [6])`;;
let cf235 = new_definition
 `cf235 = ([CpH; CpR 12; CpH; CpR 1; CpY; CpR 9; CpH; CpR 11; CpH; CpR 1; CpY;
     CpR 10; CpH; CpR 1; CpY; CpR 9; CpH; CpR 1; CpY; CpR 9; CpY; CpR 7; CpH;
     CpR 1; CpY; CpR 7; CpH; CpR 1; CpY; CpR 6; CpH; CpR 6; CpY; CpY; CpY;
     CpR 1; CpY; CpR 1; CpY],
     [32])`;;
let cf236 = new_definition
 `cf236 = ([CpH; CpR 10; CpH; CpR 1; CpY; CpR 9; CpH; CpR 1; CpY;
            CpR 8; CpH; CpR 1;
     CpY; CpR 7; CpH; CpR 1; CpY; CpR 6; CpH; CpR 1; CpY; CpR 5; CpH; CpR 1;
     CpH; CpR 6; CpH; CpR 1; CpH; CpR 1; CpY; CpR 1; CpY; CpR 1; CpY; CpY;
     CpY],
     [10])`;;
let cf237 = new_definition
 `cf237 = ([CpH; CpR 12; CpH; CpR 1; CpY; CpR 11; CpH; CpR 9; CpH; CpR 3; CpH;
     CpR 12; CpH; CpR 12; CpY; CpR 10; CpH; CpR 1; CpY; CpR 8; CpH; CpR 1;
     CpH; CpR 1; CpY; CpR 8; CpY; CpR 8; CpH; CpR 8; CpY; CpY; CpR 5; CpY;
     CpR 4; CpY; CpY; CpR 3; CpY; CpY],
     [36])`;;
let cf238 = new_definition
 `cf238 = ([CpH; CpR 12; CpH; CpR 1; CpY; CpR 11; CpH; CpR 11; CpH; CpR 1; CpY;
     CpR 7; CpH; CpR 4; CpH; CpR 11; CpH; CpR 11; CpH; CpR 11; CpY; CpR 9;
     CpH; CpR 10; CpY; CpR 2; CpH; CpR 9; CpY; CpY; CpY; CpR 3; CpH; CpR 1;
     CpY; CpR 1; CpY; CpR 1; CpY; CpR 1; CpY; CpR 2; CpY],
     [43])`;;
let cf239 = new_definition
 `cf239 = ([CpH; CpR 4; CpH; CpR 11; CpH; CpR 1; CpH; CpR 1; CpY;
            CpR 3; CpH; CpR 2;
     CpH; CpR 12; CpY; CpR 4; CpH; CpR 10; CpH; CpR 1; CpY; CpR 5; CpH;
     CpR 1; CpY; CpR 7; CpH; CpR 1; CpH; CpR 1; CpY; CpR 1; CpY; CpR 1; CpY;
     CpR 1; CpY; CpR 4; CpY; CpY; CpY; CpY],
     [36])`;;
let cf240 = new_definition
 `cf240 = ([CpH; CpR 12; CpH; CpR 1; CpY; CpR 11; CpH; CpR 1; CpY; CpR 10; CpH;
     CpR 1; CpY; CpR 9; CpH; CpR 1; CpY; CpR 8; CpH; CpR 1; CpY; CpR 8; CpH;
     CpR 8; CpH; CpR 8; CpH; CpR 8; CpY; CpR 2; CpH; CpR 1; CpY; CpR 5; CpY;
     CpY; CpR 3; CpY; CpR 1; CpY; CpY],
     [38])`;;
let cf241 = new_definition
 `cf241 = ([CpH; CpR 12; CpH; CpR 1; CpY; CpR 11; CpH; CpR 1; CpY; CpR 10; CpH;
     CpR 1; CpY; CpR 9; CpH; CpR 1; CpY; CpR 8; CpH; CpR 1; CpY; CpR 6; CpH;
     CpR 1; CpH; CpR 1; CpH; CpR 8; CpH; CpR 8; CpY; CpY; CpY; CpR 2; CpH;
     CpR 1; CpY; CpR 1; CpY; CpR 1; CpY; CpY],
     [37])`;;
let cf242 = new_definition
 `cf242 = ([CpH; CpR 9; CpH; CpR 1; CpY; CpR 8; CpH; CpR 1; CpY;
            CpR 7; CpH; CpR 1;
     CpY; CpR 6; CpH; CpR 1; CpY; CpR 5; CpH; CpR 1; CpH; CpR 1; CpY; CpH;
     CpR 5; CpY; CpR 4; CpY; CpR 1; CpY; CpR 1; CpY],
     [14])`;;
let cf243 = new_definition
 `cf243 = ([CpH; CpR 3; CpH; CpR 11; CpH; CpR 11; CpY; CpR 7; CpH; CpR 3; CpH;
     CpR 10; CpH; CpR 10; CpY; CpR 7; CpH; CpR 2; CpH; CpR 9; CpY; CpR 8;
     CpY; CpR 6; CpY; CpY; CpR 2; CpY; CpR 3; CpY; CpY; CpR 2; CpY],
     [32])`;;
let cf244 = new_definition
 `cf244 = ([CpH; CpR 3; CpH; CpR 11; CpH; CpR 11; CpY; CpR 7; CpH; CpR 3; CpH;
     CpR 10; CpH; CpR 10; CpY; CpR 7; CpH; CpR 2; CpH; CpR 9; CpY; CpR 8;
     CpY; CpR 6; CpY; CpY; CpY; CpR 3; CpY; CpR 1; CpY; CpR 2; CpY],
     [32])`;;
let cf245 = new_definition
 `cf245 = ([CpH; CpR 10; CpH; CpR 1; CpY; CpR 9; CpH; CpR 1; CpY;
            CpR 8; CpH; CpR 8;
     CpH; CpR 1; CpY; CpR 6; CpH; CpR 1; CpH; CpR 1; CpY; CpR 6; CpY; CpR 5;
     CpH; CpR 1; CpY; CpR 1; CpY; CpY; CpR 3; CpY; CpY],
     [30])`;;
let cf246 = new_definition
 `cf246 = ([CpH; CpR 2; CpH; CpR 11; CpY; CpR 8; CpH; CpR 2; CpH; CpR 10; CpY;
     CpR 8; CpH; CpR 7; CpH; CpR 2; CpH; CpR 9; CpY; CpR 8; CpY; CpR 4; CpH;
     CpR 1; CpY; CpR 1; CpY; CpY; CpR 3; CpY; CpR 1; CpY; CpR 2; CpY],
     [1; 2; 30])`;;
let cf247 = new_definition
 `cf247 = ([CpH; CpR 10; CpH; CpR 1; CpY; CpR 4; CpH; CpR 9; CpH;
            CpR 1; CpY; CpR 3;
     CpH; CpR 9; CpY; CpR 4; CpH; CpR 1; CpY; CpR 4; CpY; CpY; CpR 3; CpH;
     CpR 1; CpY; CpR 4; CpH; CpR 1; CpY; CpR 3; CpY; CpR 1; CpY],
     [6])`;;
let cf248 = new_definition
 `cf248 = ([CpH; CpR 10; CpH; CpR 1; CpY; CpR 8; CpH; CpR 2; CpH; CpR 10; CpY;
     CpR 8; CpH; CpR 1; CpY; CpR 5; CpH; CpR 1; CpH; CpR 1; CpH; CpR 1; CpY;
     CpR 5; CpY; CpR 1; CpY; CpY; CpY; CpR 3; CpY; CpY],
     [31])`;;
let cf249 = new_definition
 `cf249 = ([CpH; CpR 2; CpH; CpR 12; CpY; CpR 3; CpH; CpR 11; CpY; CpR 6; CpH;
     CpR 2; CpH; CpR 10; CpY; CpR 2; CpH; CpR 1; CpY; CpR 3; CpH; CpR 8; CpY;
     CpY; CpR 1; CpY; CpR 3; CpH; CpR 5; CpH; CpR 5; CpY; CpR 3; CpY; CpY;
     CpY],
     [26])`;;
let cf250 = new_definition
 `cf250 = ([CpH; CpR 8; CpH; CpR 1; CpH; CpR 1; CpH; CpR 1; CpY; CpR 3;
            CpH; CpR 10;
     CpY; CpR 3; CpH; CpR 9; CpY; CpR 3; CpH; CpR 8; CpY; CpR 2; CpY; CpR 4;
     CpY; CpR 5; CpH; CpR 1; CpY; CpR 1; CpY; CpY; CpR 2; CpY],
     [20])`;;
let cf251 = new_definition
 `cf251 = ([CpH; CpR 10; CpH; CpR 1; CpY; CpR 9; CpH; CpR 1; CpY;
            CpR 8; CpH; CpR 1;
     CpY; CpR 7; CpH; CpR 1; CpY; CpR 6; CpH; CpR 1; CpY; CpR 3; CpY; CpR 3;
     CpH; CpR 1; CpY; CpH; CpR 4; CpY; CpY; CpR 1; CpY],
     [18])`;;
let cf252 = new_definition
 `cf252 = ([CpH; CpR 11; CpH; CpR 1; CpY; CpR 10; CpH; CpR 1; CpY; CpR 9; CpH;
     CpR 1; CpY; CpR 8; CpH; CpR 1; CpY; CpR 7; CpH; CpR 1; CpY; CpR 7; CpH;
     CpR 7; CpH; CpR 7; CpY; CpR 3; CpY; CpY; CpR 3; CpY; CpR 1; CpY; CpR 1;
     CpY],
     [18])`;;
let cf253 = new_definition
 `cf253 = ([CpH; CpR 3; CpH; CpR 12; CpH; CpR 12; CpY; CpR 9; CpH; CpR 2; CpH;
     CpR 11; CpY; CpR 9; CpH; CpR 1; CpY; CpR 7; CpH; CpR 2; CpH; CpR 9; CpY;
     CpR 8; CpY; CpR 6; CpY; CpY; CpR 5; CpY; CpR 4; CpY; CpY; CpY],
     [33])`;;
let cf254 = new_definition
 `cf254 = ([CpH; CpR 3; CpH; CpR 12; CpH; CpR 12; CpY; CpR 8; CpH; CpR 3; CpH;
     CpR 11; CpH; CpR 11; CpY; CpR 9; CpH; CpR 1; CpY; CpR 8; CpH; CpR 1;
     CpY; CpR 8; CpY; CpR 6; CpY; CpY; CpY; CpR 3; CpY; CpR 1; CpY; CpR 2;
     CpY],
     [11; 12; 33])`;;
let cf255 = new_definition
 `cf255 = ([CpH; CpR 10; CpH; CpR 2; CpH; CpR 12; CpY; CpR 10; CpH; CpR 1; CpY;
     CpR 9; CpH; CpR 1; CpY; CpR 8; CpH; CpR 1; CpY; CpR 7; CpH; CpR 1; CpY;
     CpR 7; CpH; CpR 7; CpY; CpY; CpR 2; CpY; CpR 3; CpY; CpR 3; CpY; CpY],
     [33])`;;
let cf256 = new_definition
 `cf256 = ([CpH; CpR 11; CpH; CpR 1; CpY; CpR 9; CpH; CpR 2; CpH; CpR 11; CpY;
     CpR 9; CpH; CpR 1; CpY; CpR 8; CpH; CpR 1; CpY; CpR 7; CpH; CpR 1; CpY;
     CpR 7; CpH; CpR 7; CpY; CpY; CpY; CpR 2; CpY; CpR 2; CpY; CpR 2; CpY],
     [31])`;;
let cf257 = new_definition
 `cf257 = ([CpH; CpR 10; CpH; CpR 2; CpH; CpR 12; CpY; CpR 10; CpH; CpR 1; CpY;
     CpR 9; CpH; CpR 1; CpY; CpR 8; CpH; CpR 1; CpY; CpR 6; CpH; CpR 1; CpH;
     CpR 1; CpY; CpR 6; CpY; CpR 3; CpY; CpY; CpR 3; CpY; CpR 1; CpY; CpR 1;
     CpY],
     [33])`;;
let cf258 = new_definition
 `cf258 = ([CpH; CpR 3; CpH; CpR 11; CpH; CpR 11; CpY; CpR 9; CpH; CpR 1; CpY;
     CpR 7; CpH; CpR 2; CpH; CpR 9; CpY; CpR 7; CpH; CpR 1; CpY; CpR 7; CpY;
     CpR 5; CpY; CpR 5; CpH; CpR 5; CpY; CpR 2; CpY; CpY; CpR 2; CpY],
     [24])`;;
let cf259 = new_definition
 `cf259 = ([CpH; CpR 2; CpH; CpR 12; CpY; CpR 3; CpH; CpR 11; CpY; CpR 4; CpH;
     CpR 9; CpH; CpR 1; CpY; CpR 3; CpH; CpR 9; CpY; CpR 4; CpH; CpR 8; CpH;
     CpR 8; CpY; CpR 3; CpY; CpR 5; CpY; CpR 1; CpY; CpR 3; CpY; CpY; CpR 1;
     CpY],
     [4; 5; 22; 29])`;;
let cf260 = new_definition
 `cf260 = ([CpH; CpR 3; CpH; CpR 12; CpH; CpR 12; CpY; CpR 10; CpH; CpR 1; CpY;
     CpR 9; CpH; CpR 1; CpY; CpR 8; CpH; CpR 8; CpH; CpR 1; CpY; CpR 8; CpY;
     CpR 6; CpY; CpR 5; CpH; CpR 1; CpY; CpR 1; CpY; CpY; CpR 3; CpY; CpY],
     [31])`;;
let cf261 = new_definition
 `cf261 = ([CpH; CpR 10; CpH; CpR 2; CpH; CpR 12; CpY; CpR 10; CpH; CpR 1; CpY;
     CpR 9; CpH; CpR 1; CpY; CpR 8; CpH; CpR 1; CpY; CpR 7; CpH; CpR 1; CpY;
     CpR 4; CpY; CpR 1; CpY; CpR 2; CpH; CpR 1; CpY; CpR 1; CpY; CpY; CpY],
     [15; 16; 33])`;;
let cf262 = new_definition
 `cf262 = ([CpH; CpR 11; CpH; CpR 1; CpY; CpR 4; CpH; CpR 10; CpH; CpR 1; CpY;
     CpR 3; CpH; CpR 10; CpY; CpR 3; CpH; CpR 2; CpH; CpR 9; CpY; CpR 2; CpY;
     CpR 4; CpY; CpY; CpR 4; CpY; CpR 4; CpH; CpR 1; CpY; CpR 3; CpY; CpR 1;
     CpY],
     [33])`;;
let cf263 = new_definition
 `cf263 = ([CpH; CpR 11; CpH; CpR 1; CpY; CpR 4; CpH; CpR 10; CpH; CpR 1; CpY;
     CpR 3; CpH; CpR 10; CpY; CpR 5; CpH; CpR 7; CpH; CpR 1; CpH; CpR 1; CpY;
     CpR 2; CpY; CpR 4; CpY; CpY; CpR 4; CpY; CpY; CpR 3; CpY; CpR 1; CpY],
     [21; 26; 33])`;;
let cf264 = new_definition
 `cf264 = ([CpH; CpR 2; CpH; CpR 12; CpY; CpR 3; CpH; CpR 11; CpY; CpR 3; CpH;
     CpR 10; CpY; CpR 3; CpH; CpR 9; CpY; CpR 5; CpH; CpR 8; CpH; CpR 8; CpH;
     CpR 8; CpY; CpR 4; CpY; CpY; CpR 4; CpY; CpR 1; CpY; CpR 2; CpY; CpR 1;
     CpY],
     [5; 30])`;;
let cf265 = new_definition
 `cf265 = ([CpH; CpR 4; CpH; CpR 12; CpH; CpR 12; CpH; CpR 12; CpY;
            CpR 10; CpH;
     CpR 1; CpY; CpR 8; CpH; CpR 2; CpH; CpR 10; CpY; CpR 8; CpH; CpR 1; CpY;
     CpR 8; CpY; CpR 5; CpY; CpR 1; CpY; CpY; CpY; CpR 3; CpY; CpY],
     [14; 29; 31])`;;
let cf266 = new_definition
 `cf266 = ([CpH; CpR 11; CpH; CpR 1; CpY; CpR 3; CpH; CpR 11; CpY; CpR 3; CpH;
     CpR 10; CpY; CpR 3; CpH; CpR 9; CpY; CpR 4; CpH; CpR 1; CpY; CpR 4; CpY;
     CpR 3; CpH; CpR 1; CpY; CpR 5; CpH; CpR 1; CpY; CpR 3; CpY; CpR 1; CpY;
     CpR 1; CpY],
     [1; 2; 32])`;;
let cf267 = new_definition
 `cf267 = ([CpH; CpR 9; CpH; CpR 3; CpH; CpR 12; CpH; CpR 12; CpY; CpR 9; CpH;
     CpR 2; CpH; CpR 11; CpY; CpR 9; CpH; CpR 1; CpY; CpR 7; CpH; CpR 1; CpH;
     CpR 1; CpY; CpR 7; CpY; CpY; CpY; CpR 3; CpY; CpR 1; CpY; CpR 1; CpY;
     CpR 2; CpY],
     [35])`;;
let cf268 = new_definition
 `cf268 = ([CpH; CpR 2; CpH; CpR 12; CpY; CpR 5; CpH; CpR 9; CpH;
            CpR 1; CpH; CpR 1;
     CpY; CpR 3; CpH; CpR 10; CpY; CpR 3; CpH; CpR 9; CpY; CpR 3; CpH; CpR 1;
     CpY; CpR 1; CpY; CpR 1; CpY; CpR 5; CpH; CpR 5; CpY; CpR 2; CpY; CpY;
     CpR 2; CpY],
     [32])`;;
let cf269 = new_definition
 `cf269 = ([CpH; CpR 10; CpH; CpR 1; CpH; CpR 1; CpY; CpR 3; CpH; CpR 11; CpY;
     CpR 3; CpH; CpR 10; CpY; CpR 5; CpH; CpR 1; CpY; CpR 3; CpY; CpR 5; CpH;
     CpR 7; CpH; CpR 7; CpH; CpR 7; CpY; CpY; CpR 1; CpY; CpR 3; CpY; CpY;
     CpY],
     [33])`;;
let cf270 = new_definition
 `cf270 = ([CpH; CpR 12; CpH; CpR 1; CpY; CpR 11; CpH; CpR 1; CpY; CpR 9; CpH;
     CpR 10; CpH; CpR 1; CpY; CpR 9; CpH; CpR 1; CpY; CpR 9; CpH; CpR 9; CpH;
     CpR 9; CpY; CpR 7; CpH; CpR 1; CpY; CpR 1; CpY; CpY; CpY; CpR 4; CpY;
     CpY; CpY],
     [33])`;;
let cf271 = new_definition
 `cf271 = ([CpH; CpR 3; CpH; CpR 11; CpH; CpR 1; CpY; CpR 3; CpH; CpR 11; CpY;
     CpR 3; CpH; CpR 3; CpH; CpR 9; CpH; CpR 1; CpY; CpR 3; CpH; CpR 9; CpY;
     CpR 6; CpH; CpR 1; CpY; CpR 1; CpY; CpY; CpR 3; CpY; CpR 1; CpY; CpR 1;
     CpY; CpR 2; CpY],
     [18; 19; 33])`;;
let cf272 = new_definition
 `cf272 = ([CpH; CpR 11; CpH; CpR 1; CpY; CpR 9; CpH; CpR 2; CpH; CpR 11; CpY;
     CpR 9; CpH; CpR 1; CpY; CpR 8; CpH; CpR 1; CpY; CpR 6; CpH; CpR 8; CpY;
     CpR 2; CpH; CpR 7; CpY; CpY; CpY; CpR 2; CpH; CpR 1; CpY; CpR 1; CpY;
     CpY],
     [31])`;;
let cf273 = new_definition
 `cf273 = ([CpH; CpR 9; CpH; CpR 1; CpH; CpR 1; CpH; CpR 1; CpY; CpR 3;
            CpH; CpR 11;
     CpY; CpR 6; CpH; CpR 7; CpH; CpR 1; CpH; CpR 1; CpH; CpR 1; CpY; CpR 2;
     CpY; CpR 4; CpY; CpY; CpR 1; CpY; CpR 1; CpY; CpR 3; CpY; CpY; CpY],
     [8])`;;
let cf274 = new_definition
 `cf274 = ([CpH; CpR 2; CpH; CpR 12; CpY; CpR 4; CpH; CpR 10; CpH; CpR 1; CpY;
     CpR 3; CpH; CpR 10; CpY; CpR 3; CpH; CpR 9; CpY; CpR 4; CpH; CpR 1; CpY;
     CpR 6; CpH; CpR 1; CpH; CpR 1; CpY; CpR 1; CpY; CpR 1; CpY; CpR 3; CpY;
     CpR 1; CpY; CpR 2; CpY],
     [36])`;;
let cf275 = new_definition
 `cf275 = ([CpH; CpR 11; CpH; CpR 1; CpY; CpR 8; CpH; CpR 10; CpH; CpR 1; CpY;
     CpR 8; CpH; CpR 2; CpH; CpR 10; CpY; CpR 9; CpY; CpR 5; CpH; CpR 8; CpY;
     CpY; CpY; CpR 3; CpH; CpR 1; CpY; CpR 4; CpH; CpR 1; CpY; CpR 3; CpY;
     CpR 1; CpY],
     [26])`;;
let cf276 = new_definition
 `cf276 = ([CpH; CpR 11; CpH; CpR 1; CpY; CpR 3; CpH; CpR 11; CpY; CpR 3; CpH;
     CpR 10; CpY; CpR 6; CpH; CpR 1; CpY; CpR 5; CpH; CpR 8; CpY; CpR 4; CpH;
     CpR 7; CpH; CpR 7; CpH; CpR 7; CpY; CpY; CpR 1; CpY; CpR 3; CpY; CpY;
     CpY],
     [6])`;;
let cf277 = new_definition
 `cf277 = ([CpH; CpR 12; CpH; CpR 1; CpY; CpR 11; CpH; CpR 1; CpY; CpR 10; CpH;
     CpR 10; CpH; CpR 1; CpY; CpR 7; CpH; CpR 3; CpH; CpR 10; CpH; CpR 10;
     CpH; CpR 9; CpH; CpR 1; CpY; CpR 8; CpY; CpR 1; CpY; CpR 1; CpY; CpY;
     CpY; CpR 4; CpY; CpY; CpY],
     [36])`;;
let cf278 = new_definition
 `cf278 = ([CpH; CpR 2; CpH; CpR 13; CpY; CpR 3; CpH; CpR 12; CpY; CpR 5; CpH;
     CpR 2; CpH; CpR 11; CpY; CpR 3; CpH; CpR 10; CpH; CpR 2; CpH; CpR 10;
     CpY; CpR 3; CpY; CpY; CpY; CpR 1; CpY; CpR 3; CpH; CpR 5; CpH; CpR 5;
     CpY; CpR 3; CpY; CpY; CpY],
     [30])`;;
let cf279 = new_definition
 `cf279 = ([CpH; CpR 4; CpH; CpR 11; CpH; CpR 1; CpH; CpR 1; CpY; CpR 3; CpH;
     CpR 12; CpY; CpR 3; CpH; CpR 2; CpH; CpR 11; CpY; CpR 2; CpH; CpR 10;
     CpY; CpR 9; CpH; CpR 1; CpY; CpR 1; CpY; CpR 2; CpH; CpR 7; CpY; CpR 2;
     CpY; CpY; CpR 3; CpY; CpY; CpR 2; CpY],
     [40])`;;
let cf280 = new_definition
 `cf280 = ([CpH; CpR 2; CpH; CpR 13; CpY; CpR 3; CpH; CpR 2; CpH; CpR 12; CpY;
     CpR 4; CpH; CpR 10; CpH; CpR 1; CpY; CpR 5; CpH; CpR 1; CpY; CpR 9; CpH;
     CpR 1; CpY; CpR 7; CpH; CpR 1; CpH; CpR 1; CpY; CpR 1; CpY; CpR 1; CpY;
     CpR 4; CpY; CpR 1; CpY; CpR 3; CpY; CpY],
     [39])`;;
let cf281 = new_definition
 `cf281 = ([CpH; CpR 12; CpH; CpR 1; CpY; CpR 11; CpH; CpR 1; CpY; CpR 10; CpH;
     CpR 1; CpY; CpR 9; CpH; CpR 1; CpY; CpR 8; CpH; CpR 1; CpY; CpR 7; CpH;
     CpR 1; CpY; CpR 7; CpH; CpR 7; CpY; CpR 6; CpY; CpR 4; CpY; CpY; CpR 3;
     CpY; CpR 1; CpY],
     [27; 30; 33])`;;
let cf282 = new_definition
 `cf282 = ([CpH; CpR 2; CpH; CpR 13; CpY; CpR 4; CpH; CpR 11; CpH; CpR 1; CpY;
     CpR 3; CpH; CpR 11; CpY; CpR 3; CpH; CpR 10; CpY; CpR 3; CpH; CpR 9;
     CpY; CpR 2; CpH; CpR 8; CpY; CpR 2; CpH; CpR 7; CpY; CpR 5; CpY; CpR 5;
     CpY; CpY; CpR 3; CpY; CpR 1; CpY],
     [21])`;;
let cf283 = new_definition
 `cf283 = ([CpH; CpR 3; CpH; CpR 13; CpH; CpR 13; CpY; CpR 10; CpH; CpR 2; CpH;
     CpR 12; CpY; CpR 9; CpH; CpR 2; CpH; CpR 11; CpY; CpR 8; CpH; CpR 2;
     CpH; CpR 10; CpY; CpR 9; CpY; CpR 7; CpY; CpY; CpR 3; CpY; CpR 2; CpY;
     CpR 2; CpY; CpR 3; CpY; CpR 2; CpY],
     [7])`;;
let cf284 = new_definition
 `cf284 = ([CpH; CpR 10; CpH; CpR 3; CpH; CpR 13; CpH; CpR 13; CpY;
            CpR 11; CpH;
     CpR 1; CpY; CpR 10; CpH; CpR 1; CpY; CpR 9; CpH; CpR 1; CpY; CpR 7; CpH;
     CpR 1; CpH; CpR 1; CpY; CpR 7; CpY; CpY; CpY; CpR 3; CpY; CpR 1; CpY;
     CpR 1; CpY; CpR 2; CpY],
     [36])`;;
let cf285 = new_definition
 `cf285 = ([CpH; CpR 2; CpH; CpR 12; CpY; CpR 4; CpH; CpR 10; CpH; CpR 1; CpY;
     CpR 3; CpH; CpR 10; CpY; CpR 3; CpH; CpR 9; CpY; CpR 4; CpH; CpR 8; CpH;
     CpR 8; CpY; CpR 3; CpY; CpR 1; CpY; CpR 5; CpH; CpR 5; CpY; CpR 2; CpY;
     CpY; CpR 2; CpY],
     [21])`;;
let cf286 = new_definition
 `cf286 = ([CpH; CpR 2; CpH; CpR 13; CpY; CpR 3; CpH; CpR 12; CpY; CpR 4; CpH;
     CpR 10; CpH; CpR 1; CpY; CpR 3; CpH; CpR 10; CpY; CpR 3; CpH; CpR 9;
     CpY; CpR 3; CpH; CpR 1; CpY; CpR 7; CpH; CpR 7; CpY; CpR 3; CpY; CpR 1;
     CpY; CpY; CpY; CpR 2; CpY],
     [31])`;;
let cf287 = new_definition
 `cf287 = ([CpH; CpR 12; CpH; CpR 1; CpY; CpR 9; CpH; CpR 3; CpH; CpR 12; CpH;
     CpR 12; CpY; CpR 10; CpH; CpR 1; CpY; CpR 9; CpH; CpR 1; CpY; CpR 7;
     CpH; CpR 1; CpH; CpR 1; CpY; CpR 7; CpY; CpY; CpY; CpR 3; CpY; CpR 2;
     CpY; CpR 2; CpY; CpR 1; CpY],
     [28; 33; 37])`;;
let cf288 = new_definition
 `cf288 = ([CpH; CpR 3; CpH; CpR 13; CpH; CpR 13; CpY; CpR 11; CpH; CpR 1; CpY;
     CpR 8; CpH; CpR 3; CpH; CpR 11; CpH; CpR 11; CpY; CpR 8; CpH; CpR 2;
     CpH; CpR 10; CpY; CpR 9; CpY; CpR 7; CpY; CpY; CpY; CpR 3; CpY; CpR 2;
     CpY; CpY; CpR 2; CpY],
     [6; 12; 32; 34])`;;
let cf289 = new_definition
 `cf289 = ([CpH; CpR 12; CpH; CpR 1; CpY; CpR 11; CpH; CpR 1; CpY; CpR 10; CpH;
     CpR 1; CpY; CpR 9; CpH; CpR 1; CpY; CpR 7; CpH; CpR 2; CpH; CpR 9; CpY;
     CpR 8; CpH; CpR 8; CpH; CpR 8; CpY; CpR 3; CpY; CpY; CpR 2; CpY; CpR 3;
     CpY; CpY; CpR 1; CpY],
     [37])`;;
let cf290 = new_definition
 `cf290 = ([CpH; CpR 12; CpH; CpR 1; CpY; CpR 11; CpH; CpR 11; CpH; CpR 1; CpY;
     CpR 10; CpH; CpR 1; CpY; CpR 9; CpH; CpR 1; CpY; CpR 8; CpH; CpR 1; CpY;
     CpR 8; CpH; CpR 8; CpY; CpR 7; CpH; CpR 7; CpY; CpR 2; CpY; CpY; CpR 3;
     CpY; CpY; CpY],
     [27])`;;
let cf291 = new_definition
 `cf291 = ([CpH; CpR 11; CpH; CpR 1; CpH; CpR 1; CpY; CpR 4; CpH; CpR 11; CpH;
     CpR 1; CpY; CpR 3; CpH; CpR 11; CpY; CpR 5; CpH; CpR 8; CpH; CpR 1; CpH;
     CpR 1; CpY; CpR 2; CpY; CpR 3; CpY; CpR 2; CpY; CpR 4; CpY; CpY; CpR 3;
     CpY; CpR 1; CpY; CpR 1; CpY],
     [36])`;;
let cf292 = new_definition
 `cf292 = ([CpH; CpR 3; CpH; CpR 13; CpH; CpR 13; CpY; CpR 10; CpH; CpR 2; CpH;
     CpR 12; CpY; CpR 10; CpH; CpR 10; CpH; CpR 1; CpY; CpR 9; CpH; CpR 1;
     CpY; CpR 9; CpY; CpR 7; CpY; CpR 6; CpH; CpR 1; CpY; CpR 1; CpY; CpY;
     CpR 3; CpY; CpR 1; CpY; CpR 2; CpY],
     [18; 19; 37])`;;
let cf293 = new_definition
 `cf293 = ([CpH; CpR 11; CpH; CpR 1; CpH; CpR 1; CpY; CpR 3; CpH; CpR 12; CpY;
     CpR 3; CpH; CpR 11; CpY; CpR 4; CpH; CpR 2; CpH; CpR 10; CpY; CpR 2;
     CpY; CpR 3; CpY; CpR 4; CpH; CpR 7; CpH; CpR 7; CpY; CpY; CpR 1; CpY;
     CpR 3; CpY; CpY; CpY],
     [34])`;;
let cf294 = new_definition
 `cf294 = ([CpH; CpR 11; CpH; CpR 2; CpH; CpR 13; CpY; CpR 10; CpH; CpR 2; CpH;
     CpR 12; CpY; CpR 10; CpH; CpR 1; CpY; CpR 8; CpH; CpR 2; CpH; CpR 10;
     CpY; CpR 8; CpH; CpR 1; CpY; CpR 3; CpY; CpY; CpR 5; CpY; CpY; CpY;
     CpR 3; CpY; CpR 1; CpY],
     [28; 34; 36])`;;
let cf295 = new_definition
 `cf295 = ([CpH; CpR 10; CpH; CpR 1; CpH; CpR 1; CpH; CpR 1; CpY; CpR 3; CpH;
     CpR 12; CpY; CpR 3; CpH; CpR 11; CpY; CpR 5; CpH; CpR 8; CpH; CpR 1;
     CpH; CpR 1; CpY; CpR 2; CpY; CpR 4; CpY; CpY; CpR 5; CpY; CpY; CpR 3;
     CpY; CpR 1; CpY; CpR 1; CpY],
     [33])`;;
let cf296 = new_definition
 `cf296 = ([CpH; CpR 2; CpH; CpR 13; CpY; CpR 3; CpH; CpR 12; CpY; CpR 3; CpH;
     CpR 11; CpY; CpR 4; CpH; CpR 9; CpH; CpR 1; CpY; CpR 2; CpH; CpR 1; CpH;
     CpR 1; CpH; CpR 1; CpY; CpR 6; CpY; CpR 1; CpY; CpR 1; CpY; CpR 3; CpY;
     CpR 3; CpY; CpY; CpR 2; CpY],
     [31])`;;
let cf297 = new_definition
 `cf297 = ([CpH; CpR 2; CpH; CpR 13; CpY; CpR 3; CpH; CpR 12; CpY; CpR 4; CpH;
     CpR 10; CpH; CpR 1; CpY; CpR 3; CpH; CpR 10; CpY; CpR 4; CpH; CpR 8;
     CpH; CpR 1; CpY; CpR 7; CpY; CpR 1; CpY; CpR 1; CpY; CpR 2; CpH; CpR 1;
     CpY; CpR 1; CpY; CpY; CpY],
     [8; 9; 30; 37])`;;
let cf298 = new_definition
 `cf298 = ([CpH; CpR 2; CpH; CpR 13; CpY; CpR 3; CpH; CpR 12; CpY; CpR 5; CpH;
     CpR 9; CpH; CpR 1; CpH; CpR 1; CpY; CpR 3; CpH; CpR 10; CpY; CpR 2; CpH;
     CpR 1; CpH; CpR 1; CpY; CpR 6; CpY; CpR 1; CpY; CpR 1; CpY; CpY; CpY;
     CpR 3; CpY; CpY],
     [26; 33; 35])`;;
let cf299 = new_definition
 `cf299 = ([CpH; CpR 12; CpH; CpR 1; CpY; CpR 11; CpH; CpR 1; CpY; CpR 9; CpH;
     CpR 2; CpH; CpR 11; CpY; CpR 9; CpH; CpR 1; CpY; CpR 8; CpH; CpR 1; CpY;
     CpR 5; CpY; CpR 2; CpH; CpR 7; CpY; CpY; CpY; CpR 2; CpH; CpR 1; CpY;
     CpR 1; CpY; CpY],
     [13; 31; 37])`;;
let cf300 = new_definition
 `cf300 = ([CpH; CpR 2; CpH; CpR 13; CpY; CpR 4; CpH; CpR 11; CpH; CpR 1; CpY;
     CpR 3; CpH; CpR 2; CpH; CpR 11; CpY; CpR 3; CpH; CpR 10; CpY; CpR 2;
     CpH; CpR 1; CpY; CpR 7; CpY; CpR 7; CpH; CpR 7; CpY; CpR 3; CpY; CpY;
     CpY; CpR 3; CpY; CpY],
     [35])`;;
let cf301 = new_definition
 `cf301 = ([CpH; CpR 12; CpH; CpR 1; CpY; CpR 8; CpH; CpR 4; CpH; CpR 12; CpH;
     CpR 12; CpH; CpR 12; CpY; CpR 9; CpH; CpR 2; CpH; CpR 11; CpY; CpR 9;
     CpH; CpR 1; CpY; CpR 9; CpY; CpR 4; CpY; CpY; CpR 4; CpY; CpY; CpR 3;
     CpY; CpR 1; CpY; CpR 1; CpY],
     [17])`;;
let cf302 = new_definition
 `cf302 = ([CpH; CpR 2; CpH; CpR 13; CpY; CpR 3; CpH; CpR 12; CpY; CpR 5; CpH;
     CpR 9; CpH; CpR 1; CpH; CpR 1; CpY; CpR 3; CpH; CpR 10; CpY; CpR 3; CpH;
     CpR 9; CpY; CpR 2; CpH; CpR 8; CpY; CpY; CpR 1; CpY; CpR 3; CpY; CpR 1;
     CpY; CpY; CpR 1; CpY],
     [18; 19; 37])`;;
let cf303 = new_definition
 `cf303 = ([CpH; CpR 12; CpH; CpR 1; CpY; CpR 3; CpH; CpR 12; CpY; CpR 3; CpH;
     CpR 11; CpY; CpR 7; CpH; CpR 6; CpH; CpR 1; CpH; CpR 1; CpH; CpR 1; CpH;
     CpR 1; CpY; CpR 2; CpY; CpR 4; CpY; CpR 1; CpY; CpR 4; CpY; CpY; CpR 3;
     CpY; CpR 1; CpY; CpR 1; CpY],
     [24; 29; 37])`;;
let cf304 = new_definition
 `cf304 = ([CpH; CpR 12; CpH; CpR 1; CpY; CpR 3; CpH; CpR 12; CpY; CpR 3; CpH;
     CpR 11; CpY; CpR 3; CpH; CpR 10; CpY; CpR 3; CpH; CpR 2; CpH; CpR 9;
     CpY; CpR 2; CpY; CpY; CpR 4; CpY; CpR 1; CpH; CpR 5; CpY; CpR 1; CpH;
     CpR 1; CpY; CpR 1; CpY; CpY],
     [32])`;;
let cf305 = new_definition
 `cf305 = ([CpH; CpR 2; CpH; CpR 13; CpY; CpR 3; CpH; CpR 12; CpY; CpR 5; CpH;
     CpR 2; CpH; CpR 11; CpY; CpR 4; CpH; CpR 10; CpH; CpR 10; CpY; CpR 3;
     CpY; CpR 5; CpH; CpR 8; CpH; CpR 8; CpH; CpR 8; CpY; CpY; CpR 1; CpY;
     CpR 4; CpY; CpY; CpY; CpY],
     [37])`;;
let cf306 = new_definition
 `cf306 = ([CpH; CpR 12; CpH; CpR 1; CpY; CpR 8; CpH; CpR 4; CpH; CpR 12; CpH;
     CpR 12; CpH; CpR 12; CpY; CpR 10; CpH; CpR 1; CpY; CpR 9; CpH; CpR 1;
     CpY; CpR 6; CpY; CpY; CpR 2; CpH; CpR 7; CpY; CpY; CpY; CpR 2; CpH;
     CpR 1; CpY; CpR 1; CpY; CpY],
     [35])`;;
let cf307 = new_definition
 `cf307 = ([CpH; CpR 2; CpH; CpR 13; CpY; CpR 4; CpH; CpR 2; CpH; CpR 12; CpY;
     CpR 3; CpH; CpR 11; CpY; CpR 5; CpH; CpR 10; CpH; CpR 10; CpH; CpR 10;
     CpH; CpR 1; CpH; CpR 1; CpY; CpR 2; CpY; CpY; CpY; CpR 1; CpY; CpR 2;
     CpH; CpR 5; CpY; CpR 3; CpY; CpY; CpY],
     [36])`;;
let cf308 = new_definition
 `cf308 = ([CpH; CpR 5; CpH; CpR 13; CpH; CpR 13; CpH; CpR 13; CpH;
            CpR 13; CpY;
     CpR 11; CpH; CpR 1; CpY; CpR 9; CpH; CpR 2; CpH; CpR 11; CpY; CpR 9;
     CpH; CpR 1; CpY; CpR 9; CpY; CpR 7; CpH; CpR 8; CpY; CpY; CpR 1; CpY;
     CpR 4; CpY; CpY; CpY; CpY],
     [7])`;;
let cf309 = new_definition
 `cf309 = ([CpH; CpR 2; CpH; CpR 13; CpY; CpR 3; CpH; CpR 12; CpY; CpR 3; CpH;
     CpR 11; CpY; CpR 3; CpH; CpR 10; CpY; CpR 3; CpH; CpR 9; CpY; CpR 2;
     CpH; CpR 1; CpH; CpR 1; CpH; CpR 8; CpH; CpR 8; CpY; CpY; CpR 1; CpY;
     CpR 3; CpY; CpR 3; CpY; CpY; CpR 2; CpY],
     [30])`;;
let cf310 = new_definition
 `cf310 = ([CpH; CpR 3; CpH; CpR 13; CpH; CpR 13; CpY; CpR 9; CpH; CpR 3; CpH;
     CpR 12; CpH; CpR 12; CpY; CpR 9; CpH; CpR 2; CpH; CpR 11; CpY; CpR 9;
     CpH; CpR 1; CpY; CpR 9; CpY; CpR 6; CpH; CpR 8; CpY; CpR 2; CpY; CpY;
     CpR 4; CpY; CpY; CpY; CpY],
     [7])`;;
let cf311 = new_definition
 `cf311 = ([CpH; CpR 2; CpH; CpR 13; CpY; CpR 3; CpH; CpR 12; CpY; CpR 3; CpH;
     CpR 11; CpY; CpR 3; CpH; CpR 10; CpY; CpR 5; CpH; CpR 7; CpH; CpR 1;
     CpH; CpR 1; CpY; CpH; CpR 8; CpY; CpR 3; CpH; CpR 7; CpY; CpY; CpR 3;
     CpY; CpR 3; CpY; CpY; CpR 2; CpY],
     [34])`;;
let cf312 = new_definition
 `cf312 = ([CpH; CpR 12; CpH; CpR 1; CpY; CpR 3; CpH; CpR 12; CpY; CpR 3; CpH;
     CpR 11; CpY; CpR 5; CpH; CpR 2; CpH; CpR 10; CpY; CpR 2; CpY; CpR 5;
     CpH; CpR 8; CpY; CpR 2; CpH; CpR 1; CpH; CpR 7; CpH; CpR 7; CpY; CpY;
     CpR 1; CpY; CpR 3; CpY; CpY; CpY],
     [31])`;;
let cf313 = new_definition
 `cf313 = ([CpH; CpR 2; CpH; CpR 13; CpY; CpR 3; CpH; CpR 12; CpY; CpR 3; CpH;
     CpR 11; CpY; CpR 3; CpH; CpR 10; CpY; CpR 6; CpH; CpR 1; CpY; CpR 5;
     CpH; CpR 1; CpH; CpR 1; CpH; CpR 1; CpH; CpR 1; CpY; CpR 7; CpH; CpR 7;
     CpY; CpY; CpR 3; CpY; CpY; CpR 3; CpY; CpY],
     [42])`;;
let cf314 = new_definition
 `cf314 = ([CpH; CpR 2; CpH; CpR 13; CpY; CpR 3; CpH; CpR 12; CpY; CpR 5; CpH;
     CpR 9; CpH; CpR 1; CpH; CpR 1; CpY; CpR 3; CpH; CpR 10; CpY; CpR 4; CpH;
     CpR 9; CpH; CpR 9; CpH; CpR 1; CpH; CpR 1; CpY; CpR 1; CpY; CpY; CpR 5;
     CpY; CpY; CpR 3; CpY; CpR 1; CpY; CpR 1; CpY],
     [33])`;;
let cf315 = new_definition
 `cf315 = ([CpH; CpR 12; CpH; CpR 1; CpY; CpR 11; CpH; CpR 1; CpY; CpR 10; CpH;
     CpR 1; CpY; CpR 9; CpH; CpR 1; CpY; CpR 8; CpH; CpR 9; CpH; CpR 9; CpH;
     CpR 9; CpH; CpR 2; CpH; CpR 9; CpY; CpR 3; CpH; CpR 8; CpY; CpY; CpR 6;
     CpY; CpR 4; CpY; CpR 3; CpY; CpR 2; CpY; CpY],
     [42])`;;
let cf316 = new_definition
 `cf316 = ([CpH; CpR 12; CpH; CpR 1; CpY; CpR 3; CpH; CpR 12; CpY; CpR 3; CpH;
     CpR 11; CpY; CpR 7; CpH; CpR 1; CpY; CpR 5; CpH; CpR 9; CpY; CpR 5; CpH;
     CpR 8; CpH; CpR 8; CpH; CpR 8; CpH; CpR 8; CpY; CpR 2; CpH; CpR 1; CpY;
     CpR 2; CpY; CpR 3; CpY; CpR 1; CpY; CpR 2; CpY; CpY],
     [6])`;;
let cf317 = new_definition
 `cf317 = ([CpH; CpR 12; CpH; CpR 1; CpY; CpR 11; CpH; CpR 1; CpY; CpR 10; CpH;
     CpR 1; CpY; CpR 9; CpH; CpR 1; CpY; CpR 5; CpH; CpR 1; CpH; CpR 1; CpH;
     CpR 1; CpH; CpR 1; CpH; CpR 9; CpH; CpR 9; CpY; CpR 8; CpH; CpR 1; CpY;
     CpR 1; CpY; CpR 2; CpY; CpR 4; CpY; CpY; CpR 3; CpY; CpR 2; CpY],
     [46])`;;
let cf318 = new_definition
 `cf318 = ([CpH; CpR 3; CpH; CpR 13; CpH; CpR 13; CpY; CpR 10; CpH; CpR 2; CpH;
     CpR 12; CpY; CpR 10; CpH; CpR 1; CpY; CpR 7; CpH; CpR 3; CpH; CpR 10;
     CpH; CpR 10; CpY; CpR 9; CpY; CpR 7; CpY; CpY; CpR 6; CpY; CpR 4; CpY;
     CpR 1; CpY; CpR 2; CpY; CpR 1; CpY],
     [37])`;;
let cf319 = new_definition
 `cf319 = ([CpH; CpR 12; CpH; CpR 1; CpY; CpR 11; CpH; CpR 1; CpY; CpR 10; CpH;
     CpR 10; CpH; CpR 1; CpY; CpR 9; CpH; CpR 1; CpY; CpR 8; CpH; CpR 1; CpY;
     CpR 8; CpH; CpR 8; CpY; CpR 6; CpH; CpR 1; CpY; CpR 1; CpY; CpY; CpR 2;
     CpY; CpR 2; CpY; CpR 2; CpY],
     [35])`;;
let cf320 = new_definition
 `cf320 = ([CpH; CpR 4; CpH; CpR 13; CpH; CpR 13; CpH; CpR 13; CpY;
            CpR 11; CpH;
     CpR 1; CpY; CpR 9; CpH; CpR 2; CpH; CpR 11; CpY; CpR 8; CpH; CpR 2; CpH;
     CpR 10; CpY; CpR 9; CpY; CpR 6; CpY; CpR 1; CpY; CpY; CpY; CpR 3; CpY;
     CpR 1; CpY; CpR 2; CpY],
     [14; 32; 34])`;;
let cf321 = new_definition
 `cf321 = ([CpH; CpR 2; CpH; CpR 13; CpY; CpR 11; CpH; CpR 1; CpY; CpR 10; CpH;
     CpR 1; CpY; CpR 8; CpH; CpR 8; CpH; CpR 2; CpH; CpR 10; CpY; CpR 9; CpY;
     CpR 5; CpH; CpR 1; CpY; CpR 7; CpH; CpR 1; CpY; CpR 1; CpY; CpY; CpR 3;
     CpY; CpR 1; CpY; CpR 2; CpY],
     [1; 2; 35])`;;
let cf322 = new_definition
 `cf322 = ([CpH; CpR 12; CpH; CpR 1; CpY; CpR 11; CpH; CpR 1; CpY; CpR 10; CpH;
     CpR 1; CpY; CpR 9; CpH; CpR 1; CpY; CpR 8; CpH; CpR 1; CpY; CpR 8; CpH;
     CpR 8; CpH; CpR 8; CpH; CpR 8; CpY; CpR 2; CpH; CpR 1; CpY; CpR 1; CpY;
     CpY; CpR 3; CpY; CpR 1; CpY; CpR 1; CpY],
     [32])`;;
let cf323 = new_definition
 `cf323 = ([CpH; CpR 12; CpH; CpR 1; CpY; CpR 9; CpH; CpR 3; CpH; CpR 12; CpH;
     CpR 12; CpY; CpR 10; CpH; CpR 1; CpY; CpR 9; CpH; CpR 1; CpY; CpR 8;
     CpH; CpR 1; CpY; CpR 8; CpH; CpR 8; CpY; CpR 7; CpH; CpR 7; CpY; CpR 2;
     CpY; CpY; CpR 3; CpY; CpY; CpY],
     [30])`;;
let cf324 = new_definition
 `cf324 = ([CpH; CpR 2; CpH; CpR 8; CpY; CpR 6; CpH; CpR 1; CpY;
            CpR 6; CpH; CpR 6;
     CpH; CpR 6; CpH; CpR 6; CpY; CpR 4; CpY; CpY; CpY; CpY],
     [6])`;;
let cf325 = new_definition
 `cf325 = ([CpH; CpR 7; CpH; CpR 2; CpH; CpR 9; CpY; CpR 7; CpH;
            CpR 6; CpH; CpR 2;
     CpH; CpR 8; CpY; CpR 7; CpH; CpR 7; CpY; CpY; CpY; CpY; CpY; CpY],
     [21])`;;
let cf326 = new_definition
 `cf326 = ([CpH; CpR 4; CpH; CpR 7; CpH; CpR 1; CpH; CpR 1; CpY;
            CpR 4; CpH; CpR 1;
     CpH; CpR 1; CpH; CpR 1; CpY; CpR 1; CpY; CpR 1; CpY; CpR 1; CpY; CpR 2;
     CpH; CpR 4; CpY; CpR 2; CpY; CpR 1; CpY],
     [29])`;;
let cf327 = new_definition
 `cf327 = ([CpH; CpR 8; CpH; CpR 1; CpY; CpR 3; CpH; CpR 8; CpY;
            CpR 5; CpH; CpR 5;
     CpH; CpR 1; CpH; CpR 1; CpY; CpR 2; CpY; CpR 3; CpY; CpR 1; CpY; CpR 1;
     CpY; CpR 2; CpY],
     [23])`;;
let cf328 = new_definition
 `cf328 = ([CpH; CpR 8; CpH; CpR 1; CpY; CpR 3; CpH; CpR 8; CpY;
            CpR 4; CpH; CpR 6;
     CpH; CpR 1; CpY; CpR 2; CpH; CpR 1; CpY; CpR 3; CpY; CpR 1; CpY; CpR 3;
     CpY; CpY],
     [0; 23])`;;
let cf329 = new_definition
 `cf329 = ([CpH; CpR 2; CpH; CpR 9; CpY; CpR 7; CpH; CpR 1; CpY;
            CpR 4; CpH; CpR 7;
     CpY; CpR 4; CpH; CpR 1; CpY; CpR 5; CpH; CpR 1; CpY; CpR 4; CpH; CpR 1;
     CpY; CpR 3; CpY; CpR 1; CpY],
     [6])`;;
let cf330 = new_definition
 `cf330 = ([CpH; CpR 3; CpH; CpR 9; CpH; CpR 1; CpY; CpR 3; CpH;
            CpR 2; CpH; CpR 9;
     CpY; CpR 3; CpH; CpR 8; CpY; CpR 2; CpH; CpR 1; CpY; CpR 1; CpY; CpR 1;
     CpY; CpR 1; CpY; CpR 1; CpY; CpR 2; CpY],
     [14; 15; 21; 26])`;;
let cf331 = new_definition
 `cf331 = ([CpH; CpR 2; CpH; CpR 10; CpY; CpR 4; CpH; CpR 4; CpH;
            CpR 7; CpH; CpR 1;
     CpH; CpR 1; CpY; CpR 5; CpH; CpR 1; CpH; CpR 1; CpY; CpR 1; CpY; CpR 1;
     CpY; CpR 1; CpY; CpR 1; CpY; CpR 2; CpY; CpR 1; CpY],
     [30])`;;
let cf332 = new_definition
 `cf332 = ([CpH; CpR 9; CpH; CpR 1; CpY; CpR 7; CpH; CpR 2; CpH;
            CpR 9; CpY; CpR 6;
     CpH; CpR 1; CpH; CpR 7; CpH; CpR 1; CpY; CpR 7; CpH; CpR 1; CpY; CpR 1;
     CpY; CpR 1; CpY; CpR 1; CpY; CpR 1; CpY; CpR 2; CpY],
     [30])`;;
let cf333 = new_definition
 `cf333 = ([CpH; CpR 9; CpH; CpR 1; CpY; CpR 7; CpH; CpR 1; CpH;
            CpR 8; CpH; CpR 1;
     CpY; CpR 7; CpH; CpR 1; CpH; CpR 1; CpY; CpR 1; CpY; CpR 1; CpY; CpR 4;
     CpH; CpR 1; CpY; CpR 4; CpH; CpR 1; CpY; CpR 3; CpY; CpR 1; CpY],
     [25])`;;
let cf334 = new_definition
 `cf334 = ([CpH; CpR 9; CpH; CpR 1; CpY; CpR 3; CpH; CpR 9; CpY;
            CpR 3; CpH; CpR 8;
     CpY; CpR 4; CpH; CpR 6; CpH; CpR 1; CpY; CpR 2; CpY; CpR 3; CpY; CpR 1;
     CpY; CpR 1; CpY; CpR 2; CpY],
     [24])`;;
let cf335 = new_definition
 `cf335 = ([CpH; CpR 2; CpH; CpR 10; CpY; CpR 8; CpH; CpR 1; CpY;
            CpR 4; CpH; CpR 4;
     CpH; CpR 8; CpH; CpR 8; CpH; CpR 8; CpY; CpR 7; CpY; CpR 5; CpY; CpY;
     CpY; CpR 3; CpY; CpR 1; CpY],
     [6])`;;
let cf336 = new_definition
 `cf336 = ([CpH; CpR 9; CpH; CpR 1; CpY; CpR 7; CpH; CpR 2; CpH;
            CpR 9; CpY; CpR 6;
     CpH; CpR 2; CpH; CpR 8; CpY; CpR 6; CpH; CpR 1; CpY; CpR 5; CpY; CpY;
     CpR 3; CpY; CpY; CpR 2; CpY],
     [18])`;;
let cf337 = new_definition
 `cf337 = ([CpH; CpR 2; CpH; CpR 10; CpY; CpR 8; CpH; CpR 1; CpY;
            CpR 6; CpH; CpR 2;
     CpH; CpR 8; CpY; CpR 6; CpH; CpR 7; CpY; CpR 5; CpY; CpY; CpR 4; CpH;
     CpR 4; CpY; CpR 2; CpY; CpY],
     [6])`;;
let cf338 = new_definition
 `cf338 = ([CpH; CpR 2; CpH; CpR 10; CpY; CpR 8; CpH; CpR 1; CpY;
            CpR 5; CpH; CpR 3;
     CpH; CpR 8; CpH; CpR 8; CpY; CpR 7; CpH; CpR 7; CpY; CpR 5; CpY; CpY;
     CpR 2; CpY; CpR 2; CpY; CpR 1; CpY],
     [27])`;;
let cf339 = new_definition
 `cf339 = ([CpH; CpR 2; CpH; CpR 10; CpY; CpR 4; CpH; CpR 8; CpH;
            CpR 1; CpY; CpR 3;
     CpH; CpR 2; CpH; CpR 8; CpY; CpR 2; CpY; CpR 5; CpH; CpR 1; CpY; CpR 5;
     CpY; CpR 1; CpY; CpR 2; CpY; CpR 2; CpY],
     [12])`;;
let cf340 = new_definition
 `cf340 = ([CpH; CpR 2; CpH; CpR 10; CpY; CpR 8; CpH; CpR 1; CpY;
            CpR 7; CpH; CpR 1;
     CpY; CpR 5; CpH; CpR 7; CpY; CpR 5; CpY; CpR 5; CpH; CpR 1; CpY; CpR 4;
     CpH; CpR 1; CpY; CpR 3; CpY; CpR 1; CpY],
     [6])`;;
let cf341 = new_definition
 `cf341 = ([CpH; CpR 8; CpH; CpR 1; CpH; CpR 1; CpY; CpR 3; CpH;
            CpR 9; CpY; CpR 5;
     CpH; CpR 6; CpH; CpR 1; CpH; CpR 1; CpY; CpR 2; CpY; CpR 3; CpY; CpR 1;
     CpY; CpR 1; CpY; CpR 1; CpY; CpR 2; CpY],
     [26])`;;
let cf342 = new_definition
 `cf342 = ([CpH; CpR 9; CpH; CpR 1; CpY; CpR 8; CpH; CpR 1; CpY;
            CpR 7; CpH; CpR 1;
     CpY; CpR 6; CpH; CpR 6; CpH; CpR 1; CpY; CpR 5; CpY; CpR 4; CpH; CpR 5;
     CpY; CpY; CpR 1; CpY; CpR 2; CpY],
     [12; 13; 28])`;;
let cf343 = new_definition
 `cf343 = ([CpH; CpR 2; CpH; CpR 11; CpY; CpR 3; CpH; CpR 10; CpY; CpR 3; CpH;
     CpR 4; CpH; CpR 7; CpH; CpR 1; CpH; CpR 1; CpY; CpR 6; CpH; CpR 1; CpY;
     CpR 1; CpY; CpR 1; CpY; CpR 1; CpY; CpR 1; CpY; CpR 2; CpY; CpR 1; CpY],
     [1; 2; 8; 9])`;;
let cf344 = new_definition
 `cf344 = ([CpH; CpR 2; CpH; CpR 9; CpY; CpR 7; CpH; CpR 1; CpY;
            CpR 4; CpH; CpR 7;
     CpY; CpR 4; CpH; CpR 1; CpY; CpR 4; CpH; CpR 1; CpH; CpR 1; CpY; CpH;
     CpR 4; CpY; CpY; CpR 1; CpY],
     [6])`;;
let cf345 = new_definition
 `cf345 = ([CpH; CpR 10; CpH; CpR 1; CpY; CpR 9; CpH; CpR 9; CpH;
            CpR 1; CpY; CpR 7;
     CpH; CpR 2; CpH; CpR 9; CpY; CpR 4; CpH; CpR 8; CpY; CpY; CpY; CpY;
     CpR 4; CpH; CpR 1; CpY; CpR 3; CpY; CpR 1; CpY],
     [25])`;;
let cf346 = new_definition
 `cf346 = ([CpH; CpR 2; CpH; CpR 11; CpY; CpR 4; CpH; CpR 2; CpH; CpR 10; CpY;
     CpR 4; CpH; CpR 8; CpH; CpR 1; CpY; CpR 5; CpH; CpR 1; CpH; CpR 1; CpY;
     CpR 1; CpY; CpR 1; CpY; CpR 1; CpY; CpR 1; CpY; CpR 2; CpY; CpR 1; CpY],
     [28])`;;
let cf347 = new_definition
 `cf347 = ([CpH; CpR 2; CpH; CpR 11; CpY; CpR 3; CpH; CpR 10; CpY; CpR 3; CpH;
     CpR 3; CpH; CpR 8; CpH; CpR 1; CpY; CpR 2; CpH; CpR 1; CpH; CpR 1; CpY;
     CpR 1; CpY; CpR 1; CpY; CpR 1; CpY; CpR 1; CpY; CpR 2; CpY; CpR 1; CpY],
     [4; 5; 24; 29])`;;
let cf348 = new_definition
 `cf348 = ([CpH; CpR 4; CpH; CpR 9; CpH; CpR 1; CpH; CpR 1; CpY;
            CpR 3; CpH; CpR 2;
     CpH; CpR 10; CpY; CpR 3; CpH; CpR 9; CpY; CpR 7; CpH; CpR 8; CpY; CpY;
     CpY; CpY; CpR 4; CpH; CpR 1; CpY; CpR 3; CpY; CpR 1; CpY],
     [25])`;;
let cf349 = new_definition
 `cf349 = ([CpH; CpR 8; CpH; CpR 2; CpH; CpR 10; CpY; CpR 8; CpH;
            CpR 6; CpH; CpR 3;
     CpH; CpR 9; CpH; CpR 9; CpY; CpR 8; CpH; CpR 8; CpY; CpY; CpY; CpY;
     CpR 4; CpH; CpR 4; CpY; CpR 2; CpY; CpY],
     [24])`;;
let cf350 = new_definition
 `cf350 = ([CpH; CpR 8; CpH; CpR 2; CpH; CpR 10; CpY; CpR 6; CpH;
            CpR 8; CpH; CpR 1;
     CpY; CpR 8; CpH; CpR 8; CpY; CpY; CpY; CpR 4; CpH; CpR 1; CpH; CpR 1;
     CpY; CpH; CpR 4; CpY; CpY; CpR 1; CpY],
     [18])`;;
let cf351 = new_definition
 `cf351 = ([CpH; CpR 2; CpH; CpR 11; CpY; CpR 3; CpH; CpR 2; CpH; CpR 10; CpY;
     CpR 4; CpH; CpR 1; CpH; CpR 7; CpH; CpR 1; CpH; CpR 1; CpY; CpR 2; CpH;
     CpR 8; CpY; CpR 2; CpY; CpY; CpR 1; CpY; CpR 1; CpY; CpR 2; CpY; CpR 1;
     CpY],
     [34])`;;
let cf352 = new_definition
 `cf352 = ([CpH; CpR 10; CpH; CpR 1; CpY; CpR 8; CpH; CpR 9; CpH;
            CpR 1; CpY; CpR 8;
     CpH; CpR 9; CpH; CpR 2; CpH; CpR 9; CpY; CpR 8; CpH; CpR 1; CpY; CpR 7;
     CpY; CpR 1; CpY; CpY; CpR 4; CpH; CpR 1; CpY; CpR 3; CpY; CpR 1; CpY],
     [21])`;;
let cf353 = new_definition
 `cf353 = ([CpH; CpR 10; CpH; CpR 1; CpY; CpR 9; CpH; CpR 9; CpH;
            CpR 1; CpY; CpR 7;
     CpH; CpR 1; CpH; CpR 8; CpH; CpR 1; CpY; CpR 8; CpH; CpR 1; CpY; CpR 1;
     CpY; CpR 1; CpY; CpR 5; CpY; CpR 4; CpH; CpR 4; CpY; CpR 2; CpY; CpY],
     [29])`;;
let cf354 = new_definition
 `cf354 = ([CpH; CpR 10; CpH; CpR 1; CpY; CpR 8; CpH; CpR 2; CpH; CpR 10; CpY;
     CpR 6; CpH; CpR 1; CpH; CpR 8; CpH; CpR 1; CpY; CpR 8; CpH; CpR 1; CpY;
     CpR 1; CpY; CpR 2; CpH; CpR 6; CpY; CpR 5; CpY; CpR 3; CpY; CpY; CpR 2;
     CpY],
     [11])`;;
let cf355 = new_definition
 `cf355 = ([CpH; CpR 9; CpH; CpR 1; CpY; CpR 7; CpH; CpR 1; CpH;
            CpR 8; CpH; CpR 1;
     CpY; CpR 7; CpH; CpR 1; CpH; CpR 1; CpY; CpR 1; CpY; CpR 1; CpY; CpR 3;
     CpH; CpR 1; CpH; CpR 1; CpY; CpH; CpR 4; CpY; CpY; CpR 1; CpY],
     [25])`;;
let cf356 = new_definition
 `cf356 = ([CpH; CpR 3; CpH; CpR 11; CpH; CpR 11; CpY; CpR 9; CpH; CpR 1; CpY;
     CpR 7; CpH; CpR 2; CpH; CpR 9; CpY; CpR 7; CpH; CpR 1; CpY; CpR 7; CpY;
     CpR 5; CpY; CpY; CpY; CpR 2; CpY; CpR 2; CpY],
     [27])`;;
let cf357 = new_definition
 `cf357 = ([CpH; CpR 10; CpH; CpR 1; CpY; CpR 9; CpH; CpR 1; CpY;
            CpR 8; CpH; CpR 1;
     CpY; CpR 6; CpH; CpR 2; CpH; CpR 8; CpY; CpR 6; CpH; CpR 1; CpY; CpR 5;
     CpY; CpR 3; CpY; CpY; CpR 3; CpY; CpY],
     [12; 13; 29])`;;
let cf358 = new_definition
 `cf358 = ([CpH; CpR 2; CpH; CpR 11; CpY; CpR 9; CpH; CpR 1; CpY;
            CpR 8; CpH; CpR 1;
     CpY; CpR 7; CpH; CpR 1; CpY; CpR 6; CpH; CpR 7; CpY; CpR 5; CpY; CpR 4;
     CpH; CpR 5; CpY; CpR 3; CpY; CpY; CpY],
     [16; 17; 28])`;;
let cf359 = new_definition
 `cf359 = ([CpH; CpR 2; CpH; CpR 11; CpY; CpR 9; CpH; CpR 1; CpY;
            CpR 8; CpH; CpR 1;
     CpY; CpR 6; CpH; CpR 2; CpH; CpR 8; CpY; CpR 7; CpH; CpR 7; CpY; CpR 5;
     CpY; CpR 2; CpY; CpR 2; CpY; CpR 2; CpY; CpY],
     [19])`;;
let cf360 = new_definition
 `cf360 = ([CpH; CpR 2; CpH; CpR 11; CpY; CpR 9; CpH; CpR 1; CpY;
            CpR 6; CpH; CpR 8;
     CpH; CpR 1; CpY; CpR 8; CpY; CpR 5; CpH; CpR 1; CpY; CpR 6; CpH; CpR 1;
     CpY; CpR 5; CpH; CpR 1; CpY; CpR 4; CpY; CpY; CpR 1; CpY],
     [6])`;;
let cf361 = new_definition
 `cf361 = ([CpH; CpR 10; CpH; CpR 1; CpY; CpR 6; CpH; CpR 4; CpH; CpR 10; CpH;
     CpR 10; CpH; CpR 10; CpY; CpR 8; CpH; CpR 1; CpY; CpR 7; CpH; CpR 1;
     CpY; CpR 6; CpY; CpY; CpY; CpR 3; CpY; CpR 1; CpY; CpR 1; CpY],
     [26])`;;
let cf362 = new_definition
 `cf362 = ([CpH; CpR 2; CpH; CpR 11; CpY; CpR 9; CpH; CpR 1; CpY;
            CpR 7; CpH; CpR 2;
     CpH; CpR 9; CpY; CpR 7; CpH; CpR 8; CpH; CpR 8; CpY; CpR 6; CpY; CpY;
     CpR 5; CpH; CpR 5; CpY; CpY; CpR 2; CpY; CpY],
     [28])`;;
let cf363 = new_definition
 `cf363 = ([CpH; CpR 2; CpH; CpR 10; CpY; CpR 8; CpH; CpR 1; CpY;
            CpR 4; CpH; CpR 4;
     CpH; CpR 8; CpH; CpR 8; CpH; CpR 8; CpY; CpR 7; CpY; CpR 5; CpY; CpY;
     CpR 4; CpH; CpR 1; CpY; CpR 3; CpY; CpR 1; CpY],
     [6])`;;
let cf364 = new_definition
 `cf364 = ([CpH; CpR 2; CpH; CpR 11; CpY; CpR 9; CpH; CpR 1; CpY;
            CpR 6; CpH; CpR 3;
     CpH; CpR 9; CpH; CpR 9; CpY; CpR 7; CpH; CpR 8; CpY; CpR 6; CpY; CpY;
     CpR 4; CpH; CpR 1; CpY; CpR 4; CpY; CpR 2; CpY; CpY],
     [6])`;;
let cf365 = new_definition
 `cf365 = ([CpH; CpR 2; CpH; CpR 11; CpY; CpR 9; CpH; CpR 1; CpY;
            CpR 8; CpH; CpR 6;
     CpH; CpR 3; CpH; CpR 9; CpH; CpR 9; CpY; CpR 8; CpY; CpR 5; CpH; CpR 1;
     CpY; CpR 6; CpY; CpR 1; CpY; CpR 3; CpY; CpR 2; CpY; CpY],
     [21])`;;
let cf366 = new_definition
 `cf366 = ([CpH; CpR 3; CpH; CpR 11; CpH; CpR 11; CpY; CpR 9; CpH; CpR 1; CpY;
     CpR 5; CpH; CpR 4; CpH; CpR 9; CpH; CpR 9; CpH; CpR 9; CpY; CpR 8; CpY;
     CpR 6; CpY; CpY; CpY; CpY; CpR 3; CpY; CpR 1; CpY],
     [29])`;;
let cf367 = new_definition
 `cf367 = ([CpH; CpR 10; CpH; CpR 1; CpY; CpR 7; CpH; CpR 3; CpH; CpR 10; CpH;
     CpR 10; CpY; CpR 8; CpH; CpR 1; CpY; CpR 7; CpH; CpR 1; CpY; CpR 7; CpH;
     CpR 7; CpY; CpY; CpY; CpY; CpR 2; CpY; CpR 2; CpY],
     [32])`;;
let cf368 = new_definition
 `cf368 = ([CpH; CpR 2; CpH; CpR 10; CpY; CpR 8; CpH; CpR 1; CpY;
            CpR 7; CpH; CpR 1;
     CpY; CpR 5; CpH; CpR 7; CpY; CpR 5; CpY; CpR 4; CpH; CpR 1; CpH; CpR 1;
     CpY; CpH; CpR 4; CpY; CpY; CpR 1; CpY],
     [6])`;;
let cf369 = new_definition
 `cf369 = ([CpH; CpR 2; CpH; CpR 11; CpY; CpR 9; CpH; CpR 1; CpY;
            CpR 8; CpH; CpR 1;
     CpY; CpR 5; CpH; CpR 8; CpY; CpR 6; CpY; CpR 5; CpH; CpR 1; CpH; CpR 5;
     CpH; CpR 1; CpY; CpR 2; CpY; CpY; CpR 3; CpY; CpR 1; CpY],
     [31])`;;
let cf370 = new_definition
 `cf370 = ([CpH; CpR 2; CpH; CpR 11; CpY; CpR 9; CpH; CpR 1; CpY;
            CpR 7; CpH; CpR 2;
     CpH; CpR 9; CpY; CpR 6; CpH; CpR 8; CpY; CpR 6; CpY; CpR 4; CpH; CpR 1;
     CpH; CpR 1; CpY; CpR 1; CpY; CpY; CpR 3; CpY; CpR 1; CpY],
     [6])`;;
let cf371 = new_definition
 `cf371 = ([CpH; CpR 10; CpH; CpR 1; CpY; CpR 9; CpH; CpR 1; CpY;
            CpR 8; CpH; CpR 6;
     CpH; CpR 3; CpH; CpR 9; CpH; CpR 9; CpY; CpR 8; CpH; CpR 8; CpY; CpY;
     CpY; CpY; CpR 4; CpH; CpR 4; CpY; CpR 2; CpY; CpY],
     [4; 5; 24; 29])`;;
let cf372 = new_definition
 `cf372 = ([CpH; CpR 10; CpH; CpR 1; CpY; CpR 9; CpH; CpR 1; CpY;
            CpR 6; CpH; CpR 8;
     CpH; CpR 1; CpY; CpR 8; CpH; CpR 8; CpY; CpY; CpY; CpR 4; CpH; CpR 1;
     CpH; CpR 1; CpY; CpH; CpR 4; CpY; CpY; CpR 1; CpY],
     [4; 5; 18; 23])`;;
let cf373 = new_definition
 `cf373 = ([CpH; CpR 2; CpH; CpR 12; CpY; CpR 3; CpH; CpR 2; CpH; CpR 11; CpY;
     CpR 3; CpH; CpR 2; CpH; CpR 10; CpY; CpR 2; CpH; CpR 1; CpH; CpR 1; CpY;
     CpR 2; CpH; CpR 1; CpY; CpR 7; CpY; CpR 1; CpY; CpR 1; CpY; CpR 1; CpY;
     CpR 2; CpY; CpR 1; CpY],
     [33])`;;
let cf374 = new_definition
 `cf374 = ([CpH; CpR 11; CpH; CpR 1; CpY; CpR 10; CpH; CpR 10; CpH; CpR 1; CpY;
     CpR 8; CpH; CpR 9; CpH; CpR 1; CpY; CpR 9; CpH; CpR 9; CpY; CpR 8; CpH;
     CpR 8; CpY; CpR 2; CpY; CpY; CpY; CpR 4; CpH; CpR 1; CpY; CpR 3; CpY;
     CpR 1; CpY],
     [30])`;;
let cf375 = new_definition
 `cf375 = ([CpH; CpR 2; CpH; CpR 11; CpY; CpR 3; CpH; CpR 2; CpH; CpR 10; CpY;
     CpR 4; CpH; CpR 2; CpH; CpR 6; CpH; CpR 1; CpH; CpR 2; CpH; CpR 9; CpY;
     CpR 1; CpH; CpR 1; CpY; CpR 1; CpY; CpY; CpR 1; CpY; CpR 1; CpY; CpR 2;
     CpY; CpR 1; CpY],
     [37])`;;
let cf376 = new_definition
 `cf376 = ([CpH; CpR 10; CpH; CpR 1; CpY; CpR 8; CpH; CpR 9; CpH;
            CpR 1; CpY; CpR 8;
     CpH; CpR 8; CpH; CpR 3; CpH; CpR 8; CpH; CpR 1; CpY; CpH; CpR 8; CpY;
     CpY; CpR 1; CpY; CpY; CpR 4; CpH; CpR 1; CpY; CpR 3; CpY; CpR 1; CpY],
     [21])`;;
let cf377 = new_definition
 `cf377 = ([CpH; CpR 2; CpH; CpR 12; CpY; CpR 10; CpH; CpR 1; CpY; CpR 8; CpH;
     CpR 2; CpH; CpR 10; CpY; CpR 8; CpH; CpR 8; CpH; CpR 1; CpY; CpR 8; CpY;
     CpR 6; CpY; CpY; CpR 5; CpH; CpR 5; CpY; CpR 2; CpY; CpR 3; CpY; CpR 1;
     CpY],
     [29])`;;
let cf378 = new_definition
 `cf378 = ([CpH; CpR 11; CpH; CpR 1; CpY; CpR 9; CpH; CpR 2; CpH; CpR 11; CpY;
     CpR 8; CpH; CpR 2; CpH; CpR 10; CpY; CpR 8; CpH; CpR 1; CpY; CpR 7; CpH;
     CpR 1; CpY; CpR 6; CpY; CpY; CpR 3; CpY; CpR 3; CpY; CpR 3; CpY; CpR 1;
     CpY],
     [18])`;;
let cf379 = new_definition
 `cf379 = ([CpH; CpR 11; CpH; CpR 1; CpY; CpR 10; CpH; CpR 1; CpY; CpR 7; CpH;
     CpR 3; CpH; CpR 10; CpH; CpR 10; CpY; CpR 8; CpH; CpR 1; CpY; CpR 7;
     CpH; CpR 1; CpY; CpR 6; CpY; CpY; CpY; CpR 3; CpY; CpR 1; CpY; CpR 1;
     CpY],
     [30])`;;
let cf380 = new_definition
 `cf380 = ([CpH; CpR 3; CpH; CpR 12; CpH; CpR 12; CpY; CpR 10; CpH; CpR 1; CpY;
     CpR 8; CpH; CpR 2; CpH; CpR 10; CpY; CpR 7; CpH; CpR 2; CpH; CpR 9; CpY;
     CpR 8; CpY; CpR 6; CpY; CpY; CpY; CpR 3; CpY; CpR 2; CpY; CpY],
     [30; 33])`;;
let cf381 = new_definition
 `cf381 = ([CpH; CpR 3; CpH; CpR 12; CpH; CpR 12; CpY; CpR 10; CpH; CpR 1; CpY;
     CpR 9; CpH; CpR 1; CpY; CpR 6; CpH; CpR 3; CpH; CpR 9; CpH; CpR 9; CpY;
     CpR 8; CpY; CpR 6; CpY; CpY; CpY; CpY; CpR 3; CpY; CpR 1; CpY],
     [31])`;;
let cf382 = new_definition
 `cf382 = ([CpH; CpR 2; CpH; CpR 12; CpY; CpR 10; CpH; CpR 1; CpY; CpR 8; CpH;
     CpR 2; CpH; CpR 10; CpY; CpR 6; CpH; CpR 3; CpH; CpR 9; CpH; CpR 9; CpY;
     CpR 8; CpY; CpR 6; CpY; CpR 6; CpY; CpR 4; CpY; CpR 3; CpY; CpY; CpY],
     [25])`;;
let cf383 = new_definition
 `cf383 = ([CpH; CpR 10; CpH; CpR 1; CpY; CpR 9; CpH; CpR 1; CpY;
            CpR 8; CpH; CpR 1;
     CpY; CpR 7; CpH; CpR 1; CpY; CpR 7; CpH; CpR 1; CpY; CpR 5; CpH; CpR 1;
     CpH; CpR 1; CpY; CpH; CpR 5; CpY; CpY; CpY; CpR 1; CpY],
     [14])`;;
let cf384 = new_definition
 `cf384 = ([CpH; CpR 11; CpH; CpR 1; CpY; CpR 7; CpH; CpR 4; CpH; CpR 11; CpH;
     CpR 11; CpH; CpR 11; CpY; CpR 9; CpH; CpR 1; CpY; CpR 8; CpH; CpR 1;
     CpY; CpR 6; CpY; CpY; CpY; CpR 2; CpH; CpR 1; CpY; CpR 1; CpY; CpR 1;
     CpY; CpR 1; CpY],
     [33])`;;
let cf385 = new_definition
 `cf385 = ([CpH; CpR 11; CpH; CpR 1; CpY; CpR 7; CpH; CpR 4; CpH; CpR 11; CpH;
     CpR 11; CpH; CpR 11; CpY; CpR 9; CpH; CpR 1; CpY; CpR 7; CpH; CpR 1;
     CpH; CpR 1; CpY; CpR 7; CpY; CpY; CpY; CpY; CpR 3; CpY; CpR 1; CpY;
     CpR 1; CpY],
     [32])`;;
let cf386 = new_definition
 `cf386 = ([CpH; CpR 11; CpH; CpR 1; CpY; CpR 8; CpH; CpR 3; CpH; CpR 11; CpH;
     CpR 11; CpY; CpR 8; CpH; CpR 2; CpH; CpR 10; CpY; CpR 8; CpH; CpR 1;
     CpY; CpR 8; CpH; CpR 8; CpY; CpY; CpY; CpY; CpR 3; CpY; CpR 2; CpY; CpY],
     [29])`;;
let cf387 = new_definition
 `cf387 = ([CpH; CpR 2; CpH; CpR 11; CpY; CpR 7; CpH; CpR 3; CpH; CpR 10; CpH;
     CpR 10; CpY; CpR 6; CpH; CpR 3; CpH; CpR 9; CpH; CpR 9; CpY; CpR 8; CpY;
     CpR 6; CpH; CpR 7; CpY; CpY; CpR 1; CpY; CpR 3; CpY; CpR 2; CpY; CpY],
     [6])`;;
let cf388 = new_definition
 `cf388 = ([CpH; CpR 2; CpH; CpR 11; CpY; CpR 9; CpH; CpR 1; CpY;
            CpR 4; CpH; CpR 5;
     CpH; CpR 9; CpH; CpR 9; CpH; CpR 9; CpH; CpR 9; CpY; CpR 8; CpY; CpR 5;
     CpH; CpR 7; CpY; CpR 2; CpY; CpY; CpR 3; CpY; CpR 2; CpY; CpY],
     [6])`;;
let cf389 = new_definition
 `cf389 = ([CpH; CpR 2; CpH; CpR 11; CpY; CpR 5; CpH; CpR 2; CpH; CpR 10; CpY;
     CpR 3; CpH; CpR 9; CpY; CpR 2; CpY; CpR 5; CpH; CpR 1; CpY; CpR 1; CpY;
     CpR 4; CpH; CpR 1; CpH; CpR 1; CpY; CpH; CpR 4; CpY; CpY; CpR 1; CpY],
     [18])`;;
let cf390 = new_definition
 `cf390 = ([CpH; CpR 10; CpH; CpR 1; CpY; CpR 9; CpH; CpR 9; CpH;
            CpR 1; CpY; CpR 7;
     CpH; CpR 1; CpH; CpR 8; CpH; CpR 1; CpY; CpR 2; CpH; CpR 8; CpY; CpY;
     CpY; CpR 4; CpH; CpR 1; CpH; CpR 1; CpY; CpH; CpR 4; CpY; CpY; CpR 1;
     CpY],
     [25])`;;
let cf391 = new_definition
 `cf391 = ([CpH; CpR 2; CpH; CpR 11; CpY; CpR 3; CpH; CpR 2; CpH; CpR 10; CpY;
     CpR 6; CpH; CpR 9; CpH; CpR 7; CpH; CpR 1; CpH; CpR 1; CpH; CpR 1; CpH;
     CpR 1; CpY; CpR 1; CpY; CpY; CpR 1; CpY; CpR 1; CpY; CpR 4; CpH; CpR 4;
     CpY; CpY; CpR 1; CpY],
     [36])`;;
let cf392 = new_definition
 `cf392 = ([CpH; CpR 10; CpH; CpR 1; CpY; CpR 9; CpH; CpR 7; CpH; CpR 3; CpH;
     CpR 10; CpH; CpR 10; CpY; CpR 7; CpH; CpR 1; CpH; CpR 1; CpH; CpR 9;
     CpH; CpR 9; CpY; CpY; CpR 1; CpY; CpY; CpY; CpR 4; CpH; CpR 4; CpY;
     CpR 2; CpY; CpY],
     [27])`;;
let cf393 = new_definition
 `cf393 = ([CpH; CpR 10; CpH; CpR 1; CpY; CpR 7; CpH; CpR 9; CpH;
            CpR 1; CpY; CpR 7;
     CpH; CpR 1; CpH; CpR 1; CpH; CpR 9; CpH; CpR 9; CpY; CpY; CpR 1; CpY;
     CpY; CpR 4; CpH; CpR 1; CpH; CpR 1; CpY; CpH; CpR 4; CpY; CpY; CpR 1;
     CpY],
     [21])`;;
let cf394 = new_definition
 `cf394 = ([CpH; CpR 2; CpH; CpR 13; CpY; CpR 11; CpH; CpR 1; CpY; CpR 10; CpH;
     CpR 1; CpY; CpR 9; CpH; CpR 1; CpY; CpR 8; CpH; CpR 8; CpH; CpR 1; CpY;
     CpR 8; CpY; CpR 6; CpY; CpR 5; CpH; CpR 6; CpY; CpR 3; CpY; CpY; CpR 3;
     CpY; CpR 1; CpY],
     [16; 17; 32])`;;
let cf395 = new_definition
 `cf395 = ([CpH; CpR 2; CpH; CpR 12; CpY; CpR 5; CpH; CpR 9; CpH;
            CpR 1; CpH; CpR 1;
     CpY; CpR 3; CpH; CpR 10; CpY; CpR 3; CpH; CpR 9; CpY; CpR 2; CpH; CpR 1;
     CpY; CpR 2; CpY; CpR 1; CpY; CpR 5; CpH; CpR 5; CpY; CpY; CpY; CpR 1;
     CpY],
     [30])`;;
let cf396 = new_definition
 `cf396 = ([CpH; CpR 11; CpH; CpR 1; CpY; CpR 10; CpH; CpR 1; CpY; CpR 9; CpH;
     CpR 1; CpY; CpR 8; CpH; CpR 1; CpY; CpR 7; CpH; CpR 1; CpY; CpR 7; CpH;
     CpR 1; CpY; CpR 6; CpH; CpR 1; CpY; CpH; CpR 5; CpY; CpY; CpY; CpR 1;
     CpY],
     [18])`;;
let cf397 = new_definition
 `cf397 = ([CpH; CpR 11; CpH; CpR 1; CpY; CpR 10; CpH; CpR 1; CpY; CpR 9; CpH;
     CpR 1; CpY; CpR 8; CpH; CpR 1; CpY; CpR 7; CpH; CpR 1; CpY; CpR 6; CpH;
     CpR 1; CpH; CpR 7; CpH; CpR 7; CpY; CpY; CpY; CpR 1; CpY; CpR 1; CpY;
     CpR 2; CpY],
     [34])`;;
let cf398 = new_definition
 `cf398 = ([CpH; CpR 12; CpH; CpR 1; CpY; CpR 10; CpH; CpR 2; CpH; CpR 12; CpY;
     CpR 9; CpH; CpR 2; CpH; CpR 11; CpY; CpR 9; CpH; CpR 1; CpY; CpR 8; CpH;
     CpR 1; CpY; CpR 6; CpY; CpY; CpR 2; CpH; CpR 1; CpY; CpR 4; CpY; CpR 3;
     CpY; CpR 1; CpY; CpR 1; CpY],
     [33])`;;
let cf399 = new_definition
 `cf399 = ([CpH; CpR 12; CpH; CpR 1; CpY; CpR 11; CpH; CpR 1; CpY; CpR 10; CpH;
     CpR 9; CpH; CpR 2; CpH; CpR 11; CpY; CpR 9; CpH; CpR 1; CpY; CpR 8; CpH;
     CpR 1; CpY; CpR 5; CpH; CpR 1; CpY; CpR 1; CpY; CpY; CpR 3; CpY; CpR 3;
     CpY; CpR 3; CpY; CpR 1; CpY],
     [18])`;;
let cf400 = new_definition
 `cf400 = ([CpH; CpR 11; CpH; CpR 1; CpY; CpR 10; CpH; CpR 10; CpH; CpR 1; CpY;
     CpR 9; CpH; CpR 9; CpH; CpR 1; CpY; CpR 8; CpH; CpR 9; CpY; CpR 2; CpH;
     CpR 8; CpY; CpY; CpY; CpR 4; CpH; CpR 1; CpH; CpR 1; CpY; CpH; CpR 4;
     CpY; CpY; CpR 1; CpY],
     [26])`;;
let cf401 = new_definition
 `cf401 = ([CpH; CpR 2; CpH; CpR 13; CpY; CpR 9; CpH; CpR 3; CpH; CpR 12; CpH;
     CpR 12; CpY; CpR 10; CpH; CpR 1; CpY; CpR 7; CpH; CpR 3; CpH; CpR 10;
     CpH; CpR 10; CpY; CpR 9; CpY; CpR 7; CpH; CpR 8; CpY; CpR 4; CpY; CpR 4;
     CpY; CpY; CpR 1; CpY; CpY; CpY],
     [6])`;;
let cf402 = new_definition
 `cf402 = ([CpH; CpR 2; CpH; CpR 10; CpY; CpR 5; CpH; CpR 7; CpH;
            CpR 1; CpH; CpR 1;
     CpY; CpR 3; CpH; CpR 8; CpY; CpR 3; CpH; CpR 7; CpY; CpR 3; CpY; CpR 1;
     CpY; CpR 1; CpY; CpR 2; CpY; CpR 1; CpY],
     [27])`;;
let cf403 = new_definition
 `cf403 = ([CpH; CpR 9; CpH; CpR 1; CpY; CpR 3; CpH; CpR 9; CpY;
            CpR 4; CpH; CpR 2;
     CpH; CpR 8; CpY; CpR 2; CpY; CpR 4; CpH; CpR 6; CpY; CpR 2; CpH; CpR 5;
     CpY; CpR 2; CpY; CpY; CpR 2; CpY],
     [26])`;;
let cf404 = new_definition
 `cf404 = ([CpH; CpR 9; CpH; CpR 1; CpY; CpR 3; CpH; CpR 9; CpY;
            CpR 4; CpH; CpR 7;
     CpH; CpR 1; CpY; CpR 3; CpH; CpR 7; CpY; CpR 5; CpY; CpR 1; CpY; CpR 3;
     CpH; CpR 1; CpY; CpR 3; CpY; CpR 1; CpY],
     [0; 23])`;;
let cf405 = new_definition
 `cf405 = ([CpH; CpR 2; CpH; CpR 10; CpY; CpR 8; CpH; CpR 1; CpY;
            CpR 4; CpH; CpR 8;
     CpY; CpR 5; CpH; CpR 1; CpY; CpR 6; CpH; CpR 1; CpY; CpR 4; CpH; CpR 1;
     CpH; CpR 1; CpY; CpR 3; CpY; CpR 1; CpY; CpR 1; CpY],
     [6])`;;
let cf406 = new_definition
 `cf406 = ([CpH; CpR 8; CpH; CpR 3; CpH; CpR 11; CpH; CpR 11; CpY; CpR 7; CpH;
     CpR 9; CpH; CpR 1; CpY; CpR 9; CpH; CpR 9; CpY; CpY; CpY; CpY; CpR 4;
     CpH; CpR 1; CpH; CpR 1; CpY; CpR 3; CpY; CpR 1; CpY; CpR 1; CpY],
     [21])`;;
let cf407 = new_definition
 `cf407 = ([CpH; CpR 9; CpH; CpR 2; CpH; CpR 11; CpY; CpR 6; CpH;
            CpR 9; CpH; CpR 1;
     CpY; CpR 9; CpH; CpR 9; CpY; CpY; CpY; CpR 6; CpH; CpR 1; CpY; CpR 4;
     CpH; CpR 1; CpH; CpR 1; CpY; CpR 3; CpY; CpR 1; CpY; CpR 1; CpY],
     [18])`;;
let cf408 = new_definition
 `cf408 = ([CpH; CpR 3; CpH; CpR 10; CpH; CpR 1; CpY; CpR 3; CpH; CpR 10; CpY;
     CpR 5; CpH; CpR 9; CpH; CpR 2; CpH; CpR 9; CpY; CpR 2; CpH; CpR 8; CpY;
     CpY; CpR 6; CpH; CpR 1; CpY; CpR 2; CpY; CpR 1; CpY; CpR 2; CpY; CpR 1;
     CpY],
     [34])`;;
let cf409 = new_definition
 `cf409 = ([CpH; CpR 10; CpH; CpR 1; CpY; CpR 8; CpH; CpR 1; CpH;
            CpR 9; CpH; CpR 1;
     CpY; CpR 8; CpH; CpR 1; CpH; CpR 1; CpY; CpR 1; CpY; CpR 1; CpY; CpR 5;
     CpH; CpR 1; CpY; CpR 4; CpH; CpR 1; CpH; CpR 1; CpY; CpR 3; CpY; CpR 1;
     CpY; CpR 1; CpY],
     [25])`;;
let cf410 = new_definition
 `cf410 = ([CpH; CpR 10; CpH; CpR 1; CpY; CpR 3; CpH; CpR 10; CpY; CpR 5; CpH;
     CpR 7; CpH; CpR 1; CpH; CpR 1; CpY; CpR 3; CpH; CpR 8; CpY; CpR 2; CpY;
     CpR 3; CpY; CpR 1; CpY; CpR 1; CpY; CpR 2; CpY; CpR 1; CpY],
     [1; 2; 28])`;;
let cf411 = new_definition
 `cf411 = ([CpH; CpR 2; CpH; CpR 11; CpY; CpR 3; CpH; CpR 10; CpY; CpR 4; CpH;
     CpR 8; CpH; CpR 1; CpY; CpR 3; CpH; CpR 8; CpY; CpR 3; CpH; CpR 7; CpY;
     CpR 3; CpY; CpR 1; CpY; CpR 1; CpY; CpR 2; CpY; CpR 1; CpY],
     [27])`;;
let cf412 = new_definition
 `cf412 = ([CpH; CpR 10; CpH; CpR 1; CpY; CpR 3; CpH; CpR 10; CpY; CpR 3; CpH;
     CpR 9; CpY; CpR 3; CpH; CpR 2; CpH; CpR 8; CpY; CpR 2; CpY; CpR 3; CpY;
     CpR 2; CpH; CpR 1; CpY; CpR 4; CpY; CpR 1; CpY; CpR 2; CpY],
     [28])`;;
let cf413 = new_definition
 `cf413 = ([CpH; CpR 2; CpH; CpR 11; CpY; CpR 6; CpH; CpR 7; CpH;
            CpR 1; CpH; CpR 1;
     CpH; CpR 1; CpY; CpR 3; CpH; CpR 9; CpY; CpR 3; CpH; CpR 8; CpY; CpR 3;
     CpY; CpR 1; CpY; CpR 1; CpY; CpR 2; CpY; CpR 1; CpY; CpR 1; CpY],
     [25])`;;
let cf414 = new_definition
 `cf414 = ([CpH; CpR 2; CpH; CpR 11; CpY; CpR 5; CpH; CpR 8; CpH;
            CpR 1; CpH; CpR 1;
     CpY; CpR 3; CpH; CpR 9; CpY; CpR 3; CpH; CpR 8; CpY; CpR 4; CpY; CpR 1;
     CpY; CpR 1; CpY; CpR 4; CpH; CpR 4; CpY; CpY; CpR 1; CpY],
     [27])`;;
let cf415 = new_definition
 `cf415 = ([CpH; CpR 2; CpH; CpR 11; CpY; CpR 9; CpH; CpR 1; CpY;
            CpR 6; CpH; CpR 8;
     CpH; CpR 1; CpY; CpR 8; CpY; CpR 5; CpH; CpR 1; CpY; CpR 6; CpH; CpR 1;
     CpY; CpR 5; CpH; CpR 1; CpY; CpR 3; CpY; CpR 1; CpY; CpR 1; CpY],
     [6])`;;
let cf416 = new_definition
 `cf416 = ([CpH; CpR 2; CpH; CpR 11; CpY; CpR 9; CpH; CpR 1; CpY;
            CpR 4; CpH; CpR 5;
     CpH; CpR 9; CpH; CpR 9; CpH; CpR 9; CpH; CpR 9; CpY; CpR 8; CpY; CpR 6;
     CpY; CpY; CpY; CpR 3; CpY; CpR 1; CpY; CpR 1; CpY],
     [6])`;;
let cf417 = new_definition
 `cf417 = ([CpH; CpR 3; CpH; CpR 11; CpH; CpR 11; CpY; CpR 6; CpH; CpR 4; CpH;
     CpR 10; CpH; CpR 10; CpH; CpR 10; CpY; CpR 8; CpH; CpR 1; CpY; CpR 8;
     CpY; CpR 6; CpY; CpY; CpY; CpR 2; CpY; CpR 2; CpY; CpR 1; CpY],
     [31])`;;
let cf418 = new_definition
 `cf418 = ([CpH; CpR 8; CpH; CpR 3; CpH; CpR 11; CpH; CpR 11; CpY; CpR 9; CpH;
     CpR 1; CpY; CpR 8; CpH; CpR 1; CpY; CpR 6; CpH; CpR 1; CpH; CpR 1; CpY;
     CpR 6; CpY; CpY; CpY; CpR 3; CpY; CpY; CpR 2; CpY],
     [32])`;;
let cf419 = new_definition
 `cf419 = ([CpH; CpR 10; CpH; CpR 1; CpY; CpR 3; CpH; CpR 10; CpY; CpR 4; CpH;
     CpR 2; CpH; CpR 9; CpY; CpR 2; CpH; CpR 1; CpY; CpR 4; CpH; CpR 7; CpY;
     CpR 2; CpH; CpR 6; CpY; CpR 3; CpY; CpY; CpY; CpR 2; CpY],
     [29])`;;
let cf420 = new_definition
 `cf420 = ([CpH; CpR 10; CpH; CpR 1; CpY; CpR 8; CpH; CpR 2; CpH; CpR 10; CpY;
     CpR 7; CpH; CpR 2; CpH; CpR 9; CpY; CpR 6; CpH; CpR 2; CpH; CpR 8; CpY;
     CpR 6; CpY; CpY; CpR 4; CpY; CpY; CpY; CpR 2; CpY],
     [32])`;;
let cf421 = new_definition
 `cf421 = ([CpH; CpR 2; CpH; CpR 11; CpY; CpR 9; CpH; CpR 1; CpY;
            CpR 7; CpH; CpR 2;
     CpH; CpR 9; CpY; CpR 6; CpH; CpR 8; CpY; CpR 6; CpY; CpY; CpR 4; CpH;
     CpR 5; CpY; CpR 2; CpH; CpR 4; CpY; CpR 2; CpY; CpY],
     [6])`;;
let cf422 = new_definition
 `cf422 = ([CpH; CpR 10; CpH; CpR 1; CpY; CpR 7; CpH; CpR 3; CpH; CpR 10; CpH;
     CpR 10; CpY; CpR 7; CpH; CpR 2; CpH; CpR 9; CpY; CpR 7; CpH; CpR 1; CpY;
     CpR 6; CpY; CpY; CpR 3; CpY; CpY; CpR 2; CpY; CpR 1; CpY],
     [31])`;;
let cf423 = new_definition
 `cf423 = ([CpH; CpR 2; CpH; CpR 11; CpY; CpR 4; CpH; CpR 9; CpH;
            CpR 1; CpY; CpR 3;
     CpH; CpR 9; CpY; CpR 3; CpH; CpR 2; CpH; CpR 8; CpY; CpR 3; CpY; CpR 1;
     CpY; CpR 3; CpH; CpR 1; CpY; CpR 1; CpY; CpR 3; CpY; CpR 1; CpY],
     [26])`;;
let cf424 = new_definition
 `cf424 = ([CpH; CpR 9; CpH; CpR 1; CpY; CpR 3; CpH; CpR 9; CpY;
            CpR 4; CpH; CpR 7;
     CpH; CpR 1; CpY; CpR 2; CpH; CpR 1; CpH; CpR 1; CpY; CpR 3; CpY; CpR 1;
     CpY; CpR 2; CpH; CpR 1; CpY; CpR 1; CpY; CpY],
     [26])`;;
let cf425 = new_definition
 `cf425 = ([CpH; CpR 2; CpH; CpR 10; CpY; CpR 4; CpH; CpR 8; CpH;
            CpR 1; CpY; CpR 3;
     CpH; CpR 8; CpY; CpR 4; CpH; CpR 6; CpH; CpR 1; CpY; CpR 3; CpY; CpR 1;
     CpY; CpR 4; CpH; CpR 4; CpY; CpY; CpR 1; CpY],
     [26])`;;
let cf426 = new_definition
 `cf426 = ([CpH; CpR 10; CpH; CpR 1; CpY; CpR 3; CpH; CpR 10; CpY; CpR 5; CpH;
     CpR 7; CpH; CpR 1; CpH; CpR 1; CpY; CpR 3; CpH; CpR 8; CpY; CpR 5; CpY;
     CpR 1; CpY; CpR 4; CpH; CpR 1; CpY; CpR 3; CpY; CpR 1; CpY; CpR 1; CpY],
     [30])`;;
let cf427 = new_definition
 `cf427 = ([CpH; CpR 9; CpH; CpR 1; CpY; CpR 3; CpH; CpR 9; CpY;
            CpR 4; CpH; CpR 2;
     CpH; CpR 8; CpY; CpR 2; CpY; CpR 5; CpH; CpR 6; CpH; CpR 6; CpY; CpR 1;
     CpH; CpR 1; CpY; CpR 1; CpY; CpY; CpR 2; CpY],
     [28])`;;
let cf428 = new_definition
 `cf428 = ([CpH; CpR 2; CpH; CpR 11; CpY; CpR 3; CpH; CpR 2; CpH; CpR 10; CpY;
     CpR 4; CpH; CpR 8; CpH; CpR 1; CpY; CpR 3; CpH; CpR 8; CpY; CpR 4; CpH;
     CpR 7; CpY; CpR 2; CpY; CpY; CpR 3; CpY; CpR 1; CpY; CpY],
     [19])`;;
let cf429 = new_definition
 `cf429 = ([CpH; CpR 10; CpH; CpR 1; CpY; CpR 3; CpH; CpR 10; CpY; CpR 3; CpH;
     CpR 2; CpH; CpR 9; CpY; CpR 3; CpH; CpR 1; CpY; CpR 4; CpH; CpR 7; CpY;
     CpR 2; CpY; CpY; CpR 2; CpH; CpR 1; CpY; CpR 1; CpY; CpY],
     [27])`;;
let cf430 = new_definition
 `cf430 = ([CpH; CpR 2; CpH; CpR 11; CpY; CpR 9; CpH; CpR 1; CpY;
            CpR 8; CpH; CpR 1;
     CpY; CpR 5; CpH; CpR 8; CpY; CpR 6; CpY; CpR 6; CpH; CpR 1; CpY; CpR 4;
     CpH; CpR 1; CpH; CpR 1; CpY; CpR 3; CpY; CpR 1; CpY; CpR 1; CpY],
     [6])`;;
let cf431 = new_definition
 `cf431 = ([CpH; CpR 2; CpH; CpR 11; CpY; CpR 5; CpH; CpR 8; CpH;
            CpR 1; CpH; CpR 1;
     CpY; CpR 3; CpH; CpR 9; CpY; CpR 4; CpH; CpR 8; CpH; CpR 8; CpY; CpR 3;
     CpY; CpR 1; CpY; CpR 1; CpY; CpR 1; CpY; CpR 2; CpY; CpR 1; CpY],
     [30])`;;
let cf432 = new_definition
 `cf432 = ([CpH; CpR 10; CpH; CpR 1; CpY; CpR 8; CpH; CpR 2; CpH; CpR 10; CpY;
     CpR 8; CpH; CpR 1; CpY; CpR 7; CpH; CpR 7; CpH; CpR 1; CpY; CpR 6; CpY;
     CpR 4; CpH; CpR 6; CpY; CpY; CpR 1; CpY; CpR 2; CpY; CpR 1; CpY],
     [31])`;;
let cf433 = new_definition
 `cf433 = ([CpH; CpR 10; CpH; CpR 1; CpY; CpR 3; CpH; CpR 10; CpY; CpR 3; CpH;
     CpR 9; CpY; CpR 3; CpH; CpR 8; CpY; CpR 3; CpH; CpR 1; CpY; CpR 3; CpY;
     CpR 4; CpH; CpR 1; CpY; CpH; CpR 4; CpY; CpY; CpR 1; CpY],
     [6])`;;
let cf434 = new_definition
 `cf434 = ([CpH; CpR 2; CpH; CpR 11; CpY; CpR 3; CpH; CpR 10; CpY; CpR 3; CpH;
     CpR 9; CpY; CpR 4; CpH; CpR 2; CpH; CpR 8; CpY; CpR 3; CpY; CpR 3; CpH;
     CpR 1; CpH; CpR 1; CpY; CpR 1; CpY; CpY; CpR 3; CpY; CpR 1; CpY],
     [1; 2; 9; 22])`;;
let cf435 = new_definition
 `cf435 = ([CpH; CpR 9; CpH; CpR 2; CpH; CpR 11; CpY; CpR 9; CpH;
            CpR 9; CpH; CpR 1;
     CpY; CpR 8; CpH; CpR 1; CpY; CpR 7; CpH; CpR 1; CpY; CpR 4; CpH; CpR 1;
     CpY; CpR 1; CpY; CpY; CpR 3; CpY; CpY; CpR 2; CpY],
     [11; 12; 30])`;;
let cf436 = new_definition
 `cf436 = ([CpH; CpR 10; CpH; CpR 2; CpH; CpR 12; CpY; CpR 8; CpH; CpR 10; CpH;
     CpR 1; CpY; CpR 9; CpH; CpR 1; CpY; CpR 9; CpH; CpR 9; CpY; CpY; CpY;
     CpR 6; CpH; CpR 1; CpY; CpR 5; CpH; CpR 1; CpY; CpR 3; CpY; CpR 1; CpY;
     CpR 1; CpY],
     [22])`;;
let cf437 = new_definition
 `cf437 = ([CpH; CpR 10; CpH; CpR 2; CpH; CpR 12; CpY; CpR 10; CpH; CpR 8; CpH;
     CpR 3; CpH; CpR 11; CpH; CpR 11; CpY; CpR 9; CpH; CpR 1; CpY; CpR 9;
     CpH; CpR 9; CpY; CpY; CpY; CpY; CpY; CpR 3; CpY; CpR 1; CpY; CpR 1; CpY],
     [28])`;;
let cf438 = new_definition
 `cf438 = ([CpH; CpR 11; CpH; CpR 1; CpY; CpR 10; CpH; CpR 10; CpH; CpR 1; CpY;
     CpR 8; CpH; CpR 2; CpH; CpR 10; CpY; CpR 4; CpH; CpR 9; CpY; CpY; CpY;
     CpY; CpR 4; CpH; CpR 1; CpH; CpR 1; CpY; CpR 3; CpY; CpR 1; CpY; CpR 1;
     CpY],
     [25])`;;
let cf439 = new_definition
 `cf439 = ([CpH; CpR 3; CpH; CpR 11; CpH; CpR 1; CpY; CpR 3; CpH; CpR 11; CpY;
     CpR 5; CpH; CpR 2; CpH; CpR 10; CpY; CpR 9; CpH; CpR 1; CpY; CpR 2; CpH;
     CpR 8; CpY; CpY; CpR 6; CpH; CpR 1; CpY; CpR 2; CpY; CpR 1; CpY; CpR 2;
     CpY; CpR 1; CpY],
     [35])`;;
let cf440 = new_definition
 `cf440 = ([CpH; CpR 10; CpH; CpR 2; CpH; CpR 12; CpY; CpR 10; CpH; CpR 1; CpY;
     CpR 9; CpH; CpR 1; CpY; CpR 7; CpH; CpR 1; CpH; CpR 8; CpH; CpR 1; CpY;
     CpR 8; CpH; CpR 1; CpY; CpR 1; CpY; CpR 1; CpY; CpR 5; CpY; CpR 2; CpY;
     CpR 2; CpY; CpR 1; CpY],
     [12; 28; 32; 35])`;;
let cf441 = new_definition
 `cf441 = ([CpH; CpR 11; CpH; CpR 1; CpY; CpR 10; CpH; CpR 1; CpY; CpR 8; CpH;
     CpR 1; CpH; CpR 9; CpH; CpR 1; CpY; CpR 8; CpH; CpR 1; CpH; CpR 1; CpY;
     CpR 1; CpY; CpR 1; CpY; CpR 5; CpH; CpR 1; CpY; CpR 5; CpH; CpR 1; CpY;
     CpR 3; CpY; CpR 1; CpY; CpR 1; CpY],
     [29])`;;
let cf442 = new_definition
 `cf442 = ([CpH; CpR 2; CpH; CpR 11; CpY; CpR 5; CpH; CpR 8; CpH;
            CpR 1; CpH; CpR 1;
     CpY; CpR 4; CpH; CpR 9; CpH; CpR 2; CpH; CpR 9; CpY; CpR 2; CpH; CpR 8;
     CpY; CpY; CpY; CpR 2; CpY; CpR 2; CpH; CpR 1; CpY; CpR 1; CpY; CpY],
     [32])`;;
let cf443 = new_definition
 `cf443 = ([CpH; CpR 2; CpH; CpR 11; CpY; CpR 3; CpH; CpR 10; CpY; CpR 6; CpH;
     CpR 9; CpH; CpR 2; CpH; CpR 9; CpY; CpR 2; CpH; CpR 8; CpY; CpY; CpR 5;
     CpH; CpR 1; CpH; CpR 1; CpY; CpR 2; CpY; CpR 4; CpH; CpR 4; CpY; CpY;
     CpR 1; CpY],
     [35])`;;
let cf444 = new_definition
 `cf444 = ([CpH; CpR 11; CpH; CpR 1; CpY; CpR 3; CpH; CpR 11; CpY; CpR 6; CpH;
     CpR 7; CpH; CpR 1; CpH; CpR 1; CpH; CpR 1; CpY; CpR 3; CpH; CpR 9; CpY;
     CpR 2; CpY; CpR 3; CpY; CpR 1; CpY; CpR 1; CpY; CpR 2; CpY; CpR 1; CpY;
     CpR 1; CpY],
     [6])`;;
let cf445 = new_definition
 `cf445 = ([CpH; CpR 2; CpH; CpR 12; CpY; CpR 10; CpH; CpR 1; CpY; CpR 6; CpH;
     CpR 4; CpH; CpR 10; CpH; CpR 10; CpH; CpR 10; CpY; CpR 8; CpH; CpR 1;
     CpY; CpR 8; CpY; CpR 6; CpY; CpY; CpY; CpR 3; CpY; CpR 1; CpY; CpR 1;
     CpY],
     [23])`;;
let cf446 = new_definition
 `cf446 = ([CpH; CpR 10; CpH; CpR 1; CpH; CpR 1; CpY; CpR 5; CpH;
            CpR 9; CpH; CpR 1;
     CpH; CpR 1; CpY; CpR 3; CpH; CpR 10; CpY; CpR 3; CpH; CpR 9; CpY; CpR 2;
     CpY; CpR 3; CpY; CpR 1; CpY; CpR 1; CpY; CpR 3; CpY; CpR 3; CpY; CpR 2;
     CpY],
     [8])`;;
let cf447 = new_definition
 `cf447 = ([CpH; CpR 11; CpH; CpR 1; CpY; CpR 9; CpH; CpR 2; CpH; CpR 11; CpY;
     CpR 8; CpH; CpR 2; CpH; CpR 10; CpY; CpR 8; CpH; CpR 1; CpY; CpR 7; CpH;
     CpR 1; CpY; CpR 6; CpY; CpY; CpR 4; CpY; CpY; CpY; CpR 2; CpY],
     [8; 9; 30; 32])`;;
let cf448 = new_definition
 `cf448 = ([CpH; CpR 2; CpH; CpR 12; CpY; CpR 10; CpH; CpR 1; CpY; CpR 8; CpH;
     CpR 2; CpH; CpR 10; CpY; CpR 8; CpH; CpR 8; CpH; CpR 1; CpY; CpR 8; CpY;
     CpR 6; CpY; CpY; CpR 3; CpY; CpR 2; CpH; CpR 1; CpY; CpR 3; CpY; CpR 1;
     CpY],
     [32])`;;
let cf449 = new_definition
 `cf449 = ([CpH; CpR 11; CpH; CpR 1; CpY; CpR 3; CpH; CpR 11; CpY; CpR 5; CpH;
     CpR 8; CpH; CpR 1; CpH; CpR 1; CpY; CpR 4; CpH; CpR 8; CpH; CpR 1; CpY;
     CpR 2; CpY; CpR 3; CpY; CpR 1; CpY; CpR 2; CpY; CpR 2; CpY; CpR 3; CpY;
     CpR 2; CpY],
     [33])`;;
let cf450 = new_definition
 `cf450 = ([CpH; CpR 2; CpH; CpR 12; CpY; CpR 10; CpH; CpR 1; CpY; CpR 7; CpH;
     CpR 3; CpH; CpR 10; CpH; CpR 10; CpY; CpR 8; CpH; CpR 1; CpY; CpR 8;
     CpH; CpR 8; CpY; CpR 6; CpY; CpY; CpR 2; CpY; CpR 2; CpY; CpR 1; CpY;
     CpR 1; CpY],
     [30])`;;
let cf451 = new_definition
 `cf451 = ([CpH; CpR 10; CpH; CpR 1; CpY; CpR 3; CpH; CpR 10; CpY; CpR 4; CpH;
     CpR 8; CpH; CpR 1; CpY; CpR 4; CpH; CpR 7; CpH; CpR 1; CpY; CpR 2; CpY;
     CpR 3; CpY; CpR 1; CpY; CpR 2; CpH; CpR 1; CpY; CpR 1; CpY; CpY],
     [27])`;;
let cf452 = new_definition
 `cf452 = ([CpH; CpR 2; CpH; CpR 11; CpY; CpR 4; CpH; CpR 9; CpH;
            CpR 1; CpY; CpR 3;
     CpH; CpR 9; CpY; CpR 3; CpH; CpR 8; CpY; CpR 3; CpH; CpR 7; CpY; CpR 3;
     CpY; CpR 1; CpY; CpR 4; CpH; CpR 4; CpY; CpY; CpR 1; CpY],
     [0; 27])`;;
let cf453 = new_definition
 `cf453 = ([CpH; CpR 10; CpH; CpR 1; CpY; CpR 3; CpH; CpR 10; CpY; CpR 4; CpH;
     CpR 8; CpH; CpR 1; CpY; CpR 3; CpH; CpR 8; CpY; CpR 2; CpH; CpR 1; CpY;
     CpR 3; CpY; CpR 1; CpY; CpR 3; CpH; CpR 1; CpY; CpR 3; CpY; CpR 1; CpY],
     [27])`;;
let cf454 = new_definition
 `cf454 = ([CpH; CpR 2; CpH; CpR 12; CpY; CpR 3; CpH; CpR 11; CpY; CpR 5; CpH;
     CpR 8; CpH; CpR 1; CpH; CpR 1; CpY; CpR 3; CpH; CpR 9; CpY; CpR 3; CpH;
     CpR 8; CpY; CpR 3; CpY; CpR 1; CpY; CpR 1; CpY; CpR 2; CpY; CpR 1; CpY;
     CpR 1; CpY],
     [15; 30; 33])`;;
let cf455 = new_definition
 `cf455 = ([CpH; CpR 2; CpH; CpR 12; CpY; CpR 3; CpH; CpR 11; CpY; CpR 4; CpH;
     CpR 9; CpH; CpR 1; CpY; CpR 3; CpH; CpR 9; CpY; CpR 3; CpH; CpR 8; CpY;
     CpR 4; CpY; CpR 1; CpY; CpR 1; CpY; CpR 4; CpH; CpR 4; CpY; CpY; CpR 1;
     CpY],
     [27])`;;
let cf456 = new_definition
 `cf456 = ([CpH; CpR 2; CpH; CpR 12; CpY; CpR 10; CpH; CpR 1; CpY; CpR 9; CpH;
     CpR 1; CpY; CpR 7; CpH; CpR 8; CpH; CpR 1; CpY; CpR 8; CpY; CpR 6; CpY;
     CpR 6; CpH; CpR 1; CpY; CpR 5; CpH; CpR 1; CpY; CpR 3; CpY; CpR 1; CpY;
     CpR 1; CpY],
     [31])`;;
let cf457 = new_definition
 `cf457 = ([CpH; CpR 2; CpH; CpR 12; CpY; CpR 10; CpH; CpR 1; CpY; CpR 9; CpH;
     CpR 1; CpY; CpR 5; CpH; CpR 4; CpH; CpR 9; CpH; CpR 9; CpH; CpR 9; CpY;
     CpR 8; CpY; CpR 6; CpY; CpY; CpY; CpR 3; CpY; CpR 1; CpY; CpR 1; CpY],
     [30])`;;
let cf458 = new_definition
 `cf458 = ([CpH; CpR 10; CpH; CpR 1; CpH; CpR 1; CpY; CpR 3; CpH; CpR 11; CpY;
     CpR 4; CpH; CpR 9; CpH; CpR 1; CpY; CpR 3; CpH; CpR 9; CpY; CpR 2; CpH;
     CpR 1; CpY; CpR 3; CpY; CpR 1; CpY; CpR 1; CpY; CpR 4; CpY; CpR 3; CpY;
     CpR 1; CpY],
     [30])`;;
let cf459 = new_definition
 `cf459 = ([CpH; CpR 10; CpH; CpR 1; CpH; CpR 1; CpY; CpR 3; CpH; CpR 11; CpY;
     CpR 5; CpH; CpR 8; CpH; CpR 1; CpH; CpR 1; CpY; CpR 3; CpH; CpR 9; CpY;
     CpR 2; CpY; CpR 3; CpY; CpR 1; CpY; CpR 1; CpY; CpR 1; CpY; CpR 2; CpY;
     CpR 1; CpY],
     [31])`;;
let cf460 = new_definition
 `cf460 = ([CpH; CpR 2; CpH; CpR 12; CpY; CpR 10; CpH; CpR 1; CpY; CpR 9; CpH;
     CpR 1; CpY; CpR 8; CpH; CpR 1; CpY; CpR 6; CpH; CpR 8; CpY; CpR 6; CpY;
     CpR 4; CpH; CpR 6; CpY; CpR 2; CpH; CpR 5; CpY; CpR 3; CpY; CpY; CpY],
     [16; 17; 32])`;;
let cf461 = new_definition
 `cf461 = ([CpH; CpR 2; CpH; CpR 12; CpY; CpR 3; CpH; CpR 11; CpY; CpR 4; CpH;
     CpR 9; CpH; CpR 1; CpY; CpR 3; CpH; CpR 9; CpY; CpR 4; CpH; CpR 8; CpH;
     CpR 8; CpY; CpR 3; CpY; CpR 1; CpY; CpR 1; CpY; CpR 1; CpY; CpR 2; CpY;
     CpR 1; CpY],
     [31])`;;
let cf462 = new_definition
 `cf462 = ([CpH; CpR 2; CpH; CpR 11; CpY; CpR 9; CpH; CpR 1; CpY;
            CpR 8; CpH; CpR 1;
     CpY; CpR 7; CpH; CpR 1; CpY; CpR 7; CpH; CpR 7; CpH; CpR 7; CpY; CpR 5;
     CpY; CpR 4; CpH; CpR 5; CpY; CpY; CpR 1; CpY; CpR 2; CpY],
     [16; 17; 32])`;;
let cf463 = new_definition
 `cf463 = ([CpH; CpR 10; CpH; CpR 1; CpY; CpR 9; CpH; CpR 1; CpY;
            CpR 8; CpH; CpR 1;
     CpY; CpR 7; CpH; CpR 1; CpY; CpR 5; CpH; CpR 2; CpH; CpR 7; CpY; CpR 5;
     CpY; CpR 2; CpH; CpR 1; CpY; CpR 1; CpY; CpY; CpR 2; CpY],
     [12; 13; 32])`;;
let cf464 = new_definition
 `cf464 = ([CpH; CpR 11; CpH; CpR 1; CpY; CpR 3; CpH; CpR 11; CpY; CpR 4; CpH;
     CpR 9; CpH; CpR 1; CpY; CpR 3; CpH; CpR 2; CpH; CpR 9; CpY; CpR 2; CpY;
     CpR 3; CpY; CpR 3; CpH; CpR 6; CpY; CpY; CpR 1; CpY; CpR 2; CpY; CpR 1;
     CpY],
     [1; 2; 32])`;;
let cf465 = new_definition
 `cf465 = ([CpH; CpR 10; CpH; CpR 1; CpY; CpR 3; CpH; CpR 10; CpY; CpR 5; CpH;
     CpR 7; CpH; CpR 1; CpH; CpR 1; CpY; CpR 3; CpH; CpR 8; CpY; CpR 2; CpY;
     CpR 3; CpY; CpR 2; CpH; CpR 5; CpY; CpR 2; CpY; CpY; CpR 2; CpY],
     [26])`;;
let cf466 = new_definition
 `cf466 = ([CpH; CpR 2; CpH; CpR 12; CpY; CpR 4; CpH; CpR 10; CpH; CpR 1; CpY;
     CpR 3; CpH; CpR 10; CpY; CpR 4; CpH; CpR 8; CpH; CpR 1; CpY; CpR 3; CpH;
     CpR 8; CpY; CpR 3; CpY; CpR 5; CpY; CpR 1; CpY; CpR 3; CpY; CpY; CpR 2;
     CpY],
     [23])`;;
let cf467 = new_definition
 `cf467 = ([CpH; CpR 2; CpH; CpR 12; CpY; CpR 10; CpH; CpR 1; CpY; CpR 8; CpH;
     CpR 2; CpH; CpR 10; CpY; CpR 8; CpH; CpR 1; CpY; CpR 7; CpH; CpR 8; CpY;
     CpR 6; CpY; CpR 4; CpH; CpR 6; CpY; CpY; CpR 1; CpY; CpR 2; CpY; CpR 1;
     CpY],
     [32])`;;
let cf468 = new_definition
 `cf468 = ([CpH; CpR 11; CpH; CpR 1; CpY; CpR 3; CpH; CpR 11; CpY; CpR 3; CpH;
     CpR 10; CpY; CpR 3; CpH; CpR 9; CpY; CpR 4; CpH; CpR 1; CpY; CpR 3; CpY;
     CpR 4; CpH; CpR 6; CpH; CpR 6; CpY; CpR 3; CpY; CpR 1; CpY; CpY; CpY],
     [33])`;;
let cf469 = new_definition
 `cf469 = ([CpH; CpR 11; CpH; CpR 1; CpY; CpR 3; CpH; CpR 11; CpY; CpR 3; CpH;
     CpR 10; CpY; CpR 3; CpH; CpR 9; CpY; CpR 4; CpH; CpR 1; CpY; CpR 3; CpY;
     CpR 3; CpH; CpR 1; CpH; CpR 1; CpY; CpR 1; CpY; CpY; CpR 3; CpY; CpR 1;
     CpY],
     [1; 2; 13; 23])`;;
let cf470 = new_definition
 `cf470 = ([CpH; CpR 10; CpH; CpR 2; CpH; CpR 12; CpY; CpR 9; CpH; CpR 2; CpH;
     CpR 11; CpY; CpR 9; CpH; CpR 1; CpY; CpR 8; CpH; CpR 1; CpY; CpR 7; CpH;
     CpR 1; CpY; CpR 5; CpY; CpR 1; CpY; CpR 3; CpY; CpY; CpR 3; CpY; CpY],
     [11; 12; 33])`;;
let cf471 = new_definition
 `cf471 = ([CpH; CpR 11; CpH; CpR 1; CpY; CpR 4; CpH; CpR 10; CpH; CpR 1; CpY;
     CpR 3; CpH; CpR 10; CpY; CpR 3; CpH; CpR 9; CpY; CpR 3; CpH; CpR 1; CpY;
     CpR 4; CpY; CpY; CpR 3; CpH; CpR 1; CpY; CpR 1; CpY; CpY; CpY],
     [19; 20; 33])`;;
let cf472 = new_definition
 `cf472 = ([CpH; CpR 2; CpH; CpR 12; CpY; CpR 5; CpH; CpR 9; CpH;
            CpR 1; CpH; CpR 1;
     CpY; CpR 3; CpH; CpR 10; CpY; CpR 2; CpH; CpR 1; CpH; CpR 1; CpH; CpR 1;
     CpY; CpR 6; CpY; CpR 1; CpY; CpR 1; CpY; CpR 3; CpY; CpY; CpR 1; CpY;
     CpR 1; CpY],
     [33])`;;
let cf473 = new_definition
 `cf473 = ([CpH; CpR 11; CpH; CpR 1; CpY; CpR 7; CpH; CpR 10; CpH; CpR 1; CpY;
     CpR 9; CpH; CpR 1; CpY; CpR 9; CpY; CpR 7; CpH; CpR 8; CpH; CpR 8; CpH;
     CpR 8; CpH; CpR 8; CpY; CpY; CpR 1; CpY; CpR 4; CpY; CpY; CpY; CpY],
     [18])`;;
let cf474 = new_definition
 `cf474 = ([CpH; CpR 2; CpH; CpR 12; CpY; CpR 10; CpH; CpR 1; CpY; CpR 9; CpH;
     CpR 6; CpH; CpR 4; CpH; CpR 10; CpH; CpR 10; CpH; CpR 10; CpY; CpR 9;
     CpY; CpR 6; CpH; CpR 1; CpY; CpR 7; CpY; CpR 1; CpY; CpR 3; CpY; CpR 1;
     CpY; CpR 2; CpY; CpY],
     [21])`;;
let cf475 = new_definition
 `cf475 = ([CpH; CpR 9; CpH; CpR 3; CpH; CpR 12; CpH; CpR 12; CpY; CpR 10; CpH;
     CpR 1; CpY; CpR 9; CpH; CpR 9; CpH; CpR 1; CpY; CpR 8; CpH; CpR 1; CpY;
     CpR 3; CpH; CpR 8; CpY; CpR 3; CpY; CpY; CpY; CpR 3; CpY; CpR 1; CpY;
     CpY],
     [8; 33; 36])`;;
let cf476 = new_definition
 `cf476 = ([CpH; CpR 3; CpH; CpR 12; CpH; CpR 12; CpY; CpR 10; CpH; CpR 1; CpY;
     CpR 5; CpH; CpR 5; CpH; CpR 10; CpH; CpR 10; CpH; CpR 10; CpH; CpR 10;
     CpY; CpR 9; CpY; CpR 7; CpY; CpY; CpY; CpY; CpR 3; CpY; CpR 1; CpY;
     CpR 1; CpY],
     [33])`;;
let cf477 = new_definition
 `cf477 = ([CpH; CpR 11; CpH; CpR 1; CpY; CpR 9; CpH; CpR 2; CpH; CpR 11; CpY;
     CpR 9; CpH; CpR 1; CpY; CpR 8; CpH; CpR 7; CpH; CpR 1; CpH; CpR 1; CpY;
     CpR 7; CpY; CpR 4; CpH; CpR 7; CpY; CpY; CpR 1; CpY; CpR 2; CpY; CpR 2;
     CpY; CpY],
     [33; 36])`;;
let cf478 = new_definition
 `cf478 = ([CpH; CpR 2; CpH; CpR 12; CpY; CpR 4; CpH; CpR 10; CpH; CpR 1; CpY;
     CpR 3; CpH; CpR 10; CpY; CpR 4; CpH; CpR 9; CpH; CpR 9; CpY; CpR 8; CpY;
     CpR 5; CpH; CpR 7; CpH; CpR 7; CpY; CpY; CpR 1; CpY; CpR 2; CpY; CpR 1;
     CpY; CpR 1; CpY],
     [30; 32; 36])`;;
let cf479 = new_definition
 `cf479 = ([CpH; CpR 11; CpH; CpR 1; CpY; CpR 4; CpH; CpR 10; CpH; CpR 1; CpY;
     CpR 3; CpH; CpR 3; CpH; CpR 9; CpH; CpR 1; CpY; CpR 2; CpH; CpR 1; CpY;
     CpR 5; CpH; CpR 8; CpY; CpY; CpR 1; CpY; CpR 3; CpY; CpR 1; CpY; CpR 3;
     CpY; CpR 2; CpY],
     [15; 16; 33])`;;
let cf480 = new_definition
 `cf480 = ([CpH; CpR 2; CpH; CpR 12; CpY; CpR 9; CpH; CpR 2; CpH; CpR 11; CpY;
     CpR 9; CpH; CpR 7; CpH; CpR 3; CpH; CpR 10; CpH; CpR 10; CpY; CpR 9;
     CpY; CpR 5; CpH; CpR 1; CpY; CpR 1; CpY; CpY; CpR 3; CpY; CpR 1; CpY;
     CpR 2; CpY; CpY],
     [20; 24; 36])`;;
let cf481 = new_definition
 `cf481 = ([CpH; CpR 11; CpH; CpR 1; CpY; CpR 10; CpH; CpR 1; CpY; CpR 9; CpH;
     CpR 1; CpY; CpR 5; CpH; CpR 1; CpH; CpR 1; CpH; CpR 1; CpH; CpR 1; CpY;
     CpR 5; CpH; CpR 1; CpY; CpR 1; CpY; CpY; CpR 3; CpY; CpY; CpR 3; CpY;
     CpY],
     [35])`;;
let cf482 = new_definition
 `cf482 = ([CpH; CpR 10; CpH; CpR 1; CpY; CpR 5; CpH; CpR 8; CpH;
            CpR 1; CpH; CpR 1;
     CpY; CpR 3; CpH; CpR 9; CpY; CpR 3; CpH; CpR 1; CpY; CpR 3; CpH; CpR 1;
     CpY; CpR 1; CpY; CpY; CpR 2; CpH; CpR 1; CpY; CpR 1; CpY; CpY],
     [30])`;;
let cf483 = new_definition
 `cf483 = ([CpH; CpR 9; CpH; CpR 1; CpH; CpR 1; CpH; CpR 1; CpY; CpR 3;
            CpH; CpR 11;
     CpY; CpR 6; CpH; CpR 7; CpH; CpR 1; CpH; CpR 1; CpH; CpR 1; CpY; CpR 2;
     CpY; CpR 4; CpY; CpY; CpR 5; CpY; CpR 1; CpY; CpY; CpY; CpY],
     [32])`;;
let cf484 = new_definition
 `cf484 = ([CpH; CpR 10; CpH; CpR 1; CpY; CpR 8; CpH; CpR 9; CpH;
            CpR 1; CpY; CpR 7;
     CpH; CpR 2; CpH; CpR 9; CpY; CpR 8; CpY; CpR 3; CpY; CpY; CpR 3; CpH;
     CpR 5; CpH; CpR 1; CpH; CpR 1; CpY; CpR 1; CpY; CpY; CpY],
     [23])`;;
let cf485 = new_definition
 `cf485 = ([CpH; CpR 8; CpH; CpR 3; CpH; CpR 11; CpH; CpR 11; CpY; CpR 9; CpH;
     CpR 9; CpH; CpR 1; CpY; CpR 8; CpH; CpR 1; CpY; CpR 8; CpY; CpR 4; CpH;
     CpR 7; CpY; CpY; CpR 1; CpY; CpR 2; CpH; CpR 1; CpY; CpR 1; CpY; CpY],
     [30])`;;
let cf486 = new_definition
 `cf486 = ([CpH; CpR 11; CpH; CpR 2; CpH; CpR 13; CpY; CpR 8; CpH; CpR 11; CpH;
     CpR 1; CpY; CpR 10; CpH; CpR 1; CpY; CpR 10; CpH; CpR 10; CpY; CpY; CpY;
     CpR 6; CpH; CpR 1; CpH; CpR 1; CpY; CpR 5; CpH; CpR 1; CpY; CpR 1; CpY;
     CpR 3; CpY; CpR 1; CpY; CpR 1; CpY],
     [36])`;;
let cf487 = new_definition
 `cf487 = ([CpH; CpR 9; CpH; CpR 4; CpH; CpR 13; CpH; CpR 13; CpH; CpR 13; CpY;
     CpR 11; CpH; CpR 1; CpY; CpR 10; CpH; CpR 10; CpH; CpR 1; CpY; CpR 10;
     CpH; CpR 1; CpY; CpR 9; CpH; CpR 1; CpY; CpR 1; CpY; CpR 1; CpY; CpR 6;
     CpY; CpY; CpR 3; CpY; CpR 1; CpY; CpR 1; CpY],
     [36])`;;
let cf488 = new_definition
 `cf488 = ([CpH; CpR 10; CpH; CpR 3; CpH; CpR 13; CpH; CpR 13; CpY;
            CpR 11; CpH;
     CpR 1; CpY; CpR 10; CpH; CpR 1; CpY; CpR 8; CpH; CpR 1; CpH; CpR 9; CpH;
     CpR 1; CpY; CpR 9; CpH; CpR 1; CpY; CpR 1; CpY; CpR 1; CpY; CpR 6; CpY;
     CpY; CpR 3; CpY; CpR 1; CpY; CpR 1; CpY],
     [10; 11; 40])`;;
let cf489 = new_definition
 `cf489 = ([CpH; CpR 11; CpH; CpR 2; CpH; CpR 13; CpY; CpR 11; CpH; CpR 1; CpY;
     CpR 9; CpH; CpR 2; CpH; CpR 11; CpY; CpR 8; CpH; CpR 1; CpH; CpR 9; CpH;
     CpR 1; CpY; CpR 9; CpH; CpR 1; CpY; CpR 1; CpY; CpR 1; CpY; CpR 6; CpY;
     CpR 2; CpY; CpR 2; CpY; CpR 1; CpY; CpR 1; CpY],
     [8; 31; 35; 37])`;;
let cf490 = new_definition
 `cf490 = ([CpH; CpR 2; CpH; CpR 13; CpY; CpR 4; CpH; CpR 2; CpH; CpR 12; CpY;
     CpR 4; CpH; CpR 10; CpH; CpR 1; CpY; CpR 4; CpH; CpR 1; CpY; CpR 8; CpH;
     CpR 1; CpH; CpR 1; CpY; CpR 1; CpY; CpR 2; CpH; CpR 7; CpY; CpR 2; CpY;
     CpY; CpR 3; CpY; CpR 1; CpY; CpY],
     [19])`;;
let cf491 = new_definition
 `cf491 = ([CpH; CpR 2; CpH; CpR 11; CpY; CpR 9; CpH; CpR 1; CpY;
            CpR 8; CpH; CpR 1;
     CpY; CpR 5; CpH; CpR 8; CpY; CpR 4; CpH; CpR 2; CpH; CpR 7; CpY; CpH;
     CpR 1; CpY; CpR 4; CpH; CpR 5; CpY; CpR 3; CpH; CpR 4; CpY; CpY; CpR 1;
     CpY],
     [6])`;;
let cf492 = new_definition
 `cf492 = ([CpH; CpR 9; CpH; CpR 1; CpH; CpR 1; CpH; CpR 1; CpY; CpR 3;
            CpH; CpR 11;
     CpY; CpR 3; CpH; CpR 10; CpY; CpR 3; CpH; CpR 9; CpY; CpR 2; CpH; CpR 1;
     CpY; CpR 2; CpH; CpR 1; CpY; CpR 4; CpY; CpR 1; CpY; CpR 3; CpY; CpR 1;
     CpY; CpY],
     [34])`;;
let cf493 = new_definition
 `cf493 = ([CpH; CpR 10; CpH; CpR 3; CpH; CpR 13; CpH; CpR 13; CpY;
            CpR 11; CpH;
     CpR 1; CpY; CpR 10; CpH; CpR 1; CpY; CpR 9; CpH; CpR 1; CpY; CpR 8; CpH;
     CpR 1; CpY; CpR 8; CpH; CpR 8; CpY; CpY; CpY; CpR 4; CpY; CpR 2; CpY;
     CpR 3; CpY; CpY],
     [26; 27; 37])`;;
let cf494 = new_definition
 `cf494 = ([CpH; CpR 2; CpH; CpR 13; CpY; CpR 3; CpH; CpR 12; CpY; CpR 3; CpH;
     CpR 11; CpY; CpR 5; CpH; CpR 8; CpH; CpR 1; CpH; CpR 1; CpY; CpR 3; CpH;
     CpR 9; CpY; CpR 2; CpH; CpR 8; CpY; CpR 2; CpY; CpR 3; CpY; CpR 1; CpY;
     CpR 2; CpY; CpY; CpR 2; CpY],
     [37])`;;
let cf495 = new_definition
 `cf495 = ([CpH; CpR 12; CpH; CpR 1; CpY; CpR 11; CpH; CpR 1; CpY; CpR 10; CpH;
     CpR 1; CpY; CpR 9; CpH; CpR 1; CpY; CpR 6; CpH; CpR 3; CpH; CpR 9; CpH;
     CpR 9; CpY; CpR 8; CpH; CpR 8; CpY; CpR 2; CpY; CpR 3; CpY; CpY; CpR 3;
     CpY; CpY; CpR 2; CpY],
     [37])`;;
let cf496 = new_definition
 `cf496 = ([CpH; CpR 2; CpH; CpR 13; CpY; CpR 3; CpH; CpR 12; CpY; CpR 3; CpH;
     CpR 11; CpY; CpR 3; CpH; CpR 10; CpY; CpR 3; CpH; CpR 9; CpY; CpR 2;
     CpH; CpR 1; CpH; CpR 1; CpH; CpR 1; CpY; CpR 5; CpY; CpR 1; CpY; CpR 1;
     CpY; CpR 2; CpY; CpR 1; CpY; CpR 1; CpY],
     [35])`;;
let cf497 = new_definition
 `cf497 = ([CpH; CpR 11; CpH; CpR 1; CpH; CpR 1; CpY; CpR 5; CpH; CpR 10; CpH;
     CpR 1; CpH; CpR 1; CpY; CpR 4; CpH; CpR 10; CpH; CpR 1; CpY; CpR 3; CpH;
     CpR 10; CpY; CpR 2; CpY; CpR 3; CpY; CpR 1; CpY; CpR 1; CpY; CpR 3; CpY;
     CpR 4; CpY; CpR 2; CpY; CpR 1; CpY],
     [8])`;;
let cf498 = new_definition
 `cf498 = ([CpH; CpR 3; CpH; CpR 12; CpH; CpR 1; CpY; CpR 3; CpH; CpR 12; CpY;
     CpR 3; CpH; CpR 11; CpY; CpR 3; CpH; CpR 10; CpY; CpR 4; CpH; CpR 8;
     CpH; CpR 1; CpY; CpR 2; CpH; CpR 1; CpY; CpR 1; CpY; CpR 6; CpY; CpR 5;
     CpY; CpR 3; CpY; CpR 1; CpY; CpR 2; CpY],
     [29; 34; 36])`;;
let cf499 = new_definition
 `cf499 = ([CpH; CpR 11; CpH; CpR 1; CpH; CpR 1; CpY; CpR 5; CpH; CpR 10; CpH;
     CpR 1; CpH; CpR 1; CpY; CpR 3; CpH; CpR 11; CpY; CpR 4; CpH; CpR 9; CpH;
     CpR 1; CpY; CpR 2; CpY; CpR 3; CpY; CpR 1; CpY; CpR 6; CpY; CpR 3; CpY;
     CpR 3; CpY; CpR 3; CpY; CpR 1; CpY],
     [36])`;;
let cf500 = new_definition
 `cf500 = ([CpH; CpR 12; CpH; CpR 1; CpY; CpR 11; CpH; CpR 1; CpY; CpR 9; CpH;
     CpR 2; CpH; CpR 11; CpY; CpR 9; CpH; CpR 1; CpY; CpR 8; CpH; CpR 9; CpH;
     CpR 9; CpY; CpR 3; CpH; CpR 8; CpY; CpR 3; CpY; CpY; CpY; CpR 4; CpY;
     CpY; CpY],
     [34; 37])`;;
let cf501 = new_definition
 `cf501 = ([CpH; CpR 12; CpH; CpR 1; CpY; CpR 11; CpH; CpR 1; CpY; CpR 8; CpH;
     CpR 3; CpH; CpR 11; CpH; CpR 11; CpY; CpR 8; CpH; CpR 2; CpH; CpR 10;
     CpY; CpR 8; CpH; CpR 1; CpY; CpR 7; CpY; CpY; CpY; CpR 3; CpY; CpR 1;
     CpY; CpR 1; CpY; CpR 1; CpY],
     [33])`;;
let cf502 = new_definition
 `cf502 = ([CpH; CpR 11; CpH; CpR 1; CpH; CpR 1; CpY; CpR 3; CpH; CpR 12; CpY;
     CpR 6; CpH; CpR 8; CpH; CpR 1; CpH; CpR 1; CpH; CpR 1; CpY; CpR 3; CpH;
     CpR 10; CpY; CpR 2; CpY; CpR 3; CpY; CpR 1; CpY; CpR 1; CpY; CpR 1; CpY;
     CpR 2; CpY; CpR 1; CpY; CpR 1; CpY],
     [34])`;;
let cf503 = new_definition
 `cf503 = ([CpH; CpR 3; CpH; CpR 13; CpH; CpR 13; CpY; CpR 11; CpH; CpR 1; CpY;
     CpR 7; CpH; CpR 4; CpH; CpR 11; CpH; CpR 11; CpH; CpR 11; CpY; CpR 9;
     CpH; CpR 1; CpY; CpR 9; CpY; CpR 7; CpY; CpY; CpY; CpY; CpR 3; CpY;
     CpR 1; CpY; CpR 1; CpY],
     [34])`;;
let cf504 = new_definition
 `cf504 = ([CpH; CpR 11; CpH; CpR 1; CpH; CpR 1; CpY; CpR 3; CpH; CpR 12; CpY;
     CpR 3; CpH; CpR 11; CpY; CpR 3; CpH; CpR 3; CpH; CpR 9; CpH; CpR 1; CpY;
     CpR 2; CpY; CpR 3; CpY; CpR 3; CpH; CpR 1; CpY; CpR 5; CpY; CpR 1; CpY;
     CpR 1; CpY; CpR 2; CpY; CpR 1; CpY],
     [35])`;;
let cf505 = new_definition
 `cf505 = ([CpH; CpR 11; CpH; CpR 1; CpH; CpR 1; CpY; CpR 4; CpH; CpR 11; CpH;
     CpR 1; CpY; CpR 3; CpH; CpR 2; CpH; CpR 11; CpY; CpR 3; CpH; CpR 10;
     CpY; CpR 2; CpY; CpR 3; CpY; CpR 3; CpH; CpR 7; CpY; CpY; CpR 1; CpY;
     CpR 3; CpY; CpR 3; CpY; CpR 2; CpY],
     [8])`;;
let cf506 = new_definition
 `cf506 = ([CpH; CpR 2; CpH; CpR 13; CpY; CpR 4; CpH; CpR 11; CpH; CpR 1; CpY;
     CpR 3; CpH; CpR 11; CpY; CpR 5; CpH; CpR 8; CpH; CpR 1; CpH; CpR 1; CpY;
     CpR 3; CpH; CpR 9; CpY; CpR 3; CpY; CpR 2; CpY; CpR 4; CpY; CpY; CpR 3;
     CpY; CpR 3; CpY; CpY],
     [36])`;;
let cf507 = new_definition
 `cf507 = ([CpH; CpR 11; CpH; CpR 1; CpH; CpR 1; CpY; CpR 3; CpH; CpR 12; CpY;
     CpR 3; CpH; CpR 11; CpY; CpR 3; CpH; CpR 3; CpH; CpR 9; CpH; CpR 1; CpY;
     CpR 2; CpY; CpR 3; CpY; CpR 3; CpH; CpR 7; CpY; CpR 4; CpY; CpR 1; CpY;
     CpY; CpY; CpY],
     [37])`;;
let cf508 = new_definition
 `cf508 = ([CpH; CpR 10; CpH; CpR 1; CpY; CpR 3; CpH; CpR 10; CpY; CpR 3; CpH;
     CpR 9; CpY; CpR 3; CpH; CpR 8; CpY; CpR 3; CpH; CpR 1; CpY; CpR 3; CpY;
     CpR 3; CpH; CpR 2; CpH; CpR 5; CpY; CpH; CpR 1; CpY; CpR 3; CpY; CpR 1;
     CpY],
     [6])`;;
let cf509 = new_definition
 `cf509 = ([CpH; CpR 12; CpH; CpR 1; CpY; CpR 3; CpH; CpR 12; CpY; CpR 4; CpH;
     CpR 10; CpH; CpR 1; CpY; CpR 3; CpH; CpR 10; CpY; CpR 4; CpH; CpR 1;
     CpY; CpR 3; CpY; CpR 4; CpH; CpR 1; CpH; CpR 1; CpY; CpR 1; CpY; CpY;
     CpR 3; CpY; CpR 1; CpY; CpR 1; CpY],
     [35])`;;
let cf510 = new_definition
 `cf510 = ([CpH; CpR 12; CpH; CpR 1; CpY; CpR 11; CpH; CpR 10; CpH; CpR 2; CpH;
     CpR 12; CpY; CpR 10; CpH; CpR 1; CpY; CpR 8; CpH; CpR 2; CpH; CpR 10;
     CpY; CpR 9; CpY; CpR 4; CpY; CpY; CpY; CpR 3; CpH; CpR 1; CpY; CpR 1;
     CpY; CpY; CpY],
     [8; 9; 30; 37])`;;
let cf511 = new_definition
 `cf511 = ([CpH; CpR 2; CpH; CpR 13; CpY; CpR 11; CpH; CpR 1; CpY; CpR 10; CpH;
     CpR 1; CpY; CpR 9; CpH; CpR 7; CpH; CpR 3; CpH; CpR 10; CpH; CpR 10;
     CpY; CpR 9; CpY; CpR 5; CpH; CpR 1; CpY; CpR 1; CpY; CpY; CpR 3; CpY;
     CpR 1; CpY; CpR 2; CpY; CpY],
     [21; 25; 37])`;;
let cf512 = new_definition
 `cf512 = ([CpH; CpR 10; CpH; CpR 2; CpH; CpR 12; CpY; CpR 10; CpH; CpR 1; CpY;
     CpR 9; CpH; CpR 9; CpH; CpR 1; CpY; CpR 8; CpH; CpR 1; CpY; CpR 8; CpY;
     CpR 4; CpH; CpR 7; CpY; CpY; CpR 1; CpY; CpR 3; CpH; CpR 1; CpY; CpR 3;
     CpY; CpR 1; CpY],
     [31])`;;
let cf513 = new_definition
 `cf513 = ([CpH; CpR 2; CpH; CpR 13; CpY; CpR 4; CpH; CpR 11; CpH; CpR 1; CpY;
     CpR 3; CpH; CpR 11; CpY; CpR 5; CpH; CpR 8; CpH; CpR 1; CpH; CpR 1; CpY;
     CpR 3; CpH; CpR 1; CpY; CpR 8; CpH; CpR 8; CpY; CpY; CpR 1; CpY; CpR 4;
     CpY; CpR 4; CpY; CpR 1; CpY; CpR 2; CpY],
     [37; 39])`;;
let cf514 = new_definition
 `cf514 = ([CpH; CpR 2; CpH; CpR 12; CpY; CpR 5; CpH; CpR 9; CpH;
            CpR 1; CpH; CpR 1;
     CpY; CpR 5; CpH; CpR 8; CpH; CpR 1; CpH; CpR 1; CpY; CpR 3; CpH; CpR 9;
     CpY; CpR 4; CpH; CpR 1; CpY; CpR 7; CpY; CpR 1; CpY; CpR 4; CpY; CpY;
     CpR 1; CpY; CpY],
     [36])`;;
let cf515 = new_definition
 `cf515 = ([CpH; CpR 2; CpH; CpR 12; CpY; CpR 3; CpH; CpR 11; CpY; CpR 4; CpH;
     CpR 2; CpH; CpR 10; CpY; CpR 3; CpH; CpR 9; CpY; CpR 6; CpH; CpR 1; CpH;
     CpR 8; CpH; CpR 8; CpY; CpY; CpR 1; CpY; CpR 1; CpY; CpR 4; CpH; CpR 4;
     CpY; CpY; CpR 1; CpY],
     [34])`;;
let cf516 = new_definition
 `cf516 = ([CpH; CpR 12; CpH; CpR 1; CpY; CpR 11; CpH; CpR 1; CpY; CpR 10; CpH;
     CpR 8; CpH; CpR 3; CpH; CpR 11; CpH; CpR 11; CpY; CpR 2; CpH; CpR 10;
     CpY; CpR 8; CpH; CpR 1; CpH; CpR 1; CpY; CpR 1; CpY; CpR 1; CpY; CpR 1;
     CpY; CpR 4; CpH; CpR 1; CpY; CpR 3; CpY; CpR 1; CpY; CpR 1; CpY],
     [37])`;;
let cf517 = new_definition
 `cf517 = ([CpH; CpR 12; CpH; CpR 1; CpY; CpR 11; CpH; CpR 1; CpY; CpR 8; CpH;
     CpR 10; CpH; CpR 1; CpY; CpR 2; CpH; CpR 1; CpH; CpR 10; CpH; CpR 10;
     CpY; CpR 8; CpH; CpR 1; CpH; CpR 1; CpY; CpR 1; CpY; CpR 1; CpY; CpR 1;
     CpY; CpR 4; CpH; CpR 1; CpY; CpR 3; CpY; CpR 1; CpY; CpR 1; CpY],
     [37])`;;
let cf518 = new_definition
 `cf518 = ([CpH; CpR 11; CpH; CpR 1; CpY; CpR 9; CpH; CpR 10; CpH; CpR 1; CpY;
     CpR 8; CpH; CpR 1; CpH; CpR 9; CpH; CpR 1; CpY; CpR 2; CpH; CpR 9; CpY;
     CpY; CpY; CpR 4; CpH; CpR 1; CpH; CpR 1; CpH; CpR 1; CpY; CpH; CpR 5;
     CpY; CpR 4; CpY; CpR 1; CpY; CpR 1; CpY],
     [25])`;;
let cf519 = new_definition
 `cf519 = ([CpH; CpR 12; CpH; CpR 1; CpY; CpR 3; CpH; CpR 12; CpY; CpR 7; CpH;
     CpR 7; CpH; CpR 1; CpH; CpR 1; CpH; CpR 1; CpH; CpR 1; CpY; CpR 3; CpH;
     CpR 10; CpY; CpR 2; CpY; CpR 4; CpH; CpR 1; CpY; CpR 7; CpY; CpR 1; CpY;
     CpR 3; CpY; CpR 4; CpY; CpR 2; CpY; CpR 1; CpY],
     [6])`;;
let cf520 = new_definition
 `cf520 = ([CpH; CpR 2; CpH; CpR 12; CpY; CpR 10; CpH; CpR 1; CpY; CpR 7; CpH;
     CpR 3; CpH; CpR 10; CpH; CpR 10; CpY; CpR 7; CpH; CpR 2; CpH; CpR 9;
     CpY; CpR 8; CpY; CpR 6; CpY; CpY; CpY; CpR 3; CpY; CpR 1; CpY; CpR 1;
     CpY],
     [1; 2; 31])`;;
let cf521 = new_definition
 `cf521 = ([CpH; CpR 2; CpH; CpR 12; CpY; CpR 10; CpH; CpR 1; CpY; CpR 7; CpH;
     CpR 3; CpH; CpR 10; CpH; CpR 10; CpY; CpR 7; CpH; CpR 2; CpH; CpR 9;
     CpY; CpR 8; CpY; CpR 6; CpY; CpY; CpR 2; CpY; CpR 3; CpY; CpY; CpR 1;
     CpY],
     [2; 31])`;;
let cf522 = new_definition
 `cf522 = ([CpH; CpR 2; CpH; CpR 12; CpY; CpR 3; CpH; CpR 11; CpY; CpR 3; CpH;
     CpR 10; CpY; CpR 3; CpH; CpR 2; CpH; CpR 9; CpY; CpR 3; CpH; CpR 8; CpY;
     CpR 3; CpY; CpR 3; CpH; CpR 6; CpY; CpY; CpR 1; CpY; CpR 2; CpY; CpR 1;
     CpY],
     [31])`;;
let cf523 = new_definition
 `cf523 = ([CpH; CpR 10; CpH; CpR 1; CpY; CpR 8; CpH; CpR 2; CpH; CpR 10; CpY;
     CpR 8; CpH; CpR 1; CpY; CpR 7; CpH; CpR 1; CpY; CpR 6; CpH; CpR 1; CpH;
     CpR 1; CpY; CpH; CpR 6; CpY; CpR 2; CpY; CpY; CpR 3; CpY; CpY],
     [34])`;;
let cf524 = new_definition
 `cf524 = ([CpH; CpR 3; CpH; CpR 11; CpH; CpR 1; CpY; CpR 3; CpH; CpR 11; CpY;
     CpR 4; CpH; CpR 9; CpH; CpR 1; CpY; CpR 4; CpH; CpR 8; CpH; CpR 1; CpY;
     CpR 2; CpH; CpR 8; CpY; CpY; CpR 2; CpY; CpR 1; CpY; CpR 2; CpY; CpR 1;
     CpY; CpR 2; CpY],
     [3; 36])`;;
let cf525 = new_definition
 `cf525 = ([CpH; CpR 2; CpH; CpR 12; CpY; CpR 3; CpH; CpR 11; CpY; CpR 3; CpH;
     CpR 2; CpH; CpR 10; CpY; CpR 5; CpH; CpR 7; CpH; CpR 1; CpH; CpR 1; CpY;
     CpR 7; CpY; CpR 1; CpY; CpR 6; CpH; CpR 6; CpY; CpR 2; CpY; CpY; CpR 3;
     CpY; CpY],
     [35])`;;
let cf526 = new_definition
 `cf526 = ([CpH; CpR 11; CpH; CpR 1; CpY; CpR 9; CpH; CpR 2; CpH; CpR 11; CpY;
     CpR 9; CpH; CpR 1; CpY; CpR 5; CpH; CpR 1; CpH; CpR 1; CpH; CpR 2; CpH;
     CpR 9; CpY; CpR 6; CpY; CpR 1; CpY; CpY; CpY; CpR 4; CpY; CpY; CpY],
     [34])`;;
let cf527 = new_definition
 `cf527 = ([CpH; CpR 2; CpH; CpR 12; CpY; CpR 4; CpH; CpR 2; CpH; CpR 11; CpY;
     CpR 5; CpH; CpR 8; CpH; CpR 1; CpH; CpR 1; CpY; CpR 2; CpY; CpR 6; CpY;
     CpR 1; CpY; CpR 1; CpY; CpR 4; CpH; CpR 5; CpY; CpR 2; CpH; CpR 4; CpY;
     CpY; CpR 1; CpY],
     [27])`;;
let cf528 = new_definition
 `cf528 = ([CpH; CpR 10; CpH; CpR 1; CpY; CpR 3; CpH; CpR 10; CpY; CpR 4; CpH;
     CpR 2; CpH; CpR 9; CpY; CpR 2; CpH; CpR 1; CpY; CpR 5; CpH; CpR 7; CpH;
     CpR 7; CpY; CpR 1; CpH; CpR 1; CpY; CpR 2; CpY; CpY; CpY; CpR 2; CpY],
     [31])`;;
let cf529 = new_definition
 `cf529 = ([CpH; CpR 2; CpH; CpR 12; CpY; CpR 5; CpH; CpR 9; CpH;
            CpR 1; CpH; CpR 1;
     CpY; CpR 3; CpH; CpR 10; CpY; CpR 5; CpH; CpR 9; CpH; CpR 9; CpH; CpR 9;
     CpY; CpR 4; CpY; CpY; CpR 1; CpY; CpR 1; CpY; CpR 1; CpY; CpR 2; CpY;
     CpR 1; CpY],
     [35])`;;
let cf530 = new_definition
 `cf530 = ([CpH; CpR 11; CpH; CpR 1; CpY; CpR 10; CpH; CpR 1; CpY; CpR 8; CpH;
     CpR 2; CpH; CpR 10; CpY; CpR 8; CpH; CpR 1; CpY; CpR 7; CpH; CpR 1; CpY;
     CpR 7; CpH; CpR 1; CpY; CpH; CpR 6; CpY; CpR 2; CpY; CpY; CpR 3; CpY;
     CpY],
     [35])`;;
let cf531 = new_definition
 `cf531 = ([CpH; CpR 3; CpH; CpR 13; CpH; CpR 13; CpY; CpR 11; CpH; CpR 1; CpY;
     CpR 10; CpH; CpR 1; CpY; CpR 8; CpH; CpR 9; CpH; CpR 1; CpY; CpR 9; CpY;
     CpR 7; CpY; CpR 6; CpH; CpR 1; CpY; CpR 6; CpH; CpR 1; CpY; CpR 4; CpY;
     CpY; CpR 1; CpY; CpR 1; CpY],
     [34])`;;
let cf532 = new_definition
 `cf532 = ([CpH; CpR 12; CpH; CpR 1; CpY; CpR 10; CpH; CpR 2; CpH; CpR 12; CpY;
     CpR 10; CpH; CpR 1; CpY; CpR 9; CpH; CpR 1; CpY; CpR 6; CpH; CpR 1; CpH;
     CpR 1; CpH; CpR 1; CpY; CpR 6; CpY; CpR 1; CpY; CpY; CpY; CpR 4; CpY;
     CpY; CpY],
     [37])`;;
let cf533 = new_definition
 `cf533 = ([CpH; CpR 2; CpH; CpR 13; CpY; CpR 3; CpH; CpR 12; CpY; CpR 4; CpH;
     CpR 10; CpH; CpR 1; CpY; CpR 3; CpH; CpR 10; CpY; CpR 2; CpH; CpR 1;
     CpH; CpR 1; CpH; CpR 1; CpY; CpR 6; CpY; CpR 1; CpY; CpR 1; CpY; CpR 3;
     CpY; CpY; CpR 1; CpY; CpR 1; CpY],
     [12; 33; 37])`;;
let cf534 = new_definition
 `cf534 = ([CpH; CpR 4; CpH; CpR 13; CpH; CpR 13; CpH; CpR 13; CpY;
            CpR 11; CpH;
     CpR 1; CpY; CpR 10; CpH; CpR 1; CpY; CpR 9; CpH; CpR 9; CpH; CpR 1; CpY;
     CpR 9; CpY; CpR 6; CpY; CpR 1; CpY; CpR 5; CpH; CpR 1; CpY; CpR 4; CpY;
     CpY; CpR 1; CpY; CpR 1; CpY],
     [13; 20; 30])`;;
let cf535 = new_definition
 `cf535 = ([CpH; CpR 3; CpH; CpR 13; CpH; CpR 13; CpY; CpR 9; CpH; CpR 3; CpH;
     CpR 12; CpH; CpR 12; CpY; CpR 10; CpH; CpR 1; CpY; CpR 8; CpH; CpR 2;
     CpH; CpR 10; CpY; CpR 9; CpY; CpR 7; CpY; CpY; CpY; CpR 3; CpY; CpR 1;
     CpY; CpR 2; CpY; CpY],
     [7])`;;
let cf536 = new_definition
 `cf536 = ([CpH; CpR 11; CpH; CpR 2; CpH; CpR 13; CpY; CpR 10; CpH; CpR 2; CpH;
     CpR 12; CpY; CpR 10; CpH; CpR 1; CpY; CpR 9; CpH; CpR 1; CpY; CpR 8;
     CpH; CpR 1; CpY; CpR 8; CpH; CpR 8; CpY; CpY; CpY; CpY; CpR 2; CpY;
     CpR 2; CpY; CpR 1; CpY],
     [35])`;;
let cf537 = new_definition
 `cf537 = ([CpH; CpR 2; CpH; CpR 12; CpY; CpR 10; CpH; CpR 1; CpY; CpR 8; CpH;
     CpR 2; CpH; CpR 10; CpY; CpR 6; CpH; CpR 3; CpH; CpR 9; CpH; CpR 9; CpY;
     CpR 8; CpY; CpR 6; CpY; CpY; CpR 3; CpY; CpR 2; CpH; CpR 4; CpY; CpR 2;
     CpY; CpY],
     [6])`;;
let cf538 = new_definition
 `cf538 = ([CpH; CpR 2; CpH; CpR 12; CpY; CpR 5; CpH; CpR 9; CpH;
            CpR 1; CpH; CpR 1;
     CpY; CpR 3; CpH; CpR 10; CpY; CpR 3; CpH; CpR 9; CpY; CpR 3; CpH; CpR 8;
     CpY; CpR 3; CpY; CpR 1; CpY; CpR 2; CpY; CpR 3; CpH; CpR 4; CpY; CpY;
     CpR 1; CpY],
     [33])`;;
let cf539 = new_definition
 `cf539 = ([CpH; CpR 11; CpH; CpR 1; CpY; CpR 3; CpH; CpR 11; CpY; CpR 5; CpH;
     CpR 8; CpH; CpR 1; CpH; CpR 1; CpY; CpR 3; CpH; CpR 9; CpY; CpR 2; CpH;
     CpR 1; CpY; CpR 3; CpY; CpR 1; CpY; CpR 2; CpY; CpR 2; CpH; CpR 1; CpY;
     CpR 3; CpY; CpR 1; CpY],
     [6])`;;
let cf540 = new_definition
 `cf540 = ([CpH; CpR 10; CpH; CpR 1; CpH; CpR 1; CpY; CpR 3; CpH; CpR 11; CpY;
     CpR 3; CpH; CpR 10; CpY; CpR 5; CpH; CpR 7; CpH; CpR 1; CpH; CpR 1; CpY;
     CpR 2; CpY; CpR 3; CpY; CpR 3; CpH; CpR 1; CpY; CpR 4; CpY; CpR 1; CpY;
     CpR 1; CpY; CpR 2; CpY],
     [35])`;;
let cf541 = new_definition
 `cf541 = ([CpH; CpR 12; CpH; CpR 1; CpY; CpR 10; CpH; CpR 2; CpH; CpR 12; CpY;
     CpR 10; CpH; CpR 1; CpY; CpR 8; CpH; CpR 2; CpH; CpR 10; CpY; CpR 7;
     CpH; CpR 2; CpH; CpR 9; CpY; CpR 7; CpY; CpR 4; CpY; CpY; CpY; CpR 3;
     CpY; CpR 1; CpY; CpY],
     [37])`;;
let cf542 = new_definition
 `cf542 = ([CpH; CpR 3; CpH; CpR 12; CpH; CpR 1; CpY; CpR 3; CpH; CpR 12; CpY;
     CpR 4; CpH; CpR 10; CpH; CpR 1; CpY; CpR 3; CpH; CpR 10; CpY; CpR 4;
     CpH; CpR 9; CpH; CpR 9; CpY; CpR 3; CpY; CpR 2; CpY; CpY; CpR 1; CpY;
     CpR 1; CpY; CpR 2; CpY; CpR 1; CpY],
     [34])`;;
let cf543 = new_definition
 `cf543 = ([CpH; CpR 12; CpH; CpR 1; CpY; CpR 11; CpH; CpR 1; CpY; CpR 10; CpH;
     CpR 10; CpH; CpR 1; CpY; CpR 9; CpH; CpR 1; CpY; CpR 7; CpH; CpR 1; CpH;
     CpR 1; CpY; CpR 7; CpY; CpR 6; CpH; CpR 1; CpY; CpR 1; CpY; CpY; CpR 3;
     CpY; CpY; CpR 2; CpY],
     [34])`;;
let cf544 = new_definition
 `cf544 = ([CpH; CpR 10; CpH; CpR 1; CpH; CpR 1; CpH; CpR 1; CpY; CpR 3; CpH;
     CpR 12; CpY; CpR 5; CpH; CpR 9; CpH; CpR 1; CpH; CpR 1; CpY; CpR 3; CpH;
     CpR 10; CpY; CpR 2; CpY; CpR 4; CpY; CpY; CpR 1; CpY; CpR 1; CpY; CpR 1;
     CpY; CpR 2; CpY; CpR 1; CpY],
     [34])`;;
let cf545 = new_definition
 `cf545 = ([CpH; CpR 4; CpH; CpR 10; CpH; CpR 1; CpH; CpR 1; CpY; CpR 3; CpH;
     CpR 11; CpY; CpR 3; CpH; CpR 10; CpY; CpR 4; CpH; CpR 8; CpH; CpR 1;
     CpY; CpR 2; CpY; CpR 6; CpY; CpR 1; CpY; CpR 4; CpH; CpR 5; CpY; CpY;
     CpR 1; CpY; CpR 2; CpY],
     [4; 5; 36])`;;
let cf546 = new_definition
 `cf546 = ([CpH; CpR 5; CpH; CpR 13; CpH; CpR 13; CpH; CpR 13; CpH;
            CpR 13; CpY;
     CpR 11; CpH; CpR 1; CpY; CpR 7; CpH; CpR 4; CpH; CpR 11; CpH; CpR 11;
     CpH; CpR 11; CpY; CpR 10; CpY; CpR 6; CpY; CpR 1; CpY; CpR 1; CpY;
     CpR 3; CpY; CpR 1; CpY; CpY; CpR 1; CpY; CpR 1; CpY],
     [36])`;;
let cf547 = new_definition
 `cf547 = ([CpH; CpR 12; CpH; CpR 1; CpY; CpR 11; CpH; CpR 11; CpH; CpR 1; CpY;
     CpR 8; CpH; CpR 3; CpH; CpR 11; CpH; CpR 11; CpY; CpR 8; CpH; CpR 2;
     CpH; CpR 10; CpY; CpR 7; CpH; CpR 1; CpY; CpR 7; CpY; CpR 1; CpY; CpR 1;
     CpY; CpR 4; CpY; CpY; CpY; CpR 2; CpY],
     [34])`;;
let cf548 = new_definition
 `cf548 = ([CpH; CpR 2; CpH; CpR 13; CpY; CpR 6; CpH; CpR 9; CpH;
            CpR 1; CpH; CpR 1;
     CpH; CpR 1; CpY; CpR 3; CpH; CpR 11; CpY; CpR 5; CpH; CpR 10; CpH;
     CpR 10; CpH; CpR 10; CpY; CpR 4; CpY; CpY; CpR 1; CpY; CpR 1; CpY;
     CpR 1; CpY; CpR 2; CpY; CpR 1; CpY; CpR 1; CpY],
     [38])`;;
let cf549 = new_definition
 `cf549 = ([CpH; CpR 4; CpH; CpR 13; CpH; CpR 13; CpH; CpR 13; CpY;
            CpR 11; CpH;
     CpR 1; CpY; CpR 10; CpH; CpR 1; CpY; CpR 7; CpH; CpR 3; CpH; CpR 10;
     CpH; CpR 10; CpY; CpR 9; CpY; CpR 6; CpY; CpR 1; CpY; CpR 3; CpY; CpY;
     CpR 2; CpH; CpR 1; CpY; CpR 3; CpY; CpR 1; CpY],
     [33])`;;
let cf550 = new_definition
 `cf550 = ([CpH; CpR 2; CpH; CpR 13; CpY; CpR 11; CpH; CpR 1; CpY; CpR 10; CpH;
     CpR 1; CpY; CpR 7; CpH; CpR 9; CpH; CpR 1; CpY; CpR 9; CpY; CpR 7; CpY;
     CpR 7; CpH; CpR 7; CpH; CpR 7; CpH; CpR 2; CpH; CpR 7; CpY; CpR 2; CpY;
     CpY; CpR 3; CpY; CpR 1; CpY; CpR 1; CpY],
     [38])`;;
let cf551 = new_definition
 `cf551 = ([CpH; CpR 2; CpH; CpR 12; CpY; CpR 10; CpH; CpR 1; CpY; CpR 9; CpH;
     CpR 1; CpY; CpR 8; CpH; CpR 1; CpY; CpR 6; CpH; CpR 8; CpY; CpR 6; CpY;
     CpR 4; CpH; CpR 1; CpH; CpR 1; CpH; CpR 1; CpY; CpH; CpR 5; CpY; CpR 4;
     CpY; CpR 1; CpY; CpR 1; CpY],
     [6])`;;
let cf552 = new_definition
 `cf552 = ([CpH; CpR 2; CpH; CpR 13; CpY; CpR 3; CpH; CpR 12; CpY; CpR 4; CpH;
     CpR 10; CpH; CpR 1; CpY; CpR 6; CpH; CpR 7; CpH; CpR 1; CpH; CpR 1; CpH;
     CpR 1; CpY; CpR 2; CpY; CpR 8; CpH; CpR 8; CpY; CpR 7; CpY; CpR 1; CpY;
     CpR 1; CpY; CpR 3; CpY; CpY; CpR 2; CpY],
     [19; 20; 40])`;;
let cf553 = new_definition
 `cf553 = ([CpH; CpR 4; CpH; CpR 13; CpH; CpR 13; CpH; CpR 13; CpY;
            CpR 11; CpH;
     CpR 1; CpY; CpR 6; CpH; CpR 5; CpH; CpR 11; CpH; CpR 11; CpH; CpR 11;
     CpH; CpR 11; CpY; CpR 10; CpY; CpR 6; CpY; CpR 1; CpY; CpR 1; CpY;
     CpR 6; CpH; CpR 6; CpY; CpR 5; CpY; CpY; CpR 1; CpY; CpR 1; CpY],
     [36])`;;
let cf554 = new_definition
 `cf554 = ([CpH; CpR 12; CpH; CpR 1; CpY; CpR 11; CpH; CpR 1; CpY; CpR 10; CpH;
     CpR 1; CpY; CpR 9; CpH; CpR 1; CpY; CpR 5; CpH; CpR 1; CpH; CpR 3; CpH;
     CpR 9; CpH; CpR 9; CpY; CpR 2; CpH; CpR 8; CpY; CpR 7; CpH; CpR 1; CpY;
     CpR 1; CpY; CpR 2; CpY; CpR 3; CpY; CpY; CpR 1; CpY],
     [40])`;;
let cf555 = new_definition
 `cf555 = ([CpH; CpR 12; CpH; CpR 1; CpY; CpR 9; CpH; CpR 3; CpH; CpR 12; CpH;
     CpR 12; CpY; CpR 10; CpH; CpR 1; CpY; CpR 9; CpH; CpR 1; CpY; CpR 7;
     CpH; CpR 1; CpH; CpR 1; CpY; CpR 7; CpY; CpR 7; CpH; CpR 7; CpY; CpR 2;
     CpY; CpY; CpR 3; CpY; CpY; CpR 2; CpY],
     [37])`;;
let cf556 = new_definition
 `cf556 = ([CpH; CpR 10; CpH; CpR 1; CpY; CpR 7; CpH; CpR 3; CpH; CpR 10; CpH;
     CpR 10; CpY; CpR 8; CpH; CpR 1; CpY; CpR 6; CpH; CpR 2; CpH; CpR 8; CpY;
     CpR 6; CpY; CpY; CpY; CpR 4; CpY; CpY; CpY],
     [30])`;;
let cf557 = new_definition
 `cf557 = ([CpH; CpR 10; CpH; CpR 1; CpY; CpR 8; CpH; CpR 9; CpH;
            CpR 1; CpY; CpR 8;
     CpH; CpR 1; CpY; CpR 7; CpH; CpR 1; CpY; CpR 5; CpH; CpR 1; CpY; CpR 6;
     CpH; CpR 1; CpY; CpR 5; CpY; CpR 1; CpY; CpR 3; CpY; CpY],
     [10; 31])`;;
let cf558 = new_definition
 `cf558 = ([CpH; CpR 11; CpH; CpR 1; CpY; CpR 8; CpH; CpR 3; CpH; CpR 11; CpH;
     CpR 11; CpY; CpR 9; CpH; CpR 1; CpY; CpR 8; CpH; CpR 1; CpY; CpR 7; CpH;
     CpR 1; CpY; CpR 6; CpY; CpY; CpY; CpR 4; CpY; CpY; CpY],
     [27])`;;
let cf559 = new_definition
 `cf559 = ([CpH; CpR 2; CpH; CpR 12; CpY; CpR 10; CpH; CpR 1; CpY; CpR 8; CpH;
     CpR 9; CpH; CpR 1; CpY; CpR 8; CpH; CpR 1; CpY; CpR 8; CpY; CpR 5; CpH;
     CpR 1; CpY; CpR 6; CpH; CpR 1; CpY; CpR 4; CpY; CpR 1; CpY; CpR 1; CpY;
     CpR 2; CpY],
     [32])`;;
let cf560 = new_definition
 `cf560 = ([CpH; CpR 2; CpH; CpR 11; CpY; CpR 9; CpH; CpR 1; CpY;
            CpR 7; CpH; CpR 2;
     CpH; CpR 9; CpY; CpR 7; CpH; CpR 1; CpY; CpR 3; CpY; CpY; CpR 3; CpH;
     CpR 1; CpH; CpR 1; CpY; CpH; CpR 4; CpY; CpY; CpR 1; CpY],
     [23])`;;
let cf561 = new_definition
 `cf561 = ([CpH; CpR 10; CpH; CpR 1; CpY; CpR 8; CpH; CpR 2; CpH; CpR 10; CpY;
     CpR 8; CpH; CpR 1; CpY; CpR 5; CpH; CpR 3; CpH; CpR 8; CpH; CpR 8; CpY;
     CpR 6; CpY; CpY; CpR 2; CpH; CpR 1; CpY; CpR 2; CpY; CpY; CpY],
     [29])`;;
let cf562 = new_definition
 `cf562 = ([CpH; CpR 2; CpH; CpR 13; CpY; CpR 11; CpH; CpR 1; CpY; CpR 10; CpH;
     CpR 1; CpY; CpR 9; CpH; CpR 9; CpH; CpR 1; CpY; CpR 8; CpH; CpR 1; CpY;
     CpR 8; CpY; CpR 6; CpY; CpR 4; CpY; CpR 2; CpH; CpR 1; CpY; CpR 4; CpY;
     CpR 1; CpY; CpR 2; CpY],
     [33])`;;
let cf563 = new_definition
 `cf563 = ([CpH; CpR 2; CpH; CpR 13; CpY; CpR 3; CpH; CpR 2; CpH; CpR 12; CpY;
     CpR 3; CpH; CpR 11; CpY; CpR 3; CpH; CpR 2; CpH; CpR 10; CpY; CpR 2;
     CpY; CpR 7; CpH; CpR 1; CpY; CpR 6; CpY; CpR 1; CpY; CpR 1; CpY; CpR 4;
     CpH; CpR 4; CpY; CpY; CpR 1; CpY],
     [31])`;;
let cf564 = new_definition
 `cf564 = ([CpH; CpR 12; CpH; CpR 1; CpY; CpR 11; CpH; CpR 1; CpY; CpR 10; CpH;
     CpR 10; CpH; CpR 1; CpY; CpR 9; CpH; CpR 1; CpY; CpR 7; CpH; CpR 1; CpH;
     CpR 1; CpY; CpR 7; CpY; CpR 6; CpH; CpR 7; CpY; CpR 3; CpY; CpY; CpY;
     CpR 3; CpY; CpY],
     [8; 9; 34])`;;
let cf565 = new_definition
 `cf565 = ([CpH; CpR 2; CpH; CpR 12; CpY; CpR 8; CpH; CpR 3; CpH; CpR 11; CpH;
     CpR 11; CpY; CpR 9; CpH; CpR 1; CpY; CpR 7; CpH; CpR 2; CpH; CpR 9; CpY;
     CpR 8; CpY; CpR 6; CpH; CpR 7; CpY; CpY; CpR 1; CpY; CpR 4; CpH; CpR 4;
     CpY; CpY; CpR 1; CpY],
     [34])`;;
let cf566 = new_definition
 `cf566 = ([CpH; CpR 11; CpH; CpR 1; CpY; CpR 9; CpH; CpR 2; CpH; CpR 11; CpY;
     CpR 9; CpH; CpR 1; CpY; CpR 8; CpH; CpR 1; CpY; CpR 8; CpH; CpR 1; CpY;
     CpR 6; CpH; CpR 1; CpH; CpR 1; CpY; CpH; CpR 6; CpY; CpR 5; CpY; CpY;
     CpR 1; CpY; CpR 1; CpY],
     [17])`;;
let cf567 = new_definition
 `cf567 = ([CpH; CpR 2; CpH; CpR 9; CpY; CpR 7; CpH; CpR 1; CpY;
            CpR 7; CpH; CpR 7;
     CpH; CpR 7; CpH; CpR 7; CpH; CpR 7; CpY; CpR 5; CpY; CpY; CpY; CpY; CpY],
     [6])`;;
let cf568 = new_definition
 `cf568 = ([CpH; CpR 8; CpH; CpR 2; CpH; CpR 10; CpY; CpR 8; CpH;
            CpR 6; CpH; CpR 3;
     CpH; CpR 9; CpH; CpR 9; CpY; CpR 8; CpH; CpR 8; CpY; CpY; CpY; CpY; CpY;
     CpY; CpY],
     [24])`;;
let cf569 = new_definition
 `cf569 = ([CpH; CpR 6; CpH; CpR 4; CpH; CpR 10; CpH; CpR 10; CpH; CpR 10; CpY;
     CpR 7; CpH; CpR 9; CpH; CpR 9; CpH; CpR 9; CpY; CpY; CpY; CpY; CpY;
     CpR 4; CpH; CpR 1; CpY; CpR 3; CpY; CpR 1; CpY],
     [23])`;;
let cf570 = new_definition
 `cf570 = ([CpH; CpR 9; CpH; CpR 1; CpY; CpR 3; CpH; CpR 9; CpY;
            CpR 6; CpH; CpR 5;
     CpH; CpR 1; CpH; CpR 1; CpH; CpR 1; CpY; CpR 2; CpY; CpR 3; CpY; CpR 1;
     CpY; CpR 1; CpY; CpR 1; CpY; CpR 2; CpY],
     [27])`;;
let cf571 = new_definition
 `cf571 = ([CpH; CpR 9; CpH; CpR 1; CpY; CpR 3; CpH; CpR 9; CpY;
            CpR 5; CpH; CpR 6;
     CpH; CpR 1; CpH; CpR 1; CpY; CpR 2; CpH; CpR 1; CpY; CpR 3; CpY; CpR 1;
     CpY; CpR 1; CpY; CpR 3; CpY; CpY],
     [27])`;;
let cf572 = new_definition
 `cf572 = ([CpH; CpR 2; CpH; CpR 10; CpY; CpR 8; CpH; CpR 1; CpY;
            CpR 4; CpH; CpR 8;
     CpY; CpR 5; CpH; CpR 1; CpY; CpR 6; CpH; CpR 1; CpY; CpR 5; CpH; CpR 1;
     CpY; CpR 4; CpH; CpR 1; CpY; CpR 3; CpY; CpR 1; CpY],
     [6])`;;
let cf573 = new_definition
 `cf573 = ([CpH; CpR 7; CpH; CpR 4; CpH; CpR 11; CpH; CpR 11; CpH; CpR 11; CpY;
     CpR 8; CpH; CpR 9; CpH; CpR 1; CpY; CpR 9; CpH; CpR 9; CpY; CpY; CpY;
     CpY; CpY; CpR 4; CpH; CpR 1; CpY; CpR 3; CpY; CpR 1; CpY],
     [24])`;;
let cf574 = new_definition
 `cf574 = ([CpH; CpR 3; CpH; CpR 10; CpH; CpR 1; CpY; CpR 7; CpH; CpR 10; CpH;
     CpR 2; CpH; CpR 10; CpY; CpR 2; CpH; CpR 9; CpY; CpY; CpR 6; CpH; CpR 1;
     CpH; CpR 1; CpY; CpR 2; CpY; CpR 1; CpY; CpR 2; CpH; CpR 1; CpY; CpR 1;
     CpY; CpY],
     [33])`;;
let cf575 = new_definition
 `cf575 = ([CpH; CpR 2; CpH; CpR 11; CpY; CpR 9; CpH; CpR 1; CpY;
            CpR 6; CpH; CpR 3;
     CpH; CpR 9; CpH; CpR 9; CpY; CpR 7; CpH; CpR 1; CpY; CpR 7; CpY; CpR 5;
     CpY; CpY; CpY; CpR 2; CpY; CpR 2; CpY],
     [12; 13; 28])`;;
let cf576 = new_definition
 `cf576 = ([CpH; CpR 10; CpH; CpR 1; CpY; CpR 3; CpH; CpR 10; CpY; CpR 3; CpH;
     CpR 9; CpY; CpR 5; CpH; CpR 6; CpH; CpR 1; CpH; CpR 1; CpY; CpR 2; CpY;
     CpR 3; CpY; CpR 1; CpY; CpR 1; CpY; CpR 1; CpY; CpR 2; CpY],
     [27])`;;
let cf577 = new_definition
 `cf577 = ([CpH; CpR 2; CpH; CpR 11; CpY; CpR 9; CpH; CpR 1; CpY;
            CpR 4; CpH; CpR 5;
     CpH; CpR 9; CpH; CpR 9; CpH; CpR 9; CpH; CpR 9; CpY; CpR 8; CpY; CpR 6;
     CpY; CpY; CpY; CpY; CpR 3; CpY; CpR 1; CpY],
     [6])`;;
let cf578 = new_definition
 `cf578 = ([CpH; CpR 2; CpH; CpR 11; CpY; CpR 9; CpH; CpR 1; CpY;
            CpR 6; CpH; CpR 3;
     CpH; CpR 9; CpH; CpR 9; CpY; CpR 7; CpH; CpR 8; CpY; CpR 6; CpY; CpY;
     CpY; CpR 4; CpH; CpR 4; CpY; CpR 2; CpY; CpY],
     [6])`;;
let cf579 = new_definition
 `cf579 = ([CpH; CpR 2; CpH; CpR 11; CpY; CpR 4; CpH; CpR 9; CpH;
            CpR 1; CpY; CpR 5;
     CpH; CpR 7; CpH; CpR 1; CpH; CpR 1; CpY; CpR 3; CpH; CpR 8; CpY; CpR 3;
     CpY; CpR 1; CpY; CpR 1; CpY; CpR 1; CpY; CpR 2; CpY; CpR 1; CpY],
     [30])`;;
let cf580 = new_definition
 `cf580 = ([CpH; CpR 2; CpH; CpR 11; CpY; CpR 9; CpH; CpR 1; CpY;
            CpR 7; CpH; CpR 2;
     CpH; CpR 9; CpY; CpR 6; CpH; CpR 8; CpY; CpR 6; CpY; CpY; CpR 5; CpH;
     CpR 1; CpY; CpR 4; CpH; CpR 1; CpY; CpR 3; CpY; CpR 1; CpY],
     [6])`;;
let cf581 = new_definition
 `cf581 = ([CpH; CpR 9; CpH; CpR 1; CpH; CpR 1; CpY; CpR 4; CpH;
            CpR 9; CpH; CpR 1;
     CpY; CpR 4; CpH; CpR 8; CpH; CpR 1; CpY; CpR 2; CpH; CpR 1; CpY; CpR 3;
     CpY; CpR 1; CpY; CpR 1; CpY; CpR 1; CpY; CpR 3; CpY; CpY],
     [31])`;;
let cf582 = new_definition
 `cf582 = ([CpH; CpR 2; CpH; CpR 11; CpY; CpR 9; CpH; CpR 1; CpY;
            CpR 8; CpH; CpR 1;
     CpY; CpR 5; CpH; CpR 8; CpY; CpR 6; CpY; CpR 6; CpH; CpR 1; CpY; CpR 5;
     CpH; CpR 1; CpY; CpR 4; CpH; CpR 1; CpY; CpR 3; CpY; CpR 1; CpY],
     [6])`;;
let cf583 = new_definition
 `cf583 = ([CpH; CpR 2; CpH; CpR 10; CpY; CpR 8; CpH; CpR 1; CpY;
            CpR 4; CpH; CpR 8;
     CpY; CpR 5; CpH; CpR 1; CpY; CpR 6; CpH; CpR 1; CpY; CpR 4; CpH; CpR 1;
     CpH; CpR 1; CpY; CpH; CpR 4; CpY; CpY; CpR 1; CpY],
     [6])`;;
let cf584 = new_definition
 `cf584 = ([CpH; CpR 2; CpH; CpR 12; CpY; CpR 3; CpH; CpR 11; CpY; CpR 4; CpH;
     CpR 9; CpH; CpR 1; CpY; CpR 3; CpH; CpR 2; CpH; CpR 9; CpY; CpR 2; CpY;
     CpR 6; CpH; CpR 1; CpY; CpR 6; CpY; CpR 1; CpY; CpR 2; CpY; CpR 3; CpY;
     CpY],
     [8; 9; 33])`;;
let cf585 = new_definition
 `cf585 = ([CpH; CpR 2; CpH; CpR 12; CpY; CpR 10; CpH; CpR 1; CpY; CpR 9; CpH;
     CpR 1; CpY; CpR 5; CpH; CpR 4; CpH; CpR 9; CpH; CpR 9; CpH; CpR 9; CpY;
     CpR 8; CpY; CpR 6; CpY; CpY; CpY; CpY; CpR 3; CpY; CpR 1; CpY],
     [30])`;;
let cf586 = new_definition
 `cf586 = ([CpH; CpR 3; CpH; CpR 12; CpH; CpR 12; CpY; CpR 10; CpH; CpR 1; CpY;
     CpR 7; CpH; CpR 3; CpH; CpR 10; CpH; CpR 10; CpY; CpR 8; CpH; CpR 1;
     CpY; CpR 8; CpY; CpR 6; CpY; CpY; CpY; CpY; CpR 2; CpY; CpR 2; CpY],
     [30])`;;
let cf587 = new_definition
 `cf587 = ([CpH; CpR 2; CpH; CpR 12; CpY; CpR 10; CpH; CpR 1; CpY; CpR 9; CpH;
     CpR 1; CpY; CpR 7; CpH; CpR 2; CpH; CpR 9; CpY; CpR 7; CpH; CpR 8; CpY;
     CpR 6; CpY; CpY; CpY; CpR 4; CpH; CpR 4; CpY; CpR 2; CpY; CpY],
     [27])`;;
let cf588 = new_definition
 `cf588 = ([CpH; CpR 2; CpH; CpR 12; CpY; CpR 10; CpH; CpR 1; CpY; CpR 9; CpH;
     CpR 1; CpY; CpR 8; CpH; CpR 7; CpH; CpR 2; CpH; CpR 9; CpY; CpR 8; CpY;
     CpR 6; CpY; CpR 6; CpH; CpR 6; CpY; CpR 2; CpY; CpY; CpR 2; CpY; CpR 2;
     CpY],
     [24])`;;
let cf589 = new_definition
 `cf589 = ([CpH; CpR 11; CpH; CpR 1; CpY; CpR 3; CpH; CpR 11; CpY; CpR 3; CpH;
     CpR 10; CpY; CpR 3; CpH; CpR 9; CpY; CpR 3; CpH; CpR 1; CpH; CpR 1; CpY;
     CpR 3; CpY; CpR 3; CpH; CpR 1; CpY; CpR 4; CpY; CpR 1; CpY; CpR 1; CpY;
     CpR 2; CpY],
     [16; 17; 31])`;;
let cf590 = new_definition
 `cf590 = ([CpH; CpR 3; CpH; CpR 12; CpH; CpR 12; CpY; CpR 7; CpH; CpR 4; CpH;
     CpR 11; CpH; CpR 11; CpH; CpR 11; CpY; CpR 8; CpH; CpR 2; CpH; CpR 10;
     CpY; CpR 9; CpY; CpR 7; CpY; CpY; CpY; CpY; CpR 3; CpY; CpR 2; CpY; CpY],
     [7])`;;
let cf591 = new_definition
 `cf591 = ([CpH; CpR 2; CpH; CpR 11; CpY; CpR 9; CpH; CpR 1; CpY;
            CpR 7; CpH; CpR 2;
     CpH; CpR 9; CpY; CpR 8; CpH; CpR 8; CpH; CpR 8; CpH; CpR 8; CpY; CpR 6;
     CpY; CpY; CpR 4; CpH; CpR 5; CpY; CpR 3; CpY; CpY; CpY],
     [6])`;;
let cf592 = new_definition
 `cf592 = ([CpH; CpR 2; CpH; CpR 11; CpY; CpR 9; CpH; CpR 1; CpY;
            CpR 8; CpH; CpR 1;
     CpY; CpR 5; CpH; CpR 8; CpY; CpR 6; CpY; CpR 6; CpH; CpR 1; CpY; CpR 4;
     CpH; CpR 1; CpH; CpR 1; CpY; CpH; CpR 4; CpY; CpY; CpR 1; CpY],
     [6])`;;
let cf593 = new_definition
 `cf593 = ([CpH; CpR 11; CpH; CpR 1; CpY; CpR 10; CpH; CpR 1; CpY; CpR 8; CpH;
     CpR 2; CpH; CpR 10; CpY; CpR 7; CpH; CpR 8; CpH; CpR 1; CpY; CpR 7; CpY;
     CpR 5; CpH; CpR 7; CpH; CpR 7; CpY; CpY; CpR 1; CpY; CpR 2; CpY; CpR 2;
     CpY; CpY],
     [15])`;;
let cf594 = new_definition
 `cf594 = ([CpH; CpR 2; CpH; CpR 12; CpY; CpR 10; CpH; CpR 1; CpY; CpR 9; CpH;
     CpR 1; CpY; CpR 5; CpH; CpR 9; CpY; CpR 3; CpH; CpR 1; CpH; CpR 1; CpH;
     CpR 1; CpY; CpR 1; CpY; CpY; CpY; CpR 4; CpH; CpR 4; CpY; CpR 2; CpY;
     CpY],
     [6])`;;
let cf595 = new_definition
 `cf595 = ([CpH; CpR 2; CpH; CpR 12; CpY; CpR 3; CpH; CpR 2; CpH; CpR 11; CpY;
     CpR 4; CpH; CpR 1; CpH; CpR 8; CpH; CpR 1; CpH; CpR 1; CpY; CpR 3; CpH;
     CpR 9; CpH; CpR 9; CpY; CpR 1; CpH; CpR 1; CpY; CpR 1; CpY; CpY; CpR 1;
     CpY; CpR 1; CpY; CpR 2; CpY; CpR 1; CpY],
     [41])`;;
let cf596 = new_definition
 `cf596 = ([CpH; CpR 2; CpH; CpR 12; CpY; CpR 10; CpH; CpR 1; CpY; CpR 9; CpH;
     CpR 1; CpY; CpR 8; CpH; CpR 1; CpY; CpR 6; CpH; CpR 8; CpY; CpR 6; CpY;
     CpY; CpR 4; CpH; CpR 1; CpH; CpR 1; CpY; CpH; CpR 4; CpY; CpY; CpR 1;
     CpY],
     [16; 17; 24])`;;
let cf597 = new_definition
 `cf597 = ([CpH; CpR 2; CpH; CpR 13; CpY; CpR 11; CpH; CpR 1; CpY; CpR 10; CpH;
     CpR 1; CpY; CpR 9; CpH; CpR 9; CpH; CpR 1; CpY; CpR 8; CpH; CpR 9; CpY;
     CpR 5; CpH; CpR 1; CpY; CpR 1; CpY; CpY; CpR 4; CpH; CpR 5; CpY; CpR 3;
     CpY; CpY; CpY],
     [19; 20; 36])`;;
let cf598 = new_definition
 `cf598 = ([CpH; CpR 2; CpH; CpR 11; CpY; CpR 6; CpH; CpR 7; CpH;
            CpR 1; CpH; CpR 1;
     CpH; CpR 1; CpY; CpR 3; CpH; CpR 9; CpY; CpR 3; CpH; CpR 8; CpY; CpR 3;
     CpY; CpR 1; CpY; CpR 1; CpY; CpR 1; CpY; CpR 2; CpY; CpR 1; CpY],
     [31])`;;
let cf599 = new_definition
 `cf599 = ([CpH; CpR 10; CpH; CpR 1; CpY; CpR 3; CpH; CpR 10; CpY; CpR 5; CpH;
     CpR 2; CpH; CpR 9; CpY; CpR 2; CpY; CpR 4; CpH; CpR 7; CpY; CpR 2; CpH;
     CpR 6; CpY; CpR 2; CpH; CpR 5; CpY; CpR 2; CpY; CpY; CpR 2; CpY],
     [30])`;;
let cf600 = new_definition
 `cf600 = ([CpH; CpR 10; CpH; CpR 1; CpY; CpR 3; CpH; CpR 10; CpY; CpR 4; CpH;
     CpR 2; CpH; CpR 9; CpY; CpR 2; CpH; CpR 1; CpY; CpR 4; CpH; CpR 7; CpY;
     CpR 2; CpH; CpR 6; CpY; CpR 2; CpY; CpY; CpR 3; CpY; CpY],
     [31])`;;
let cf601 = new_definition
 `cf601 = ([CpH; CpR 2; CpH; CpR 12; CpY; CpR 10; CpH; CpR 1; CpY; CpR 6; CpH;
     CpR 4; CpH; CpR 10; CpH; CpR 10; CpH; CpR 10; CpY; CpR 8; CpH; CpR 1;
     CpY; CpR 8; CpY; CpR 6; CpY; CpY; CpY; CpR 2; CpY; CpR 2; CpY; CpR 1;
     CpY],
     [1; 2; 26; 32])`;;
let cf602 = new_definition
 `cf602 = ([CpH; CpR 11; CpH; CpR 1; CpY; CpR 3; CpH; CpR 11; CpY; CpR 5; CpH;
     CpR 8; CpH; CpR 1; CpH; CpR 1; CpY; CpR 3; CpH; CpR 9; CpY; CpR 2; CpH;
     CpR 1; CpY; CpR 3; CpY; CpR 1; CpY; CpR 1; CpY; CpR 4; CpY; CpR 3; CpY;
     CpR 1; CpY],
     [31])`;;
let cf603 = new_definition
 `cf603 = ([CpH; CpR 2; CpH; CpR 12; CpY; CpR 3; CpH; CpR 11; CpY; CpR 5; CpH;
     CpR 8; CpH; CpR 1; CpH; CpR 1; CpY; CpR 3; CpH; CpR 9; CpY; CpR 3; CpH;
     CpR 8; CpY; CpR 3; CpY; CpR 1; CpY; CpR 1; CpY; CpR 1; CpY; CpR 2; CpY;
     CpR 1; CpY],
     [31])`;;
let cf604 = new_definition
 `cf604 = ([CpH; CpR 11; CpH; CpR 1; CpY; CpR 3; CpH; CpR 11; CpY; CpR 3; CpH;
     CpR 10; CpY; CpR 4; CpH; CpR 2; CpH; CpR 9; CpY; CpR 2; CpY; CpR 3; CpY;
     CpR 2; CpH; CpR 6; CpY; CpR 2; CpH; CpR 5; CpY; CpR 2; CpY; CpY; CpR 2;
     CpY],
     [31])`;;
let cf605 = new_definition
 `cf605 = ([CpH; CpR 2; CpH; CpR 12; CpY; CpR 10; CpH; CpR 1; CpY; CpR 7; CpH;
     CpR 3; CpH; CpR 10; CpH; CpR 10; CpY; CpR 7; CpH; CpR 9; CpY; CpR 7;
     CpY; CpY; CpY; CpR 4; CpH; CpR 5; CpY; CpR 2; CpH; CpR 4; CpY; CpR 2;
     CpY; CpY],
     [6])`;;
let cf606 = new_definition
 `cf606 = ([CpH; CpR 2; CpH; CpR 11; CpY; CpR 5; CpH; CpR 8; CpH;
            CpR 1; CpH; CpR 1;
     CpY; CpR 3; CpH; CpR 9; CpY; CpR 4; CpH; CpR 7; CpH; CpR 1; CpY; CpR 3;
     CpY; CpR 1; CpY; CpR 1; CpY; CpR 4; CpH; CpR 4; CpY; CpY; CpR 1; CpY],
     [30])`;;
let cf607 = new_definition
 `cf607 = ([CpH; CpR 11; CpH; CpR 1; CpY; CpR 3; CpH; CpR 11; CpY; CpR 4; CpH;
     CpR 2; CpH; CpR 10; CpY; CpR 3; CpH; CpR 1; CpY; CpR 4; CpH; CpR 8; CpY;
     CpR 2; CpH; CpR 7; CpY; CpR 2; CpY; CpY; CpR 2; CpH; CpR 1; CpY; CpR 1;
     CpY; CpY],
     [31])`;;
let cf608 = new_definition
 `cf608 = ([CpH; CpR 2; CpH; CpR 12; CpY; CpR 5; CpH; CpR 9; CpH;
            CpR 1; CpH; CpR 1;
     CpY; CpR 3; CpH; CpR 2; CpH; CpR 10; CpY; CpR 3; CpH; CpR 9; CpY; CpR 3;
     CpY; CpR 1; CpY; CpR 3; CpH; CpR 6; CpY; CpY; CpR 1; CpY; CpR 2; CpY;
     CpR 1; CpY],
     [35])`;;
let cf609 = new_definition
 `cf609 = ([CpH; CpR 11; CpH; CpR 1; CpY; CpR 3; CpH; CpR 11; CpY; CpR 4; CpH;
     CpR 9; CpH; CpR 1; CpY; CpR 3; CpH; CpR 9; CpY; CpR 3; CpH; CpR 1; CpY;
     CpR 3; CpY; CpR 1; CpY; CpR 4; CpH; CpR 1; CpY; CpH; CpR 4; CpY; CpY;
     CpR 1; CpY],
     [27])`;;
let cf610 = new_definition
 `cf610 = ([CpH; CpR 10; CpH; CpR 1; CpY; CpR 3; CpH; CpR 10; CpY; CpR 4; CpH;
     CpR 8; CpH; CpR 1; CpY; CpR 2; CpH; CpR 1; CpH; CpR 1; CpH; CpR 1; CpY;
     CpR 3; CpY; CpR 1; CpY; CpR 5; CpY; CpR 3; CpH; CpR 1; CpY; CpR 1; CpY;
     CpY],
     [29])`;;
let cf611 = new_definition
 `cf611 = ([CpH; CpR 10; CpH; CpR 1; CpY; CpR 3; CpH; CpR 10; CpY; CpR 4; CpH;
     CpR 8; CpH; CpR 1; CpY; CpR 3; CpH; CpR 8; CpY; CpR 6; CpY; CpR 1; CpY;
     CpR 3; CpH; CpR 1; CpH; CpR 1; CpY; CpH; CpR 4; CpY; CpY; CpR 1; CpY],
     [23])`;;
let cf612 = new_definition
 `cf612 = ([CpH; CpR 11; CpH; CpR 1; CpY; CpR 4; CpH; CpR 10; CpH; CpR 1; CpY;
     CpR 3; CpH; CpR 10; CpY; CpR 5; CpH; CpR 1; CpY; CpR 4; CpY; CpY; CpR 2;
     CpH; CpR 1; CpH; CpR 1; CpH; CpR 1; CpY; CpR 1; CpY; CpY; CpY; CpY],
     [23])`;;
let cf613 = new_definition
 `cf613 = ([CpH; CpR 12; CpH; CpR 1; CpY; CpR 3; CpH; CpR 12; CpY; CpR 3; CpH;
     CpR 11; CpY; CpR 3; CpH; CpR 10; CpY; CpR 3; CpH; CpR 2; CpH; CpR 9;
     CpY; CpR 2; CpY; CpR 3; CpY; CpR 3; CpH; CpR 1; CpY; CpR 4; CpY; CpR 1;
     CpY; CpR 1; CpY; CpR 2; CpY],
     [16; 17; 32])`;;
let cf614 = new_definition
 `cf614 = ([CpH; CpR 3; CpH; CpR 13; CpH; CpR 13; CpY; CpR 10; CpH; CpR 2; CpH;
     CpR 12; CpY; CpR 8; CpH; CpR 3; CpH; CpR 11; CpH; CpR 11; CpY; CpR 9;
     CpH; CpR 1; CpY; CpR 9; CpY; CpR 7; CpY; CpY; CpY; CpY; CpR 2; CpY;
     CpR 2; CpY; CpR 1; CpY],
     [11; 12; 33])`;;
let cf615 = new_definition
 `cf615 = ([CpH; CpR 2; CpH; CpR 13; CpY; CpR 11; CpH; CpR 1; CpY; CpR 9; CpH;
     CpR 2; CpH; CpR 11; CpY; CpR 8; CpH; CpR 2; CpH; CpR 10; CpY; CpR 8;
     CpH; CpR 1; CpY; CpR 5; CpY; CpY; CpR 3; CpH; CpR 6; CpY; CpR 3; CpY;
     CpY; CpY; CpR 2; CpY],
     [12; 13; 30; 36])`;;
let cf616 = new_definition
 `cf616 = ([CpH; CpR 11; CpH; CpR 1; CpY; CpR 3; CpH; CpR 11; CpY; CpR 4; CpH;
     CpR 9; CpH; CpR 1; CpY; CpR 3; CpH; CpR 9; CpY; CpR 2; CpH; CpR 1; CpH;
     CpR 1; CpY; CpR 3; CpY; CpR 1; CpY; CpR 5; CpY; CpR 4; CpH; CpR 1; CpY;
     CpR 3; CpY; CpR 1; CpY],
     [30])`;;
let cf617 = new_definition
 `cf617 = ([CpH; CpR 2; CpH; CpR 12; CpY; CpR 3; CpH; CpR 11; CpY; CpR 4; CpH;
     CpR 9; CpH; CpR 1; CpY; CpR 3; CpH; CpR 9; CpY; CpR 4; CpH; CpR 7; CpH;
     CpR 1; CpY; CpR 3; CpY; CpR 1; CpY; CpR 1; CpY; CpR 4; CpH; CpR 4; CpY;
     CpY; CpR 1; CpY],
     [30])`;;
let cf618 = new_definition
 `cf618 = ([CpH; CpR 2; CpH; CpR 13; CpY; CpR 3; CpH; CpR 12; CpY; CpR 5; CpH;
     CpR 9; CpH; CpR 1; CpH; CpR 1; CpY; CpR 3; CpH; CpR 10; CpY; CpR 4; CpH;
     CpR 9; CpH; CpR 9; CpY; CpR 3; CpY; CpR 1; CpY; CpR 1; CpY; CpR 1; CpY;
     CpR 1; CpY; CpR 2; CpY; CpR 1; CpY],
     [35])`;;
let cf619 = new_definition
 `cf619 = ([CpH; CpR 12; CpH; CpR 1; CpY; CpR 3; CpH; CpR 12; CpY; CpR 4; CpH;
     CpR 10; CpH; CpR 1; CpY; CpR 3; CpH; CpR 2; CpH; CpR 10; CpY; CpR 2;
     CpH; CpR 1; CpY; CpR 3; CpY; CpR 3; CpH; CpR 7; CpY; CpY; CpR 1; CpY;
     CpR 4; CpY; CpR 3; CpY; CpR 1; CpY],
     [35])`;;
let cf620 = new_definition
 `cf620 = ([CpH; CpR 12; CpH; CpR 1; CpY; CpR 3; CpH; CpR 12; CpY; CpR 3; CpH;
     CpR 11; CpY; CpR 3; CpH; CpR 10; CpY; CpR 3; CpH; CpR 2; CpH; CpR 9;
     CpY; CpR 2; CpY; CpR 3; CpY; CpR 2; CpH; CpR 6; CpY; CpR 1; CpH; CpR 1;
     CpY; CpR 1; CpY; CpY; CpR 2; CpY],
     [31])`;;
let cf621 = new_definition
 `cf621 = ([CpH; CpR 2; CpH; CpR 13; CpY; CpR 3; CpH; CpR 12; CpY; CpR 5; CpH;
     CpR 9; CpH; CpR 1; CpH; CpR 1; CpY; CpR 3; CpH; CpR 10; CpY; CpR 4; CpH;
     CpR 8; CpH; CpR 1; CpY; CpR 3; CpY; CpR 1; CpY; CpR 1; CpY; CpR 1; CpY;
     CpR 2; CpY; CpR 1; CpY; CpR 1; CpY],
     [34])`;;
let cf622 = new_definition
 `cf622 = ([CpH; CpR 2; CpH; CpR 10; CpY; CpR 8; CpH; CpR 1; CpY;
            CpR 8; CpH; CpR 8;
     CpH; CpR 8; CpH; CpR 8; CpH; CpR 8; CpH; CpR 8; CpY; CpR 6; CpY; CpY;
     CpY; CpY; CpY; CpY],
     [6])`;;
let cf623 = new_definition
 `cf623 = ([CpH; CpR 10; CpH; CpR 1; CpY; CpR 3; CpH; CpR 10; CpY; CpR 7; CpH;
     CpR 5; CpH; CpR 1; CpH; CpR 1; CpH; CpR 1; CpH; CpR 1; CpY; CpR 2; CpY;
     CpR 3; CpY; CpR 1; CpY; CpR 1; CpY; CpR 1; CpY; CpR 1; CpY; CpR 2; CpY],
     [31])`;;
let cf624 = new_definition
 `cf624 = ([CpH; CpR 10; CpH; CpR 1; CpY; CpR 3; CpH; CpR 10; CpY; CpR 6; CpH;
     CpR 6; CpH; CpR 1; CpH; CpR 1; CpH; CpR 1; CpY; CpR 2; CpH; CpR 1; CpY;
     CpR 3; CpY; CpR 1; CpY; CpR 1; CpY; CpR 1; CpY; CpR 3; CpY; CpY],
     [31])`;;
let cf625 = new_definition
 `cf625 = ([CpH; CpR 2; CpH; CpR 12; CpY; CpR 10; CpH; CpR 1; CpY; CpR 6; CpH;
     CpR 4; CpH; CpR 10; CpH; CpR 10; CpH; CpR 10; CpY; CpR 8; CpH; CpR 1;
     CpY; CpR 8; CpY; CpR 6; CpY; CpY; CpY; CpY; CpR 2; CpY; CpR 2; CpY],
     [12; 13; 32])`;;
let cf626 = new_definition
 `cf626 = ([CpH; CpR 11; CpH; CpR 1; CpY; CpR 3; CpH; CpR 11; CpY; CpR 4; CpH;
     CpR 9; CpH; CpR 1; CpY; CpR 5; CpH; CpR 7; CpH; CpR 1; CpH; CpR 1; CpY;
     CpR 2; CpY; CpR 3; CpY; CpR 1; CpY; CpR 1; CpY; CpR 1; CpY; CpR 1; CpY;
     CpR 2; CpY],
     [31])`;;
let cf627 = new_definition
 `cf627 = ([CpH; CpR 11; CpH; CpR 1; CpY; CpR 3; CpH; CpR 11; CpY; CpR 3; CpH;
     CpR 10; CpY; CpR 6; CpH; CpR 6; CpH; CpR 1; CpH; CpR 1; CpH; CpR 1; CpY;
     CpR 2; CpY; CpR 3; CpY; CpR 1; CpY; CpR 1; CpY; CpR 1; CpY; CpR 1; CpY;
     CpR 2; CpY],
     [30])`;;
let cf628 = new_definition
 `cf628 = ([CpH; CpR 2; CpH; CpR 12; CpY; CpR 10; CpH; CpR 1; CpY; CpR 6; CpH;
     CpR 4; CpH; CpR 10; CpH; CpR 10; CpH; CpR 10; CpY; CpR 8; CpH; CpR 9;
     CpY; CpR 7; CpY; CpY; CpY; CpY; CpR 4; CpH; CpR 4; CpY; CpR 2; CpY; CpY],
     [6])`;;
let cf629 = new_definition
 `cf629 = ([CpH; CpR 11; CpH; CpR 1; CpY; CpR 3; CpH; CpR 11; CpY; CpR 4; CpH;
     CpR 9; CpH; CpR 1; CpY; CpR 3; CpH; CpR 1; CpH; CpR 1; CpH; CpR 1; CpY;
     CpR 3; CpY; CpR 1; CpY; CpR 2; CpH; CpR 1; CpY; CpR 5; CpY; CpR 1; CpY;
     CpR 3; CpY; CpY],
     [35])`;;
let cf630 = new_definition
 `cf630 = ([CpH; CpR 2; CpH; CpR 13; CpY; CpR 11; CpH; CpR 1; CpY; CpR 9; CpH;
     CpR 2; CpH; CpR 11; CpY; CpR 9; CpH; CpR 8; CpH; CpR 2; CpH; CpR 10;
     CpY; CpR 9; CpY; CpR 7; CpY; CpY; CpR 6; CpH; CpR 6; CpY; CpR 2; CpY;
     CpY; CpR 2; CpY; CpR 2; CpY],
     [27])`;;
let cf631 = new_definition
 `cf631 = ([CpH; CpR 11; CpH; CpR 1; CpY; CpR 3; CpH; CpR 11; CpY; CpR 6; CpH;
     CpR 7; CpH; CpR 1; CpH; CpR 1; CpH; CpR 1; CpY; CpR 3; CpH; CpR 9; CpY;
     CpR 5; CpY; CpR 1; CpY; CpR 1; CpY; CpR 1; CpY; CpR 3; CpH; CpR 1; CpY;
     CpR 3; CpY; CpR 1; CpY],
     [31])`;;
let cf632 = new_definition
 `cf632 = ([CpH; CpR 11; CpH; CpR 1; CpY; CpR 3; CpH; CpR 11; CpY; CpR 5; CpH;
     CpR 2; CpH; CpR 10; CpY; CpR 2; CpH; CpR 1; CpY; CpR 4; CpH; CpR 8; CpY;
     CpR 2; CpH; CpR 7; CpY; CpR 2; CpH; CpR 6; CpY; CpR 2; CpY; CpY; CpR 3;
     CpY; CpY],
     [35])`;;
let cf633 = new_definition
 `cf633 = ([CpH; CpR 2; CpH; CpR 11; CpY; CpR 9; CpH; CpR 1; CpY;
            CpR 9; CpH; CpR 9;
     CpH; CpR 9; CpH; CpR 9; CpH; CpR 9; CpH; CpR 9; CpH; CpR 9; CpY; CpR 7;
     CpY; CpY; CpY; CpY; CpY; CpY; CpY],
     [6])`;;

let the_configs = new_definition
 `the_configs =
  [cf001; cf002; cf003; cf004; cf005; cf006; cf007; cf008; cf009; cf010;
     cf011; cf012; cf013; cf014; cf015; cf016; cf017; cf018; cf019; cf020;
     cf021; cf022; cf023; cf024; cf025; cf026; cf027; cf028; cf029; cf030;
     cf031; cf032; cf033; cf034; cf035; cf036; cf037; cf038; cf039; cf040;
     cf041; cf042; cf043; cf044; cf045; cf046; cf047; cf048; cf049; cf050;
     cf051; cf052; cf053; cf054; cf055; cf056; cf057; cf058; cf059; cf060;
     cf061; cf062; cf063; cf064; cf065; cf066; cf067; cf068; cf069; cf070;
     cf071; cf072; cf073; cf074; cf075; cf076; cf077; cf078; cf079; cf080;
     cf081; cf082; cf083; cf084; cf085; cf086; cf087; cf088; cf089; cf090;
     cf091; cf092; cf093; cf094; cf095; cf096; cf097; cf098; cf099; cf100;
     cf101; cf102; cf103; cf104; cf105; cf106; cf107; cf108; cf109; cf110;
     cf111; cf112; cf113; cf114; cf115; cf116; cf117; cf118; cf119; cf120;
     cf121; cf122; cf123; cf124; cf125; cf126; cf127; cf128; cf129; cf130;
     cf131; cf132; cf133; cf134; cf135; cf136; cf137; cf138; cf139; cf140;
     cf141; cf142; cf143; cf144; cf145; cf146; cf147; cf148; cf149; cf150;
     cf151; cf152; cf153; cf154; cf155; cf156; cf157; cf158; cf159; cf160;
     cf161; cf162; cf163; cf164; cf165; cf166; cf167; cf168; cf169; cf170;
     cf171; cf172; cf173; cf174; cf175; cf176; cf177; cf178; cf179; cf180;
     cf181; cf182; cf183; cf184; cf185; cf186; cf187; cf188; cf189; cf190;
     cf191; cf192; cf193; cf194; cf195; cf196; cf197; cf198; cf199; cf200;
     cf201; cf202; cf203; cf204; cf205; cf206; cf207; cf208; cf209; cf210;
     cf211; cf212; cf213; cf214; cf215; cf216; cf217; cf218; cf219; cf220;
     cf221; cf222; cf223; cf224; cf225; cf226; cf227; cf228; cf229; cf230;
     cf231; cf232; cf233; cf234; cf235; cf236; cf237; cf238; cf239; cf240;
     cf241; cf242; cf243; cf244; cf245; cf246; cf247; cf248; cf249; cf250;
     cf251; cf252; cf253; cf254; cf255; cf256; cf257; cf258; cf259; cf260;
     cf261; cf262; cf263; cf264; cf265; cf266; cf267; cf268; cf269; cf270;
     cf271; cf272; cf273; cf274; cf275; cf276; cf277; cf278; cf279; cf280;
     cf281; cf282; cf283; cf284; cf285; cf286; cf287; cf288; cf289; cf290;
     cf291; cf292; cf293; cf294; cf295; cf296; cf297; cf298; cf299; cf300;
     cf301; cf302; cf303; cf304; cf305; cf306; cf307; cf308; cf309; cf310;
     cf311; cf312; cf313; cf314; cf315; cf316; cf317; cf318; cf319; cf320;
     cf321; cf322; cf323; cf324; cf325; cf326; cf327; cf328; cf329; cf330;
     cf331; cf332; cf333; cf334; cf335; cf336; cf337; cf338; cf339; cf340;
     cf341; cf342; cf343; cf344; cf345; cf346; cf347; cf348; cf349; cf350;
     cf351; cf352; cf353; cf354; cf355; cf356; cf357; cf358; cf359; cf360;
     cf361; cf362; cf363; cf364; cf365; cf366; cf367; cf368; cf369; cf370;
     cf371; cf372; cf373; cf374; cf375; cf376; cf377; cf378; cf379; cf380;
     cf381; cf382; cf383; cf384; cf385; cf386; cf387; cf388; cf389; cf390;
     cf391; cf392; cf393; cf394; cf395; cf396; cf397; cf398; cf399; cf400;
     cf401; cf402; cf403; cf404; cf405; cf406; cf407; cf408; cf409; cf410;
     cf411; cf412; cf413; cf414; cf415; cf416; cf417; cf418; cf419; cf420;
     cf421; cf422; cf423; cf424; cf425; cf426; cf427; cf428; cf429; cf430;
     cf431; cf432; cf433; cf434; cf435; cf436; cf437; cf438; cf439; cf440;
     cf441; cf442; cf443; cf444; cf445; cf446; cf447; cf448; cf449; cf450;
     cf451; cf452; cf453; cf454; cf455; cf456; cf457; cf458; cf459; cf460;
     cf461; cf462; cf463; cf464; cf465; cf466; cf467; cf468; cf469; cf470;
     cf471; cf472; cf473; cf474; cf475; cf476; cf477; cf478; cf479; cf480;
     cf481; cf482; cf483; cf484; cf485; cf486; cf487; cf488; cf489; cf490;
     cf491; cf492; cf493; cf494; cf495; cf496; cf497; cf498; cf499; cf500;
     cf501; cf502; cf503; cf504; cf505; cf506; cf507; cf508; cf509; cf510;
     cf511; cf512; cf513; cf514; cf515; cf516; cf517; cf518; cf519; cf520;
     cf521; cf522; cf523; cf524; cf525; cf526; cf527; cf528; cf529; cf530;
     cf531; cf532; cf533; cf534; cf535; cf536; cf537; cf538; cf539; cf540;
     cf541; cf542; cf543; cf544; cf545; cf546; cf547; cf548; cf549; cf550;
     cf551; cf552; cf553; cf554; cf555; cf556; cf557; cf558; cf559; cf560;
     cf561; cf562; cf563; cf564; cf565; cf566; cf567; cf568; cf569; cf570;
     cf571; cf572; cf573; cf574; cf575; cf576; cf577; cf578; cf579; cf580;
     cf581; cf582; cf583; cf584; cf585; cf586; cf587; cf588; cf589; cf590;
     cf591; cf592; cf593; cf594; cf595; cf596; cf597; cf598; cf599; cf600;
     cf601; cf602; cf603; cf604; cf605; cf606; cf607; cf608; cf609; cf610;
     cf611; cf612; cf613; cf614; cf615; cf616; cf617; cf618; cf619; cf620;
     cf621; cf622; cf623; cf624; cf625; cf626; cf627; cf628; cf629; cf630;
     cf631; cf632; cf633]`;;

let the_configs_sym = new_definition
 `the_configs_sym =
  [T; T; T; T; T; F; T; T; T; F; T; T; F; T; F; F; T; F; T; F; T; F; F; T;
     T; F; F; F; T; F; F; F; F; F; F; T; T; F; T; F; F; F; F; F; T; F; T; F;
     F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; T; F; F; F;
     F; F; F; T; T; F; F; F; F; F; F; F; F; F; F; F; F; T; F; F; F; F; F; F;
     F; F; F; T; F; F; F; T; F; F; F; F; F; F; F; T; T; F; F; T; F; F; F; T;
     F; F; F; F; F; F; F; F; F; F; F; F; F; F; T; F; F; F; F; F; T; F; F; F;
     F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F;
     T; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F;
     F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F;
     F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F;
     F; F; F; F; F; F; F; T; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; T;
     F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F;
     F; F; F; F; F; F; F; F; F; F; F; F; F; F; T; T; F; F; F; F; F; F; F; F;
     F; F; F; F; F; F; F; F; F; F; F; T; T; T; F; T; F; T; F; F; F; T; F; F;
     F; F; F; F; T; F; T; F; F; F; F; F; T; F; F; F; F; F; F; F; F; F; F; F;
     F; F; F; F; F; F; F; F; F; F; T; F; F; F; F; F; F; F; F; F; F; F; F; F;
     F; F; F; F; F; T; T; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F;
     F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F;
     F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F;
     F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F;
     F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F;
     F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F;
     T; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F;
     F; F; F; F; F; F; F; F; F; T; F; F; F; F; T; T; T; F; F; F; F; F; F; T;
     F; F; F; F; T; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; T; F; F; F;
     F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; T; F; T; F; F;
     F; F; T; F; F; F; F; F; T]`;;

let LENGTH_THE_CONFIGS = prove
 (`LENGTH the_configs = 633`,
  REWRITE_TAC[the_configs; LENGTH] THEN CONV_TAC NUM_REDUCE_CONV);;
