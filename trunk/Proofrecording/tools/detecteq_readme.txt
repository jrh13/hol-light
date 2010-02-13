**************************************************************
* Detecting uses of built-in equality of theorems statically *
**************************************************************

The ocaml compiler has a switch for outputting type information into
an annotation file. This annotation file can then be checked for example
for expressions of type "thm -> thm -> bool" etc. Drawback: You have to
compile the Hol-light sources. This section describes the necessary changes
for compiling and how to run the equality detection tool.

Copy tools/Makefile, tools/startcore.ml and tools/init.ml
to your hol_light directory.

For "make core.out" changes to certain files are necessary:
- remove '#install_printer' from end of "lib.ml"
- remove '#install_printer's from end of "printer.ml"
- remove '#install_printer's from end of "tactics.ml"
- remove history type from "Complex/grobner.ml", because it is already in "grobner.ml"
- in proofobjects_init.ml, remove the final lines
    let _ =
      if use_proofobjects then
        loads "proofobjects_trt.ml"
      else
        loads "proofobjects_dummy.ml";;
- in parser.ml, replace the code for "Hook to allow installation of user parsers" by:
let try_user_parser x =
let install_parser,
  delete_parser,
  installed_parsers,
  try_user_parser =
  let rec try_parsers ps i =
    if ps = [] then raise Noparse else
    try snd(hd ps) i with Noparse -> try_parsers (tl ps) i in
  let parser_list = ref [] in
  (fun dat -> parser_list := dat::(!parser_list)) ,
  (fun (key,_) -> try parser_list := snd (remove (fun (key',_) -> key = key')
                                                 (!parser_list))
                  with Failure _ -> ()),
  (fun () -> !parser_list),
  (fun i -> try_parsers (!parser_list) i)
in
  try_user_parser x;;

Now run the equality detection tool
(many thanks to Virgile Prevosto, who had the idea for how to write such a tool):
- change to the hol_light directory
- run "make core.out" to produce core.ml, core.out and core.annot
- the core.annot file contains information that can be used to find critical
  uses of equalities on theorems:
  run "java -jar ../tools/detecteq.jar . > criticaleq.txt"
  The java program will not terminate, but wait for input at the end,
  therefore check the criticaleq.txt file if the detection has finished,
  for example by "tail criticaleq.txt", and observing the final line "count: ..."
- the file "criticaleq.txt" will now contain a list of lines extracted from
  core.annot, where there could be a critical use of equality on
  theorems (this list is not necessarily complete, but seems to be).
  The line numbers are calculated from the core.annot file (the line numbers in the
  core.annot file are wrong and are corrected by the tool) and refer
  to lines in core.ml.
- after making the necessary changes, run again "make core.out"
- you can run now "ocamlrun -b core.out":
  This will fail with an exception, if the program flow encounters a
  critical theorem equality that has not been removed, printing a stacktrace
  with line numbers.
  Unfortunately, there is something (a bug in ocaml?) that
  causes the lines numbers to be wrong. To convert a wrongly reported line to the correct
  one, run "java -jar ../tools/detecteq.jar", wait for it to finish,
  and then input the wrong line number. It will output the correct line number.
