(*  Title:      Pure/install_pp.ML
    ID:         $Id$

Set up automatic toplevel pretty printing.
*)

fun init_pps () =
  use_string
   ["install_pp (make_pp [\"Thm\", \"thm\"] pprint_thm);",
    "install_pp (make_pp [\"Thm\", \"theory\"] pprint_theory);",
    "install_pp (make_pp [\"Thm\", \"cterm\"] pprint_cterm);",
    "install_pp (make_pp [\"Thm\", \"ctyp\"] pprint_ctyp);",
    "install_pp (make_pp [\"Sign\", \"sg\"] Sign.pprint_sg);",
    "install_pp (make_pp [\"Syntax\", \"ast\"] Syntax.pprint_ast);",
    "install_pp (make_pp [\"typ\"] Syntax.simple_pprint_typ);"];

init_pps ();

