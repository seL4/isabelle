(*  Title:      Pure/install_pp.ML
    ID:         $Id$

Set up automatic toplevel pretty printing.
*)

install_pp (make_pp ["Theory", "theory"] Display.pprint_theory);
install_pp (make_pp ["Thm", "thm"] Display.pprint_thm);
install_pp (make_pp ["Thm", "cterm"] Display.pprint_cterm);
install_pp (make_pp ["Thm", "ctyp"] Display.pprint_ctyp);
install_pp (make_pp ["Sign", "sg"] Sign.pprint_sg);
install_pp (make_pp ["Syntax", "ast"] Syntax.pprint_ast);
install_pp (make_pp ["typ"] Syntax.simple_pprint_typ);
