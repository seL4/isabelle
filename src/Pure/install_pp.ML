(*  Title:      Pure/install_pp
    ID:         $Id$

Set up automatic toplevel printing
*)

install_pp (make_pp ["Thm", "thm"] pprint_thm);
install_pp (make_pp ["Thm", "theory"] pprint_theory);
install_pp (make_pp ["Sign", "sg"] pprint_sg);
install_pp (make_pp ["term"] pprint_term);
install_pp (make_pp ["Sign", "cterm"] Sign.pprint_cterm);
install_pp (make_pp ["typ"] pprint_typ);
install_pp (make_pp ["Sign", "ctyp"] Sign.pprint_ctyp);
install_pp (make_pp ["Ast", "ast"] Syntax.pprint_ast);

