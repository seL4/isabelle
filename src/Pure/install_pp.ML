(*  Title:      Pure/install_pp.ML
    ID:         $Id$

ML toplevel pretty printing.
*)

install_pp (make_pp ["Thm", "thm"] Display.pprint_thm);
install_pp (make_pp ["Thm", "cterm"] Display.pprint_cterm);
install_pp (make_pp ["Thm", "ctyp"] Display.pprint_ctyp);
install_pp (make_pp ["Context", "theory"] Context.pprint_thy);
install_pp (make_pp ["Syntax", "ast"] Syntax.pprint_ast);
install_pp (make_pp ["typ"] (Sign.pprint_typ ProtoPure.thy));
