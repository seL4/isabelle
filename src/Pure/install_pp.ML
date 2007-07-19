(*  Title:      Pure/install_pp.ML
    ID:         $Id$

ML toplevel pretty printing.
*)

install_pp (make_pp ["Thm", "thm"] ProofDisplay.pprint_thm);
install_pp (make_pp ["Thm", "cterm"] ProofDisplay.pprint_cterm);
install_pp (make_pp ["Thm", "ctyp"] ProofDisplay.pprint_ctyp);
install_pp (make_pp ["Context", "theory"] Context.pprint_thy);
install_pp (make_pp ["Context", "proof"] ProofDisplay.pprint_context);
install_pp (make_pp ["Syntax", "ast"] Syntax.pprint_ast);
install_pp (make_pp ["typ"] (ProofDisplay.pprint_typ Pure.thy));
install_pp (make_pp ["Path", "T"] (Pretty.pprint o Pretty.quote o Pretty.str o Path.implode));
install_pp (make_pp ["File", "ident"] (Pretty.pprint o Pretty.str o File.rep_ident));
