(*  Title:      HOL/Lex/Scanner.ML
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   1998 TUM
*)

goal thy
 "DA.accepts (nae2da(rexp2nae r)) w = (w : lang r)";
by(simp_tac (simpset() addsimps [NAe_DA_equiv,accepts_rexp2nae]) 1);
qed "accepts_nae2da_rexp2nae";
