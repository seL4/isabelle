(*  Title:      HOL/Lex/Scanner.ML
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   1998 TUM
*)

Goal
 "DA.accepts (na2da(rexp2na r)) w = (w : lang r)";
by (simp_tac (simpset() addsimps [NA_DA_equiv RS sym,accepts_rexp2na]) 1);
qed "accepts_na2da_rexp2na";

Goal
 "DA.accepts (nae2da(rexp2nae r)) w = (w : lang r)";
by (simp_tac (simpset() addsimps [NAe_DA_equiv,accepts_rexp2nae]) 1);
qed "accepts_nae2da_rexp2nae";
