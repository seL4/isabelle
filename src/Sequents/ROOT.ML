(*  Title:      Sequents/ROOT.ML
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1991  University of Cambridge

Classical Sequent Calculus based on Pure Isabelle. 
*)

Unify.trace_bound:= 20;
Unify.search_bound := 40;

use_thys ["LK", "ILL", "ILL_predlog", "Washing", "Modal0", "T", "S4", "S43"];
