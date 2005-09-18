(*  Title:      Sequents/ROOT.ML
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1991  University of Cambridge

Classical Sequent Calculus based on Pure Isabelle. 
*)

val banner = "Sequent Calculii";
writeln banner;

Unify.trace_bound:= 20;
Unify.search_bound := 40;

use_thy "LK";
use_thy "ILL";
use_thy "Modal0";
use_thy"T";
use_thy"S4";
use_thy"S43";
