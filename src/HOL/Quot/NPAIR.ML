(*  Title:      HOL/Quot/NPAIR.ML
    ID:         $Id$
    Author:     Oscar Slotosch
    Copyright   1997 Technische Universitaet Muenchen

*)
open NPAIR;

goalw thy [rep_NP_def] "rep_NP(abs_NP np) = np";
by (Auto_tac());
qed "rep_abs_NP";

Addsimps [rep_abs_NP];

val prems = goalw thy [per_NP_def] "eqv (x::NP) y ==> eqv y x";
by (cut_facts_tac prems 1);
by (Auto_tac());
qed "per_sym_NP";

