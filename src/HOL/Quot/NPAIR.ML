(*  Title:      HOL/Quot/NPAIR.ML
    ID:         $Id$
    Author:     Oscar Slotosch
    Copyright   1997 Technische Universitaet Muenchen

*)
open NPAIR;

Goalw [rep_NP_def] "rep_NP(abs_NP np) = np";
by Auto_tac;
qed "rep_abs_NP";

Addsimps [rep_abs_NP];

Goalw [per_NP_def] "eqv (x::NP) y ==> eqv y x";
by Auto_tac;
qed "per_sym_NP";

