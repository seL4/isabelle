(*  Title:      HOL/MicroJava/J/Type.ML
    ID:         $Id$
    Author:     David von Oheimb
    Copyright   1999 Technische Universitaet Muenchen
*)

Goal "(\\<forall>pt. T \\<noteq> PrimT pt) = (\\<exists>t. T = RefT t)";
by(cases_tac "T" 1);
by Auto_tac;
qed "non_PrimT";
