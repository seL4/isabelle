(*  Title:      HOL/Numeral.ML
    ID:         $Id$
    Author:     Tobias Nipkow
*)

(*Unfold all "let"s involving constants*)
Goalw [Let_def] "Let (number_of v) f == f (number_of v)";
by(Simp_tac 1);
qed "Let_number_of";
Addsimps [Let_number_of];
