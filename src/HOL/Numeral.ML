(*  Title:      HOL/Numeral.ML
    ID:         $Id$
    Author:     Tobias Nipkow
*)

(*Unfold all "let"s involving constants*)
Goalw [Let_def] "Let (number_of v) f == f (number_of v)";
by(Simp_tac 1);
qed "Let_number_of";
Addsimps [Let_number_of];

(*The condition "True" is a hack to prevent looping.
  Conditional rewrite rules are tried after unconditional ones, so a rule
  like eq_nat_number_of will be tried first to eliminate #mm=#nn. *)
Goal "True ==> (number_of w = x) = (x = number_of w)";
by Auto_tac;  
qed "number_of_reorient";
Addsimps [number_of_reorient];
