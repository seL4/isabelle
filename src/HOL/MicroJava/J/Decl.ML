(*  Title:      HOL/MicroJava/J/Decl.ML
    ID:         $Id$
    Author:     David von Oheimb
    Copyright   1999 Technische Universitaet Muenchen
*)

Goalw [is_class_def, class_def] "finite {C. is_class G C}";
by (fold_goals_tac [dom_def]);
by (rtac finite_dom_map_of 1);
qed "finite_is_class";

