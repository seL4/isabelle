(*  Title:      CCL/equalities.ML
    ID:         $Id$

Equalities involving union, intersection, inclusion, etc.
*)

val eq_cs = set_cs addSIs [equalityI];

(** Binary Intersection **)

goal (the_context ()) "A Int A = A";
by (fast_tac eq_cs 1);
qed "Int_absorb";

goal (the_context ()) "A Int B  =  B Int A";
by (fast_tac eq_cs 1);
qed "Int_commute";

goal (the_context ()) "(A Int B) Int C  =  A Int (B Int C)";
by (fast_tac eq_cs 1);
qed "Int_assoc";

goal (the_context ()) "(A Un B) Int C  =  (A Int C) Un (B Int C)";
by (fast_tac eq_cs 1);
qed "Int_Un_distrib";

goal (the_context ()) "(A<=B) <-> (A Int B = A)";
by (fast_tac (eq_cs addSEs [equalityE]) 1);
qed "subset_Int_eq";

(** Binary Union **)

goal (the_context ()) "A Un A = A";
by (fast_tac eq_cs 1);
qed "Un_absorb";

goal (the_context ()) "A Un B  =  B Un A";
by (fast_tac eq_cs 1);
qed "Un_commute";

goal (the_context ()) "(A Un B) Un C  =  A Un (B Un C)";
by (fast_tac eq_cs 1);
qed "Un_assoc";

goal (the_context ()) "(A Int B) Un C  =  (A Un C) Int (B Un C)";
by (fast_tac eq_cs 1);
qed "Un_Int_distrib";

goal (the_context ())
 "(A Int B) Un (B Int C) Un (C Int A) = (A Un B) Int (B Un C) Int (C Un A)";
by (fast_tac eq_cs 1);
qed "Un_Int_crazy";

goal (the_context ()) "(A<=B) <-> (A Un B = B)";
by (fast_tac (eq_cs addSEs [equalityE]) 1);
qed "subset_Un_eq";

(** Simple properties of Compl -- complement of a set **)

goal (the_context ()) "A Int Compl(A) = {x. False}";
by (fast_tac eq_cs 1);
qed "Compl_disjoint";

goal (the_context ()) "A Un Compl(A) = {x. True}";
by (fast_tac eq_cs 1);
qed "Compl_partition";

goal (the_context ()) "Compl(Compl(A)) = A";
by (fast_tac eq_cs 1);
qed "double_complement";

goal (the_context ()) "Compl(A Un B) = Compl(A) Int Compl(B)";
by (fast_tac eq_cs 1);
qed "Compl_Un";

goal (the_context ()) "Compl(A Int B) = Compl(A) Un Compl(B)";
by (fast_tac eq_cs 1);
qed "Compl_Int";

goal (the_context ()) "Compl(UN x:A. B(x)) = (INT x:A. Compl(B(x)))";
by (fast_tac eq_cs 1);
qed "Compl_UN";

goal (the_context ()) "Compl(INT x:A. B(x)) = (UN x:A. Compl(B(x)))";
by (fast_tac eq_cs 1);
qed "Compl_INT";

(*Halmos, Naive Set Theory, page 16.*)

goal (the_context ()) "((A Int B) Un C = A Int (B Un C)) <-> (C<=A)";
by (fast_tac (eq_cs addSEs [equalityE]) 1);
qed "Un_Int_assoc_eq";


(** Big Union and Intersection **)

goal (the_context ()) "Union(A Un B) = Union(A) Un Union(B)";
by (fast_tac eq_cs 1);
qed "Union_Un_distrib";

val prems = goal (the_context ())
   "(Union(C) Int A = {x. False}) <-> (ALL B:C. B Int A = {x. False})";
by (fast_tac (eq_cs addSEs [equalityE]) 1);
qed "Union_disjoint";

goal (the_context ()) "Inter(A Un B) = Inter(A) Int Inter(B)";
by (best_tac eq_cs 1);
qed "Inter_Un_distrib";

(** Unions and Intersections of Families **)

goal (the_context ()) "(UN x:A. B(x)) = Union({Y. EX x:A. Y=B(x)})";
by (fast_tac eq_cs 1);
qed "UN_eq";

(*Look: it has an EXISTENTIAL quantifier*)
goal (the_context ()) "(INT x:A. B(x)) = Inter({Y. EX x:A. Y=B(x)})";
by (fast_tac eq_cs 1);
qed "INT_eq";

goal (the_context ()) "A Int Union(B) = (UN C:B. A Int C)";
by (fast_tac eq_cs 1);
qed "Int_Union_image";

goal (the_context ()) "A Un Inter(B) = (INT C:B. A Un C)";
by (fast_tac eq_cs 1);
qed "Un_Inter_image";
