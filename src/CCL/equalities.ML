(*  Title: 	CCL/equalities
    ID:         $Id$

Modified version of
    Title: 	HOL/equalities
    Author: 	Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1991  University of Cambridge

Equalities involving union, intersection, inclusion, etc.
*)

writeln"File HOL/equalities";

val eq_cs = set_cs addSIs [equalityI];

(** Binary Intersection **)

goal Set.thy "A Int A = A";
by (fast_tac eq_cs 1);
val Int_absorb = result();

goal Set.thy "A Int B  =  B Int A";
by (fast_tac eq_cs 1);
val Int_commute = result();

goal Set.thy "(A Int B) Int C  =  A Int (B Int C)";
by (fast_tac eq_cs 1);
val Int_assoc = result();

goal Set.thy "(A Un B) Int C  =  (A Int C) Un (B Int C)";
by (fast_tac eq_cs 1);
val Int_Un_distrib = result();

goal Set.thy "(A<=B) <-> (A Int B = A)";
by (fast_tac (eq_cs addSEs [equalityE]) 1);
val subset_Int_eq = result();

(** Binary Union **)

goal Set.thy "A Un A = A";
by (fast_tac eq_cs 1);
val Un_absorb = result();

goal Set.thy "A Un B  =  B Un A";
by (fast_tac eq_cs 1);
val Un_commute = result();

goal Set.thy "(A Un B) Un C  =  A Un (B Un C)";
by (fast_tac eq_cs 1);
val Un_assoc = result();

goal Set.thy "(A Int B) Un C  =  (A Un C) Int (B Un C)";
by (fast_tac eq_cs 1);
val Un_Int_distrib = result();

goal Set.thy
 "(A Int B) Un (B Int C) Un (C Int A) = (A Un B) Int (B Un C) Int (C Un A)";
by (fast_tac eq_cs 1);
val Un_Int_crazy = result();

goal Set.thy "(A<=B) <-> (A Un B = B)";
by (fast_tac (eq_cs addSEs [equalityE]) 1);
val subset_Un_eq = result();

(** Simple properties of Compl -- complement of a set **)

goal Set.thy "A Int Compl(A) = {x.False}";
by (fast_tac eq_cs 1);
val Compl_disjoint = result();

goal Set.thy "A Un Compl(A) = {x.True}";
by (fast_tac eq_cs 1);
val Compl_partition = result();

goal Set.thy "Compl(Compl(A)) = A";
by (fast_tac eq_cs 1);
val double_complement = result();

goal Set.thy "Compl(A Un B) = Compl(A) Int Compl(B)";
by (fast_tac eq_cs 1);
val Compl_Un = result();

goal Set.thy "Compl(A Int B) = Compl(A) Un Compl(B)";
by (fast_tac eq_cs 1);
val Compl_Int = result();

goal Set.thy "Compl(UN x:A. B(x)) = (INT x:A. Compl(B(x)))";
by (fast_tac eq_cs 1);
val Compl_UN = result();

goal Set.thy "Compl(INT x:A. B(x)) = (UN x:A. Compl(B(x)))";
by (fast_tac eq_cs 1);
val Compl_INT = result();

(*Halmos, Naive Set Theory, page 16.*)

goal Set.thy "((A Int B) Un C = A Int (B Un C)) <-> (C<=A)";
by (fast_tac (eq_cs addSEs [equalityE]) 1);
val Un_Int_assoc_eq = result();


(** Big Union and Intersection **)

goal Set.thy "Union(A Un B) = Union(A) Un Union(B)";
by (fast_tac eq_cs 1);
val Union_Un_distrib = result();

val prems = goal Set.thy
   "(Union(C) Int A = {x.False}) <-> (ALL B:C. B Int A = {x.False})";
by (fast_tac (eq_cs addSEs [equalityE]) 1);
val Union_disjoint = result();

goal Set.thy "Inter(A Un B) = Inter(A) Int Inter(B)";
by (best_tac eq_cs 1);
val Inter_Un_distrib = result();

(** Unions and Intersections of Families **)

goal Set.thy "(UN x:A. B(x)) = Union({Y. EX x:A. Y=B(x)})";
by (fast_tac eq_cs 1);
val UN_eq = result();

(*Look: it has an EXISTENTIAL quantifier*)
goal Set.thy "(INT x:A. B(x)) = Inter({Y. EX x:A. Y=B(x)})";
by (fast_tac eq_cs 1);
val INT_eq = result();

goal Set.thy "A Int Union(B) = (UN C:B. A Int C)";
by (fast_tac eq_cs 1);
val Int_Union_image = result();

goal Set.thy "A Un Inter(B) = (INT C:B. A Un C)";
by (fast_tac eq_cs 1);
val Un_Inter_image = result();
