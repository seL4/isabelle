(*  Title: 	HOL/equalities
    ID:         $Id$
    Author: 	Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1994  University of Cambridge

Equalities involving union, intersection, inclusion, etc.
*)

writeln"File HOL/equalities";

val eq_cs = set_cs addSIs [equalityI];

(** The membership relation, : **)

goal Set.thy "x ~: {}";
by(fast_tac set_cs 1);
qed "in_empty";

goal Set.thy "x : insert y A = (x=y | x:A)";
by(fast_tac set_cs 1);
qed "in_insert";

(** insert **)

goal Set.thy "!!a. a:A ==> insert a A = A";
by (fast_tac eq_cs 1);
qed "insert_absorb";

goal Set.thy "(insert x A <= B) = (x:B & A <= B)";
by (fast_tac set_cs 1);
qed "insert_subset";

(** Image **)

goal Set.thy "f``{} = {}";
by (fast_tac eq_cs 1);
qed "image_empty";

goal Set.thy "f``insert a B = insert (f a) (f``B)";
by (fast_tac eq_cs 1);
qed "image_insert";

(** Binary Intersection **)

goal Set.thy "A Int A = A";
by (fast_tac eq_cs 1);
qed "Int_absorb";

goal Set.thy "A Int B  =  B Int A";
by (fast_tac eq_cs 1);
qed "Int_commute";

goal Set.thy "(A Int B) Int C  =  A Int (B Int C)";
by (fast_tac eq_cs 1);
qed "Int_assoc";

goal Set.thy "{} Int B = {}";
by (fast_tac eq_cs 1);
qed "Int_empty_left";

goal Set.thy "A Int {} = {}";
by (fast_tac eq_cs 1);
qed "Int_empty_right";

goal Set.thy "A Int (B Un C)  =  (A Int B) Un (A Int C)";
by (fast_tac eq_cs 1);
qed "Int_Un_distrib";

goal Set.thy "(A<=B) = (A Int B = A)";
by (fast_tac (eq_cs addSEs [equalityE]) 1);
qed "subset_Int_eq";

(** Binary Union **)

goal Set.thy "A Un A = A";
by (fast_tac eq_cs 1);
qed "Un_absorb";

goal Set.thy "A Un B  =  B Un A";
by (fast_tac eq_cs 1);
qed "Un_commute";

goal Set.thy "(A Un B) Un C  =  A Un (B Un C)";
by (fast_tac eq_cs 1);
qed "Un_assoc";

goal Set.thy "{} Un B = B";
by(fast_tac eq_cs 1);
qed "Un_empty_left";

goal Set.thy "A Un {} = A";
by(fast_tac eq_cs 1);
qed "Un_empty_right";

goal Set.thy "insert a B Un C = insert a (B Un C)";
by(fast_tac eq_cs 1);
qed "Un_insert_left";

goal Set.thy "(A Int B) Un C  =  (A Un C) Int (B Un C)";
by (fast_tac eq_cs 1);
qed "Un_Int_distrib";

goal Set.thy
 "(A Int B) Un (B Int C) Un (C Int A) = (A Un B) Int (B Un C) Int (C Un A)";
by (fast_tac eq_cs 1);
qed "Un_Int_crazy";

goal Set.thy "(A<=B) = (A Un B = B)";
by (fast_tac (eq_cs addSEs [equalityE]) 1);
qed "subset_Un_eq";

goal Set.thy "(A <= insert b C) = (A <= C | b:A & A-{b} <= C)";
by (fast_tac eq_cs 1);
qed "subset_insert_iff";

goal Set.thy "(A Un B = {}) = (A = {} & B = {})";
by (fast_tac (eq_cs addEs [equalityCE]) 1);
qed "Un_empty";

(** Simple properties of Compl -- complement of a set **)

goal Set.thy "A Int Compl(A) = {}";
by (fast_tac eq_cs 1);
qed "Compl_disjoint";

goal Set.thy "A Un Compl(A) = {x.True}";
by (fast_tac eq_cs 1);
qed "Compl_partition";

goal Set.thy "Compl(Compl(A)) = A";
by (fast_tac eq_cs 1);
qed "double_complement";

goal Set.thy "Compl(A Un B) = Compl(A) Int Compl(B)";
by (fast_tac eq_cs 1);
qed "Compl_Un";

goal Set.thy "Compl(A Int B) = Compl(A) Un Compl(B)";
by (fast_tac eq_cs 1);
qed "Compl_Int";

goal Set.thy "Compl(UN x:A. B(x)) = (INT x:A. Compl(B(x)))";
by (fast_tac eq_cs 1);
qed "Compl_UN";

goal Set.thy "Compl(INT x:A. B(x)) = (UN x:A. Compl(B(x)))";
by (fast_tac eq_cs 1);
qed "Compl_INT";

(*Halmos, Naive Set Theory, page 16.*)

goal Set.thy "((A Int B) Un C = A Int (B Un C)) = (C<=A)";
by (fast_tac (eq_cs addSEs [equalityE]) 1);
qed "Un_Int_assoc_eq";


(** Big Union and Intersection **)

goal Set.thy "Union({}) = {}";
by (fast_tac eq_cs 1);
qed "Union_empty";

goal Set.thy "Union(insert a B) = a Un Union(B)";
by (fast_tac eq_cs 1);
qed "Union_insert";

goal Set.thy "Union(A Un B) = Union(A) Un Union(B)";
by (fast_tac eq_cs 1);
qed "Union_Un_distrib";

goal Set.thy "Union(A Int B) <= Union(A) Int Union(B)";
by (fast_tac set_cs 1);
qed "Union_Int_subset";

val prems = goal Set.thy
   "(Union(C) Int A = {}) = (! B:C. B Int A = {})";
by (fast_tac (eq_cs addSEs [equalityE]) 1);
qed "Union_disjoint";

goal Set.thy "Inter(A Un B) = Inter(A) Int Inter(B)";
by (best_tac eq_cs 1);
qed "Inter_Un_distrib";

(** Unions and Intersections of Families **)

(*Basic identities*)

goal Set.thy "Union(range(f)) = (UN x.f(x))";
by (fast_tac eq_cs 1);
qed "Union_range_eq";

goal Set.thy "Inter(range(f)) = (INT x.f(x))";
by (fast_tac eq_cs 1);
qed "Inter_range_eq";

goal Set.thy "Union(B``A) = (UN x:A. B(x))";
by (fast_tac eq_cs 1);
qed "Union_image_eq";

goal Set.thy "Inter(B``A) = (INT x:A. B(x))";
by (fast_tac eq_cs 1);
qed "Inter_image_eq";

goal Set.thy "!!A. a: A ==> (UN y:A. c) = c";
by (fast_tac eq_cs 1);
qed "UN_constant";

goal Set.thy "!!A. a: A ==> (INT y:A. c) = c";
by (fast_tac eq_cs 1);
qed "INT_constant";

goal Set.thy "(UN x.B) = B";
by (fast_tac eq_cs 1);
qed "UN1_constant";

goal Set.thy "(INT x.B) = B";
by (fast_tac eq_cs 1);
qed "INT1_constant";

goal Set.thy "(UN x:A. B(x)) = Union({Y. ? x:A. Y=B(x)})";
by (fast_tac eq_cs 1);
qed "UN_eq";

(*Look: it has an EXISTENTIAL quantifier*)
goal Set.thy "(INT x:A. B(x)) = Inter({Y. ? x:A. Y=B(x)})";
by (fast_tac eq_cs 1);
qed "INT_eq";

(*Distributive laws...*)

goal Set.thy "A Int Union(B) = (UN C:B. A Int C)";
by (fast_tac eq_cs 1);
qed "Int_Union";

(* Devlin, Fundamentals of Contemporary Set Theory, page 12, exercise 5: 
   Union of a family of unions **)
goal Set.thy "(UN x:C. A(x) Un B(x)) = Union(A``C)  Un  Union(B``C)";
by (fast_tac eq_cs 1);
qed "Un_Union_image";

(*Equivalent version*)
goal Set.thy "(UN i:I. A(i) Un B(i)) = (UN i:I. A(i))  Un  (UN i:I. B(i))";
by (fast_tac eq_cs 1);
qed "UN_Un_distrib";

goal Set.thy "A Un Inter(B) = (INT C:B. A Un C)";
by (fast_tac eq_cs 1);
qed "Un_Inter";

goal Set.thy "(INT x:C. A(x) Int B(x)) = Inter(A``C) Int Inter(B``C)";
by (best_tac eq_cs 1);
qed "Int_Inter_image";

(*Equivalent version*)
goal Set.thy "(INT i:I. A(i) Int B(i)) = (INT i:I. A(i)) Int (INT i:I. B(i))";
by (fast_tac eq_cs 1);
qed "INT_Int_distrib";

(*Halmos, Naive Set Theory, page 35.*)
goal Set.thy "B Int (UN i:I. A(i)) = (UN i:I. B Int A(i))";
by (fast_tac eq_cs 1);
qed "Int_UN_distrib";

goal Set.thy "B Un (INT i:I. A(i)) = (INT i:I. B Un A(i))";
by (fast_tac eq_cs 1);
qed "Un_INT_distrib";

goal Set.thy
    "(UN i:I. A(i)) Int (UN j:J. B(j)) = (UN i:I. UN j:J. A(i) Int B(j))";
by (fast_tac eq_cs 1);
qed "Int_UN_distrib2";

goal Set.thy
    "(INT i:I. A(i)) Un (INT j:J. B(j)) = (INT i:I. INT j:J. A(i) Un B(j))";
by (fast_tac eq_cs 1);
qed "Un_INT_distrib2";

(** Simple properties of Diff -- set difference **)

goal Set.thy "A-A = {}";
by (fast_tac eq_cs 1);
qed "Diff_cancel";

goal Set.thy "{}-A = {}";
by (fast_tac eq_cs 1);
qed "empty_Diff";

goal Set.thy "A-{} = A";
by (fast_tac eq_cs 1);
qed "Diff_empty";

(*NOT SUITABLE FOR REWRITING since {a} == insert a 0*)
goal Set.thy "A - insert a B = A - B - {a}";
by (fast_tac eq_cs 1);
qed "Diff_insert";

(*NOT SUITABLE FOR REWRITING since {a} == insert a 0*)
goal Set.thy "A - insert a B = A - {a} - B";
by (fast_tac eq_cs 1);
qed "Diff_insert2";

val prems = goal Set.thy "a:A ==> insert a (A-{a}) = A";
by (fast_tac (eq_cs addSIs prems) 1);
qed "insert_Diff";

goal Set.thy "A Int (B-A) = {}";
by (fast_tac eq_cs 1);
qed "Diff_disjoint";

goal Set.thy "!!A. A<=B ==> A Un (B-A) = B";
by (fast_tac eq_cs 1);
qed "Diff_partition";

goal Set.thy "!!A. [| A<=B; B<= C |] ==> (B - (C - A)) = (A :: 'a set)";
by (fast_tac eq_cs 1);
qed "double_diff";

goal Set.thy "A - (B Un C) = (A-B) Int (A-C)";
by (fast_tac eq_cs 1);
qed "Diff_Un";

goal Set.thy "A - (B Int C) = (A-B) Un (A-C)";
by (fast_tac eq_cs 1);
qed "Diff_Int";

val set_ss = set_ss addsimps
  [in_empty,in_insert,insert_subset,
   Int_absorb,Int_empty_left,Int_empty_right,
   Un_absorb,Un_empty_left,Un_empty_right,Un_empty,
   UN1_constant,image_empty,
   Compl_disjoint,double_complement,
   Union_empty,Union_insert,empty_subsetI,subset_refl,
   Diff_cancel,empty_Diff,Diff_empty,Diff_disjoint];
