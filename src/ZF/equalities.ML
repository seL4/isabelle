(*  Title:      ZF/equalities
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1992  University of Cambridge

Set Theory examples: Union, Intersection, Inclusion, etc.
    (Thanks also to Philippe de Groote.)
*)

(** Finite Sets **)

(* cons_def refers to Upair; reversing the equality LOOPS in rewriting!*)
goal thy "{a} Un B = cons(a,B)";
by (fast_tac eq_cs 1);
qed "cons_eq";

goal thy "cons(a, cons(b, C)) = cons(b, cons(a, C))";
by (fast_tac eq_cs 1);
qed "cons_commute";

goal thy "!!B. a: B ==> cons(a,B) = B";
by (fast_tac eq_cs 1);
qed "cons_absorb";

goal thy "!!B. a: B ==> cons(a, B-{a}) = B";
by (fast_tac eq_cs 1);
qed "cons_Diff";

goal thy "!!C. [| a: C;  ALL y:C. y=b |] ==> C = {b}";
by (fast_tac eq_cs 1);
qed "equal_singleton_lemma";
val equal_singleton = ballI RSN (2,equal_singleton_lemma);


(** Binary Intersection **)

(*NOT an equality, but it seems to belong here...*)
goal thy "cons(a,B) Int C <= cons(a, B Int C)";
by (fast_tac eq_cs 1);
qed "Int_cons";

goal thy "A Int A = A";
by (fast_tac eq_cs 1);
qed "Int_absorb";

goal thy "A Int B = B Int A";
by (fast_tac eq_cs 1);
qed "Int_commute";

goal thy "(A Int B) Int C  =  A Int (B Int C)";
by (fast_tac eq_cs 1);
qed "Int_assoc";

goal thy "(A Un B) Int C  =  (A Int C) Un (B Int C)";
by (fast_tac eq_cs 1);
qed "Int_Un_distrib";

goal thy "A<=B <-> A Int B = A";
by (fast_tac (eq_cs addSEs [equalityE]) 1);
qed "subset_Int_iff";

goal thy "A<=B <-> B Int A = A";
by (fast_tac (eq_cs addSEs [equalityE]) 1);
qed "subset_Int_iff2";

goal thy "!!A B C. C<=A ==> (A-B) Int C = C-B";
by (fast_tac eq_cs 1);
qed "Int_Diff_eq";

(** Binary Union **)

goal thy "cons(a,B) Un C = cons(a, B Un C)";
by (fast_tac eq_cs 1);
qed "Un_cons";

goal thy "A Un A = A";
by (fast_tac eq_cs 1);
qed "Un_absorb";

goal thy "A Un B = B Un A";
by (fast_tac eq_cs 1);
qed "Un_commute";

goal thy "(A Un B) Un C  =  A Un (B Un C)";
by (fast_tac eq_cs 1);
qed "Un_assoc";

goal thy "(A Int B) Un C  =  (A Un C) Int (B Un C)";
by (fast_tac eq_cs 1);
qed "Un_Int_distrib";

goal thy "A<=B <-> A Un B = B";
by (fast_tac (eq_cs addSEs [equalityE]) 1);
qed "subset_Un_iff";

goal thy "A<=B <-> B Un A = B";
by (fast_tac (eq_cs addSEs [equalityE]) 1);
qed "subset_Un_iff2";

(** Simple properties of Diff -- set difference **)

goal thy "A-A = 0";
by (fast_tac eq_cs 1);
qed "Diff_cancel";

goal thy "0-A = 0";
by (fast_tac eq_cs 1);
qed "empty_Diff";

goal thy "A-0 = A";
by (fast_tac eq_cs 1);
qed "Diff_0";

goal thy "A-B=0 <-> A<=B";
by (fast_tac (eq_cs addEs [equalityE]) 1);
qed "Diff_eq_0_iff";

(*NOT SUITABLE FOR REWRITING since {a} == cons(a,0)*)
goal thy "A - cons(a,B) = A - B - {a}";
by (fast_tac eq_cs 1);
qed "Diff_cons";

(*NOT SUITABLE FOR REWRITING since {a} == cons(a,0)*)
goal thy "A - cons(a,B) = A - {a} - B";
by (fast_tac eq_cs 1);
qed "Diff_cons2";

goal thy "A Int (B-A) = 0";
by (fast_tac eq_cs 1);
qed "Diff_disjoint";

goal thy "!!A B. A<=B ==> A Un (B-A) = B";
by (fast_tac eq_cs 1);
qed "Diff_partition";

goal thy "A <= B Un (A - B)";
by (Fast_tac 1);
qed "subset_Un_Diff";

goal thy "!!A B. [| A<=B; B<=C |] ==> B-(C-A) = A";
by (fast_tac eq_cs 1);
qed "double_complement";

goal thy "(A Un B) - (B-A) = A";
by (fast_tac eq_cs 1);
qed "double_complement_Un";

goal thy
 "(A Int B) Un (B Int C) Un (C Int A) = (A Un B) Int (B Un C) Int (C Un A)";
by (fast_tac eq_cs 1);
qed "Un_Int_crazy";

goal thy "A - (B Un C) = (A-B) Int (A-C)";
by (fast_tac eq_cs 1);
qed "Diff_Un";

goal thy "A - (B Int C) = (A-B) Un (A-C)";
by (fast_tac eq_cs 1);
qed "Diff_Int";

(*Halmos, Naive Set Theory, page 16.*)
goal thy "(A Int B) Un C = A Int (B Un C)  <->  C<=A";
by (fast_tac (eq_cs addSEs [equalityE]) 1);
qed "Un_Int_assoc_iff";


(** Big Union and Intersection **)

goal thy "Union(cons(a,B)) = a Un Union(B)";
by (fast_tac eq_cs 1);
qed "Union_cons";

goal thy "Union(A Un B) = Union(A) Un Union(B)";
by (fast_tac eq_cs 1);
qed "Union_Un_distrib";

goal thy "Union(A Int B) <= Union(A) Int Union(B)";
by (Fast_tac 1);
qed "Union_Int_subset";

goal thy "Union(C) Int A = 0 <-> (ALL B:C. B Int A = 0)";
by (fast_tac (eq_cs addSEs [equalityE]) 1);
qed "Union_disjoint";

goalw thy [Inter_def] "Inter(0) = 0";
by (fast_tac eq_cs 1);
qed "Inter_0";

goal thy "!!A B. [| z:A; z:B |] ==> Inter(A) Un Inter(B) <= Inter(A Int B)";
by (Fast_tac 1);
qed "Inter_Un_subset";

(* A good challenge: Inter is ill-behaved on the empty set *)
goal thy "!!A B. [| a:A;  b:B |] ==> Inter(A Un B) = Inter(A) Int Inter(B)";
by (fast_tac eq_cs 1);
qed "Inter_Un_distrib";

goal thy "Union({b}) = b";
by (fast_tac eq_cs 1);
qed "Union_singleton";

goal thy "Inter({b}) = b";
by (fast_tac eq_cs 1);
qed "Inter_singleton";

(** Unions and Intersections of Families **)

goal thy "Union(A) = (UN x:A. x)";
by (fast_tac eq_cs 1);
qed "Union_eq_UN";

goalw thy [Inter_def] "Inter(A) = (INT x:A. x)";
by (fast_tac eq_cs 1);
qed "Inter_eq_INT";

goal thy "(UN i:0. A(i)) = 0";
by (fast_tac eq_cs 1);
qed "UN_0";

(*Halmos, Naive Set Theory, page 35.*)
goal thy "B Int (UN i:I. A(i)) = (UN i:I. B Int A(i))";
by (fast_tac eq_cs 1);
qed "Int_UN_distrib";

goal thy "!!A B. i:I ==> B Un (INT i:I. A(i)) = (INT i:I. B Un A(i))";
by (fast_tac eq_cs 1);
qed "Un_INT_distrib";

goal thy
    "(UN i:I. A(i)) Int (UN j:J. B(j)) = (UN i:I. UN j:J. A(i) Int B(j))";
by (fast_tac eq_cs 1);
qed "Int_UN_distrib2";

goal thy
    "!!I J. [| i:I;  j:J |] ==> \
\    (INT i:I. A(i)) Un (INT j:J. B(j)) = (INT i:I. INT j:J. A(i) Un B(j))";
by (fast_tac eq_cs 1);
qed "Un_INT_distrib2";

goal thy "!!A. a: A ==> (UN y:A. c) = c";
by (fast_tac eq_cs 1);
qed "UN_constant";

goal thy "!!A. a: A ==> (INT y:A. c) = c";
by (fast_tac eq_cs 1);
qed "INT_constant";

(** Devlin, Fundamentals of Contemporary Set Theory, page 12, exercise 5: 
    Union of a family of unions **)

goal thy "(UN i:I. A(i) Un B(i)) = (UN i:I. A(i))  Un  (UN i:I. B(i))";
by (fast_tac eq_cs 1);
qed "UN_Un_distrib";

goal thy
    "!!A B. i:I ==> \
\           (INT i:I. A(i)  Int  B(i)) = (INT i:I. A(i)) Int (INT i:I. B(i))";
by (fast_tac eq_cs 1);
qed "INT_Int_distrib";

goal thy "(UN z:I Int J. A(z)) <= (UN z:I. A(z)) Int (UN z:J. A(z))";
by (Fast_tac 1);
qed "UN_Int_subset";

(** Devlin, page 12, exercise 5: Complements **)

goal thy "!!A B. i:I ==> B - (UN i:I. A(i)) = (INT i:I. B - A(i))";
by (fast_tac eq_cs 1);
qed "Diff_UN";

goal thy "!!A B. i:I ==> B - (INT i:I. A(i)) = (UN i:I. B - A(i))";
by (fast_tac eq_cs 1);
qed "Diff_INT";

(** Unions and Intersections with General Sum **)

(*Not suitable for rewriting: LOOPS!*)
goal thy "Sigma(cons(a,B), C) = ({a}*C(a)) Un Sigma(B,C)";
by (fast_tac eq_cs 1);
qed "Sigma_cons1";

(*Not suitable for rewriting: LOOPS!*)
goal thy "A * cons(b,B) = A*{b} Un A*B";
by (fast_tac eq_cs 1);
qed "Sigma_cons2";

goal thy "Sigma(succ(A), B) = ({A}*B(A)) Un Sigma(A,B)";
by (fast_tac eq_cs 1);
qed "Sigma_succ1";

goal thy "A * succ(B) = A*{B} Un A*B";
by (fast_tac eq_cs 1);
qed "Sigma_succ2";

goal thy "(SUM x:(UN y:A. C(y)). B(x)) = (UN y:A. SUM x:C(y). B(x))";
by (fast_tac eq_cs 1);
qed "SUM_UN_distrib1";

goal thy "(SUM i:I. UN j:J. C(i,j)) = (UN j:J. SUM i:I. C(i,j))";
by (fast_tac eq_cs 1);
qed "SUM_UN_distrib2";

goal thy "(SUM i:I Un J. C(i)) = (SUM i:I. C(i)) Un (SUM j:J. C(j))";
by (fast_tac eq_cs 1);
qed "SUM_Un_distrib1";

goal thy "(SUM i:I. A(i) Un B(i)) = (SUM i:I. A(i)) Un (SUM i:I. B(i))";
by (fast_tac eq_cs 1);
qed "SUM_Un_distrib2";

(*First-order version of the above, for rewriting*)
goal thy "I * (A Un B) = I*A Un I*B";
by (rtac SUM_Un_distrib2 1);
qed "prod_Un_distrib2";

goal thy "(SUM i:I Int J. C(i)) = (SUM i:I. C(i)) Int (SUM j:J. C(j))";
by (fast_tac eq_cs 1);
qed "SUM_Int_distrib1";

goal thy
    "(SUM i:I. A(i) Int B(i)) = (SUM i:I. A(i)) Int (SUM i:I. B(i))";
by (fast_tac eq_cs 1);
qed "SUM_Int_distrib2";

(*First-order version of the above, for rewriting*)
goal thy "I * (A Int B) = I*A Int I*B";
by (rtac SUM_Int_distrib2 1);
qed "prod_Int_distrib2";

(*Cf Aczel, Non-Well-Founded Sets, page 115*)
goal thy "(SUM i:I. A(i)) = (UN i:I. {i} * A(i))";
by (fast_tac eq_cs 1);
qed "SUM_eq_UN";

(** Domain **)

qed_goal "domain_of_prod" thy "!!A B. b:B ==> domain(A*B) = A"
 (fn _ => [ fast_tac eq_cs 1 ]);

qed_goal "domain_0" thy "domain(0) = 0"
 (fn _ => [ fast_tac eq_cs 1 ]);

qed_goal "domain_cons" thy
    "domain(cons(<a,b>,r)) = cons(a, domain(r))"
 (fn _ => [ fast_tac eq_cs 1 ]);

goal thy "domain(A Un B) = domain(A) Un domain(B)";
by (fast_tac eq_cs 1);
qed "domain_Un_eq";

goal thy "domain(A Int B) <= domain(A) Int domain(B)";
by (fast_tac eq_cs 1);
qed "domain_Int_subset";

goal thy "domain(A) - domain(B) <= domain(A - B)";
by (fast_tac eq_cs 1);
qed "domain_Diff_subset";

goal thy "domain(converse(r)) = range(r)";
by (fast_tac eq_cs 1);
qed "domain_converse";

Addsimps [domain_0, domain_cons, domain_Un_eq, domain_converse];


(** Range **)

qed_goal "range_of_prod" thy
    "!!a A B. a:A ==> range(A*B) = B"
 (fn _ => [ fast_tac eq_cs 1 ]);

qed_goal "range_0" thy "range(0) = 0"
 (fn _ => [ fast_tac eq_cs 1 ]); 

qed_goal "range_cons" thy
    "range(cons(<a,b>,r)) = cons(b, range(r))"
 (fn _ => [ fast_tac eq_cs 1 ]);

goal thy "range(A Un B) = range(A) Un range(B)";
by (fast_tac eq_cs 1);
qed "range_Un_eq";

goal thy "range(A Int B) <= range(A) Int range(B)";
by (Fast_tac 1);
qed "range_Int_subset";

goal thy "range(A) - range(B) <= range(A - B)";
by (fast_tac eq_cs 1);
qed "range_Diff_subset";

goal thy "range(converse(r)) = domain(r)";
by (fast_tac eq_cs 1);
qed "range_converse";

Addsimps [range_0, range_cons, range_Un_eq, range_converse];


(** Field **)

qed_goal "field_of_prod" thy "field(A*A) = A"
 (fn _ => [ fast_tac eq_cs 1 ]); 

qed_goal "field_0" thy "field(0) = 0"
 (fn _ => [ fast_tac eq_cs 1 ]); 

qed_goal "field_cons" thy
    "field(cons(<a,b>,r)) = cons(a, cons(b, field(r)))"
 (fn _ => [ rtac equalityI 1, ALLGOALS (Fast_tac) ]);

goal thy "field(A Un B) = field(A) Un field(B)";
by (fast_tac eq_cs 1);
qed "field_Un_eq";

goal thy "field(A Int B) <= field(A) Int field(B)";
by (fast_tac eq_cs 1);
qed "field_Int_subset";

goal thy "field(A) - field(B) <= field(A - B)";
by (fast_tac eq_cs 1);
qed "field_Diff_subset";

goal thy "field(converse(r)) = field(r)";
by (fast_tac eq_cs 1);
qed "field_converse";

Addsimps [field_0, field_cons, field_Un_eq, field_converse];


(** Image **)

goal thy "r``0 = 0";
by (fast_tac eq_cs 1);
qed "image_0";

goal thy "r``(A Un B) = (r``A) Un (r``B)";
by (fast_tac eq_cs 1);
qed "image_Un";

goal thy "r``(A Int B) <= (r``A) Int (r``B)";
by (Fast_tac 1);
qed "image_Int_subset";

goal thy "(r Int A*A)``B <= (r``B) Int A";
by (Fast_tac 1);
qed "image_Int_square_subset";

goal thy "!!r. B<=A ==> (r Int A*A)``B = (r``B) Int A";
by (fast_tac eq_cs 1);
qed "image_Int_square";

Addsimps [image_0, image_Un];


(** Inverse Image **)

goal thy "r-``0 = 0";
by (fast_tac eq_cs 1);
qed "vimage_0";

goal thy "r-``(A Un B) = (r-``A) Un (r-``B)";
by (fast_tac eq_cs 1);
qed "vimage_Un";

goal thy "r-``(A Int B) <= (r-``A) Int (r-``B)";
by (Fast_tac 1);
qed "vimage_Int_subset";

goal thy "(r Int A*A)-``B <= (r-``B) Int A";
by (Fast_tac 1);
qed "vimage_Int_square_subset";

goal thy "!!r. B<=A ==> (r Int A*A)-``B = (r-``B) Int A";
by (fast_tac eq_cs 1);
qed "vimage_Int_square";

Addsimps [vimage_0, vimage_Un];


(** Converse **)

goal thy "converse(A Un B) = converse(A) Un converse(B)";
by (fast_tac eq_cs 1);
qed "converse_Un";

goal thy "converse(A Int B) = converse(A) Int converse(B)";
by (fast_tac eq_cs 1);
qed "converse_Int";

goal thy "converse(A - B) = converse(A) - converse(B)";
by (fast_tac eq_cs 1);
qed "converse_Diff";

goal thy "converse(UN x:A. B(x)) = (UN x:A. converse(B(x)))";
by (fast_tac eq_cs 1);
qed "converse_UN";

(*Unfolding Inter avoids using excluded middle on A=0*)
goalw thy [Inter_def] "converse(INT x:A. B(x)) = (INT x:A. converse(B(x)))";
by (fast_tac eq_cs 1);
qed "converse_INT";

Addsimps [converse_Un, converse_Int, converse_Diff, converse_UN, converse_INT];

(** Pow **)

goal thy "Pow(A) Un Pow(B) <= Pow(A Un B)";
by (Fast_tac 1);
qed "Un_Pow_subset";

goal thy "(UN x:A. Pow(B(x))) <= Pow(UN x:A. B(x))";
by (Fast_tac 1);
qed "UN_Pow_subset";

goal thy "A <= Pow(Union(A))";
by (Fast_tac 1);
qed "subset_Pow_Union";

goal thy "Union(Pow(A)) = A";
by (fast_tac eq_cs 1);
qed "Union_Pow_eq";

goal thy "Pow(A Int B) = Pow(A) Int Pow(B)";
by (fast_tac eq_cs 1);
qed "Int_Pow_eq";

goal thy "!!x A. x:A ==> (INT x:A. Pow(B(x))) = Pow(INT x:A. B(x))";
by (fast_tac eq_cs 1);
qed "INT_Pow_subset";

Addsimps [Union_Pow_eq, Int_Pow_eq];

(** RepFun **)

goal thy "{f(x).x:A}=0 <-> A=0";
by (fast_tac (eq_cs addSEs [equalityE]) 1);
qed "RepFun_eq_0_iff";

(** Collect **)

goal thy "Collect(A Un B, P) = Collect(A,P) Un Collect(B,P)";
by (fast_tac eq_cs 1);
qed "Collect_Un";

goal thy "Collect(A Int B, P) = Collect(A,P) Int Collect(B,P)";
by (fast_tac eq_cs 1);
qed "Collect_Int";

goal thy "Collect(A - B, P) = Collect(A,P) - Collect(B,P)";
by (fast_tac eq_cs 1);
qed "Collect_Diff";

goal thy "{x:cons(a,B). P(x)} = if(P(a), cons(a, {x:B. P(x)}), {x:B. P(x)})";
by (simp_tac (!simpset setloop split_tac [expand_if]) 1);
by (fast_tac eq_cs 1);
qed "Collect_cons";

