(*  Title: 	ZF/equalities
    ID:         $Id$
    Author: 	Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1992  University of Cambridge

Set Theory examples: Union, Intersection, Inclusion, etc.
    (Thanks also to Philippe de Groote.)
*)

(** Finite Sets **)

(* cons_def refers to Upair; reversing the equality LOOPS in rewriting!*)
goal ZF.thy "{a} Un B = cons(a,B)";
by (fast_tac eq_cs 1);
qed "cons_eq";

goal ZF.thy "cons(a, cons(b, C)) = cons(b, cons(a, C))";
by (fast_tac eq_cs 1);
qed "cons_commute";

goal ZF.thy "!!B. a: B ==> cons(a,B) = B";
by (fast_tac eq_cs 1);
qed "cons_absorb";

goal ZF.thy "!!B. a: B ==> cons(a, B-{a}) = B";
by (fast_tac eq_cs 1);
qed "cons_Diff";

goal ZF.thy "!!C. [| a: C;  ALL y:C. y=b |] ==> C = {b}";
by (fast_tac eq_cs 1);
qed "equal_singleton_lemma";
val equal_singleton = ballI RSN (2,equal_singleton_lemma);


(** Binary Intersection **)

goal ZF.thy "0 Int A = 0";
by (fast_tac eq_cs 1);
qed "Int_0";

(*NOT an equality, but it seems to belong here...*)
goal ZF.thy "cons(a,B) Int C <= cons(a, B Int C)";
by (fast_tac eq_cs 1);
qed "Int_cons";

goal ZF.thy "A Int A = A";
by (fast_tac eq_cs 1);
qed "Int_absorb";

goal ZF.thy "A Int B = B Int A";
by (fast_tac eq_cs 1);
qed "Int_commute";

goal ZF.thy "(A Int B) Int C  =  A Int (B Int C)";
by (fast_tac eq_cs 1);
qed "Int_assoc";

goal ZF.thy "(A Un B) Int C  =  (A Int C) Un (B Int C)";
by (fast_tac eq_cs 1);
qed "Int_Un_distrib";

goal ZF.thy "A<=B <-> A Int B = A";
by (fast_tac (eq_cs addSEs [equalityE]) 1);
qed "subset_Int_iff";

goal ZF.thy "A<=B <-> B Int A = A";
by (fast_tac (eq_cs addSEs [equalityE]) 1);
qed "subset_Int_iff2";

(** Binary Union **)

goal ZF.thy "0 Un A = A";
by (fast_tac eq_cs 1);
qed "Un_0";

goal ZF.thy "cons(a,B) Un C = cons(a, B Un C)";
by (fast_tac eq_cs 1);
qed "Un_cons";

goal ZF.thy "A Un A = A";
by (fast_tac eq_cs 1);
qed "Un_absorb";

goal ZF.thy "A Un B = B Un A";
by (fast_tac eq_cs 1);
qed "Un_commute";

goal ZF.thy "(A Un B) Un C  =  A Un (B Un C)";
by (fast_tac eq_cs 1);
qed "Un_assoc";

goal ZF.thy "(A Int B) Un C  =  (A Un C) Int (B Un C)";
by (fast_tac eq_cs 1);
qed "Un_Int_distrib";

goal ZF.thy "A<=B <-> A Un B = B";
by (fast_tac (eq_cs addSEs [equalityE]) 1);
qed "subset_Un_iff";

goal ZF.thy "A<=B <-> B Un A = B";
by (fast_tac (eq_cs addSEs [equalityE]) 1);
qed "subset_Un_iff2";

(** Simple properties of Diff -- set difference **)

goal ZF.thy "A-A = 0";
by (fast_tac eq_cs 1);
qed "Diff_cancel";

goal ZF.thy "0-A = 0";
by (fast_tac eq_cs 1);
qed "empty_Diff";

goal ZF.thy "A-0 = A";
by (fast_tac eq_cs 1);
qed "Diff_0";

goal ZF.thy "A-B=0 <-> A<=B";
by (fast_tac (eq_cs addEs [equalityE]) 1);
qed "Diff_eq_0_iff";

(*NOT SUITABLE FOR REWRITING since {a} == cons(a,0)*)
goal ZF.thy "A - cons(a,B) = A - B - {a}";
by (fast_tac eq_cs 1);
qed "Diff_cons";

(*NOT SUITABLE FOR REWRITING since {a} == cons(a,0)*)
goal ZF.thy "A - cons(a,B) = A - {a} - B";
by (fast_tac eq_cs 1);
qed "Diff_cons2";

goal ZF.thy "A Int (B-A) = 0";
by (fast_tac eq_cs 1);
qed "Diff_disjoint";

goal ZF.thy "!!A B. A<=B ==> A Un (B-A) = B";
by (fast_tac eq_cs 1);
qed "Diff_partition";

goal ZF.thy "!!A B. [| A<=B; B<=C |] ==> B-(C-A) = A";
by (fast_tac eq_cs 1);
qed "double_complement";

goal ZF.thy "(A Un B) - (B-A) = A";
by (fast_tac eq_cs 1);
qed "double_complement_Un";

goal ZF.thy
 "(A Int B) Un (B Int C) Un (C Int A) = (A Un B) Int (B Un C) Int (C Un A)";
by (fast_tac eq_cs 1);
qed "Un_Int_crazy";

goal ZF.thy "A - (B Un C) = (A-B) Int (A-C)";
by (fast_tac eq_cs 1);
qed "Diff_Un";

goal ZF.thy "A - (B Int C) = (A-B) Un (A-C)";
by (fast_tac eq_cs 1);
qed "Diff_Int";

(*Halmos, Naive Set Theory, page 16.*)
goal ZF.thy "(A Int B) Un C = A Int (B Un C)  <->  C<=A";
by (fast_tac (eq_cs addSEs [equalityE]) 1);
qed "Un_Int_assoc_iff";


(** Big Union and Intersection **)

goal ZF.thy "Union(0) = 0";
by (fast_tac eq_cs 1);
qed "Union_0";

goal ZF.thy "Union(cons(a,B)) = a Un Union(B)";
by (fast_tac eq_cs 1);
qed "Union_cons";

goal ZF.thy "Union(A Un B) = Union(A) Un Union(B)";
by (fast_tac eq_cs 1);
qed "Union_Un_distrib";

goal ZF.thy "Union(A Int B) <= Union(A) Int Union(B)";
by (fast_tac ZF_cs 1);
qed "Union_Int_subset";

goal ZF.thy "Union(C) Int A = 0 <-> (ALL B:C. B Int A = 0)";
by (fast_tac (eq_cs addSEs [equalityE]) 1);
qed "Union_disjoint";

(* A good challenge: Inter is ill-behaved on the empty set *)
goal ZF.thy "!!A B. [| a:A;  b:B |] ==> Inter(A Un B) = Inter(A) Int Inter(B)";
by (fast_tac eq_cs 1);
qed "Inter_Un_distrib";

goal ZF.thy "Union({b}) = b";
by (fast_tac eq_cs 1);
qed "Union_singleton";

goal ZF.thy "Inter({b}) = b";
by (fast_tac eq_cs 1);
qed "Inter_singleton";

(** Unions and Intersections of Families **)

goal ZF.thy "Union(A) = (UN x:A. x)";
by (fast_tac eq_cs 1);
qed "Union_eq_UN";

goalw ZF.thy [Inter_def] "Inter(A) = (INT x:A. x)";
by (fast_tac eq_cs 1);
qed "Inter_eq_INT";

goal ZF.thy "(UN i:0. A(i)) = 0";
by (fast_tac eq_cs 1);
qed "UN_0";

(*Halmos, Naive Set Theory, page 35.*)
goal ZF.thy "B Int (UN i:I. A(i)) = (UN i:I. B Int A(i))";
by (fast_tac eq_cs 1);
qed "Int_UN_distrib";

goal ZF.thy "!!A B. i:I ==> B Un (INT i:I. A(i)) = (INT i:I. B Un A(i))";
by (fast_tac eq_cs 1);
qed "Un_INT_distrib";

goal ZF.thy
    "(UN i:I. A(i)) Int (UN j:J. B(j)) = (UN i:I. UN j:J. A(i) Int B(j))";
by (fast_tac eq_cs 1);
qed "Int_UN_distrib2";

goal ZF.thy
    "!!I J. [| i:I;  j:J |] ==> \
\    (INT i:I. A(i)) Un (INT j:J. B(j)) = (INT i:I. INT j:J. A(i) Un B(j))";
by (fast_tac eq_cs 1);
qed "Un_INT_distrib2";

goal ZF.thy "!!A. a: A ==> (UN y:A. c) = c";
by (fast_tac eq_cs 1);
qed "UN_constant";

goal ZF.thy "!!A. a: A ==> (INT y:A. c) = c";
by (fast_tac eq_cs 1);
qed "INT_constant";

(** Devlin, Fundamentals of Contemporary Set Theory, page 12, exercise 5: 
    Union of a family of unions **)

goal ZF.thy "(UN i:I. A(i) Un B(i)) = (UN i:I. A(i))  Un  (UN i:I. B(i))";
by (fast_tac eq_cs 1);
qed "UN_Un_distrib";

goal ZF.thy
    "!!A B. i:I ==> \
\           (INT i:I. A(i)  Int  B(i)) = (INT i:I. A(i)) Int (INT i:I. B(i))";
by (fast_tac eq_cs 1);
qed "INT_Int_distrib";

(** Devlin, page 12, exercise 5: Complements **)

goal ZF.thy "!!A B. i:I ==> B - (UN i:I. A(i)) = (INT i:I. B - A(i))";
by (fast_tac eq_cs 1);
qed "Diff_UN";

goal ZF.thy "!!A B. i:I ==> B - (INT i:I. A(i)) = (UN i:I. B - A(i))";
by (fast_tac eq_cs 1);
qed "Diff_INT";

(** Unions and Intersections with General Sum **)

goal ZF.thy "Sigma(cons(a,B), C) = ({a}*C(a)) Un Sigma(B,C)";
by (fast_tac eq_cs 1);
qed "Sigma_cons";

goal ZF.thy "(SUM x:(UN y:A. C(y)). B(x)) = (UN y:A. SUM x:C(y). B(x))";
by (fast_tac eq_cs 1);
qed "SUM_UN_distrib1";

goal ZF.thy "(SUM i:I. UN j:J. C(i,j)) = (UN j:J. SUM i:I. C(i,j))";
by (fast_tac eq_cs 1);
qed "SUM_UN_distrib2";

goal ZF.thy "(SUM i:I Un J. C(i)) = (SUM i:I. C(i)) Un (SUM j:J. C(j))";
by (fast_tac eq_cs 1);
qed "SUM_Un_distrib1";

goal ZF.thy "(SUM i:I. A(i) Un B(i)) = (SUM i:I. A(i)) Un (SUM i:I. B(i))";
by (fast_tac eq_cs 1);
qed "SUM_Un_distrib2";

(*First-order version of the above, for rewriting*)
goal ZF.thy "I * (A Un B) = I*A Un I*B";
by (resolve_tac [SUM_Un_distrib2] 1);
qed "prod_Un_distrib2";

goal ZF.thy "(SUM i:I Int J. C(i)) = (SUM i:I. C(i)) Int (SUM j:J. C(j))";
by (fast_tac eq_cs 1);
qed "SUM_Int_distrib1";

goal ZF.thy
    "(SUM i:I. A(i) Int B(i)) = (SUM i:I. A(i)) Int (SUM i:I. B(i))";
by (fast_tac eq_cs 1);
qed "SUM_Int_distrib2";

(*First-order version of the above, for rewriting*)
goal ZF.thy "I * (A Int B) = I*A Int I*B";
by (resolve_tac [SUM_Int_distrib2] 1);
qed "prod_Int_distrib2";

(*Cf Aczel, Non-Well-Founded Sets, page 115*)
goal ZF.thy "(SUM i:I. A(i)) = (UN i:I. {i} * A(i))";
by (fast_tac eq_cs 1);
qed "SUM_eq_UN";

(** Domain **)

qed_goal "domain_of_prod" ZF.thy "!!A B. b:B ==> domain(A*B) = A"
 (fn _ => [ fast_tac eq_cs 1 ]);

qed_goal "domain_0" ZF.thy "domain(0) = 0"
 (fn _ => [ fast_tac eq_cs 1 ]);

qed_goal "domain_cons" ZF.thy
    "domain(cons(<a,b>,r)) = cons(a, domain(r))"
 (fn _ => [ fast_tac eq_cs 1 ]);

goal ZF.thy "domain(A Un B) = domain(A) Un domain(B)";
by (fast_tac eq_cs 1);
qed "domain_Un_eq";

goal ZF.thy "domain(A Int B) <= domain(A) Int domain(B)";
by (fast_tac eq_cs 1);
qed "domain_Int_subset";

goal ZF.thy "domain(A) - domain(B) <= domain(A - B)";
by (fast_tac eq_cs 1);
qed "domain_diff_subset";

goal ZF.thy "domain(converse(r)) = range(r)";
by (fast_tac eq_cs 1);
qed "domain_converse";



(** Range **)

qed_goal "range_of_prod" ZF.thy
    "!!a A B. a:A ==> range(A*B) = B"
 (fn _ => [ fast_tac eq_cs 1 ]);

qed_goal "range_0" ZF.thy "range(0) = 0"
 (fn _ => [ fast_tac eq_cs 1 ]); 

qed_goal "range_cons" ZF.thy
    "range(cons(<a,b>,r)) = cons(b, range(r))"
 (fn _ => [ fast_tac eq_cs 1 ]);

goal ZF.thy "range(A Un B) = range(A) Un range(B)";
by (fast_tac eq_cs 1);
qed "range_Un_eq";

goal ZF.thy "range(A Int B) <= range(A) Int range(B)";
by (fast_tac ZF_cs 1);
qed "range_Int_subset";

goal ZF.thy "range(A) - range(B) <= range(A - B)";
by (fast_tac eq_cs 1);
qed "range_diff_subset";

goal ZF.thy "range(converse(r)) = domain(r)";
by (fast_tac eq_cs 1);
qed "range_converse";

(** Field **)

qed_goal "field_of_prod" ZF.thy "field(A*A) = A"
 (fn _ => [ fast_tac eq_cs 1 ]); 

qed_goal "field_0" ZF.thy "field(0) = 0"
 (fn _ => [ fast_tac eq_cs 1 ]); 

qed_goal "field_cons" ZF.thy
    "field(cons(<a,b>,r)) = cons(a, cons(b, field(r)))"
 (fn _ => [ rtac equalityI 1, ALLGOALS (fast_tac ZF_cs) ]);

goal ZF.thy "field(A Un B) = field(A) Un field(B)";
by (fast_tac eq_cs 1);
qed "field_Un_eq";

goal ZF.thy "field(A Int B) <= field(A) Int field(B)";
by (fast_tac eq_cs 1);
qed "field_Int_subset";

goal ZF.thy "field(A) - field(B) <= field(A - B)";
by (fast_tac eq_cs 1);
qed "field_diff_subset";


(** Image **)

goal ZF.thy "r``0 = 0";
by (fast_tac eq_cs 1);
qed "image_0";

goal ZF.thy "r``(A Un B) = (r``A) Un (r``B)";
by (fast_tac eq_cs 1);
qed "image_Un";

goal ZF.thy "r``(A Int B) <= (r``A) Int (r``B)";
by (fast_tac ZF_cs 1);
qed "image_Int_subset";

goal ZF.thy "(r Int A*A)``B <= (r``B) Int A";
by (fast_tac ZF_cs 1);
qed "image_Int_square_subset";

goal ZF.thy "!!r. B<=A ==> (r Int A*A)``B = (r``B) Int A";
by (fast_tac eq_cs 1);
qed "image_Int_square";


(** Inverse Image **)

goal ZF.thy "r-``0 = 0";
by (fast_tac eq_cs 1);
qed "vimage_0";

goal ZF.thy "r-``(A Un B) = (r-``A) Un (r-``B)";
by (fast_tac eq_cs 1);
qed "vimage_Un";

goal ZF.thy "r-``(A Int B) <= (r-``A) Int (r-``B)";
by (fast_tac ZF_cs 1);
qed "vimage_Int_subset";

goal ZF.thy "(r Int A*A)-``B <= (r-``B) Int A";
by (fast_tac ZF_cs 1);
qed "vimage_Int_square_subset";

goal ZF.thy "!!r. B<=A ==> (r Int A*A)-``B = (r-``B) Int A";
by (fast_tac eq_cs 1);
qed "vimage_Int_square";


(** Converse **)

goal ZF.thy "converse(A Un B) = converse(A) Un converse(B)";
by (fast_tac eq_cs 1);
qed "converse_Un";

goal ZF.thy "converse(A Int B) = converse(A) Int converse(B)";
by (fast_tac eq_cs 1);
qed "converse_Int";

goal ZF.thy "converse(A) - converse(B) = converse(A - B)";
by (fast_tac eq_cs 1);
qed "converse_diff";

(*Does the analogue hold for INT?*)
goal ZF.thy "converse(UN x:A. B(x)) = (UN x:A. converse(B(x)))";
by (fast_tac eq_cs 1);
qed "converse_UN";

(** Pow **)

goal ZF.thy "Pow(A) Un Pow(B) <= Pow(A Un B)";
by (fast_tac upair_cs 1);
qed "Un_Pow_subset";

goal ZF.thy "(UN x:A. Pow(B(x))) <= Pow(UN x:A. B(x))";
by (fast_tac upair_cs 1);
qed "UN_Pow_subset";

goal ZF.thy "A <= Pow(Union(A))";
by (fast_tac upair_cs 1);
qed "subset_Pow_Union";

goal ZF.thy "Union(Pow(A)) = A";
by (fast_tac eq_cs 1);
qed "Union_Pow_eq";

goal ZF.thy "Pow(A) Int Pow(B) = Pow(A Int B)";
by (fast_tac eq_cs 1);
qed "Int_Pow_eq";

goal ZF.thy "!!x A. x:A ==> (INT x:A. Pow(B(x))) = Pow(INT x:A. B(x))";
by (fast_tac eq_cs 1);
qed "INT_Pow_subset";

(** RepFun **)

goal ZF.thy "{f(x).x:A}=0 <-> A=0";
by (fast_tac (eq_cs addSEs [equalityE]) 1);
qed "RepFun_eq_0_iff";

goal ZF.thy "{f(x).x:0} = 0";
by (fast_tac eq_cs 1);
qed "RepFun_0";
