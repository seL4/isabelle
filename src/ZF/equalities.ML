(*  Title:      ZF/equalities
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1992  University of Cambridge

Set Theory examples: Union, Intersection, Inclusion, etc.
    (Thanks also to Philippe de Groote.)
*)

(** Finite Sets **)

(* cons_def refers to Upair; reversing the equality LOOPS in rewriting!*)
Goal "{a} Un B = cons(a,B)";
by (Blast_tac 1);
qed "cons_eq";

Goal "cons(a, cons(b, C)) = cons(b, cons(a, C))";
by (Blast_tac 1);
qed "cons_commute";

Goal "a: B ==> cons(a,B) = B";
by (Blast_tac 1);
qed "cons_absorb";

Goal "a: B ==> cons(a, B-{a}) = B";
by (Blast_tac 1);
qed "cons_Diff";

Goal "[| a: C;  ALL y:C. y=b |] ==> C = {b}";
by (Blast_tac 1);
qed "equal_singleton_lemma";
val equal_singleton = ballI RSN (2,equal_singleton_lemma);


(** Binary Intersection **)

(*NOT an equality, but it seems to belong here...*)
Goal "cons(a,B) Int C <= cons(a, B Int C)";
by (Blast_tac 1);
qed "Int_cons";

Goal "A Int A = A";
by (Blast_tac 1);
qed "Int_absorb";

Goal "A Int B = B Int A";
by (Blast_tac 1);
qed "Int_commute";

Goal "(A Int B) Int C  =  A Int (B Int C)";
by (Blast_tac 1);
qed "Int_assoc";

Goal "(A Un B) Int C  =  (A Int C) Un (B Int C)";
by (Blast_tac 1);
qed "Int_Un_distrib";

Goal "A<=B <-> A Int B = A";
by (blast_tac (claset() addSEs [equalityE]) 1);
qed "subset_Int_iff";

Goal "A<=B <-> B Int A = A";
by (blast_tac (claset() addSEs [equalityE]) 1);
qed "subset_Int_iff2";

Goal "C<=A ==> (A-B) Int C = C-B";
by (Blast_tac 1);
qed "Int_Diff_eq";

(** Binary Union **)

Goal "cons(a,B) Un C = cons(a, B Un C)";
by (Blast_tac 1);
qed "Un_cons";

Goal "A Un A = A";
by (Blast_tac 1);
qed "Un_absorb";

Goal "A Un B = B Un A";
by (Blast_tac 1);
qed "Un_commute";

Goal "(A Un B) Un C  =  A Un (B Un C)";
by (Blast_tac 1);
qed "Un_assoc";

Goal "(A Int B) Un C  =  (A Un C) Int (B Un C)";
by (Blast_tac 1);
qed "Un_Int_distrib";

Goal "A<=B <-> A Un B = B";
by (blast_tac (claset() addSEs [equalityE]) 1);
qed "subset_Un_iff";

Goal "A<=B <-> B Un A = B";
by (blast_tac (claset() addSEs [equalityE]) 1);
qed "subset_Un_iff2";

(** Simple properties of Diff -- set difference **)

Goal "A-A = 0";
by (Blast_tac 1);
qed "Diff_cancel";

Goal "0-A = 0";
by (Blast_tac 1);
qed "empty_Diff";

Goal "A-0 = A";
by (Blast_tac 1);
qed "Diff_0";

Goal "A-B=0 <-> A<=B";
by (blast_tac (claset() addEs [equalityE]) 1);
qed "Diff_eq_0_iff";

(*NOT SUITABLE FOR REWRITING since {a} == cons(a,0)*)
Goal "A - cons(a,B) = A - B - {a}";
by (Blast_tac 1);
qed "Diff_cons";

(*NOT SUITABLE FOR REWRITING since {a} == cons(a,0)*)
Goal "A - cons(a,B) = A - {a} - B";
by (Blast_tac 1);
qed "Diff_cons2";

Goal "A Int (B-A) = 0";
by (Blast_tac 1);
qed "Diff_disjoint";

Goal "A<=B ==> A Un (B-A) = B";
by (Blast_tac 1);
qed "Diff_partition";

Goal "A <= B Un (A - B)";
by (Blast_tac 1);
qed "subset_Un_Diff";

Goal "[| A<=B; B<=C |] ==> B-(C-A) = A";
by (Blast_tac 1);
qed "double_complement";

Goal "(A Un B) - (B-A) = A";
by (Blast_tac 1);
qed "double_complement_Un";

Goal
 "(A Int B) Un (B Int C) Un (C Int A) = (A Un B) Int (B Un C) Int (C Un A)";
by (Blast_tac 1);
qed "Un_Int_crazy";

Goal "A - (B Un C) = (A-B) Int (A-C)";
by (Blast_tac 1);
qed "Diff_Un";

Goal "A - (B Int C) = (A-B) Un (A-C)";
by (Blast_tac 1);
qed "Diff_Int";

(*Halmos, Naive Set Theory, page 16.*)
Goal "(A Int B) Un C = A Int (B Un C)  <->  C<=A";
by (blast_tac (claset() addSEs [equalityE]) 1);
qed "Un_Int_assoc_iff";


(** Big Union and Intersection **)

Goal "Union(cons(a,B)) = a Un Union(B)";
by (Blast_tac 1);
qed "Union_cons";

Goal "Union(A Un B) = Union(A) Un Union(B)";
by (Blast_tac 1);
qed "Union_Un_distrib";

Goal "Union(A Int B) <= Union(A) Int Union(B)";
by (Blast_tac 1);
qed "Union_Int_subset";

Goal "Union(C) Int A = 0 <-> (ALL B:C. B Int A = 0)";
by (blast_tac (claset() addSEs [equalityE]) 1);
qed "Union_disjoint";

Goal "Union(A) = 0 <-> (ALL B:A. B=0)";
by (Blast_tac 1);
qed "Union_empty_iff";

Goalw [Inter_def] "Inter(0) = 0";
by (Blast_tac 1);
qed "Inter_0";

Goal "[| z:A; z:B |] ==> Inter(A) Un Inter(B) <= Inter(A Int B)";
by (Blast_tac 1);
qed "Inter_Un_subset";

(* A good challenge: Inter is ill-behaved on the empty set *)
Goal "[| a:A;  b:B |] ==> Inter(A Un B) = Inter(A) Int Inter(B)";
by (Blast_tac 1);
qed "Inter_Un_distrib";

Goal "Union({b}) = b";
by (Blast_tac 1);
qed "Union_singleton";

Goal "Inter({b}) = b";
by (Blast_tac 1);
qed "Inter_singleton";

(** Unions and Intersections of Families **)

Goal "Union(A) = (UN x:A. x)";
by (Blast_tac 1);
qed "Union_eq_UN";

Goalw [Inter_def] "Inter(A) = (INT x:A. x)";
by (Blast_tac 1);
qed "Inter_eq_INT";

Goal "(UN i:0. A(i)) = 0";
by (Blast_tac 1);
qed "UN_0";

(*Halmos, Naive Set Theory, page 35.*)
Goal "B Int (UN i:I. A(i)) = (UN i:I. B Int A(i))";
by (Blast_tac 1);
qed "Int_UN_distrib";

Goal "i:I ==> B Un (INT i:I. A(i)) = (INT i:I. B Un A(i))";
by (Blast_tac 1);
qed "Un_INT_distrib";

Goal "(UN i:I. A(i)) Int (UN j:J. B(j)) = (UN i:I. UN j:J. A(i) Int B(j))";
by (Blast_tac 1);
qed "Int_UN_distrib2";

Goal "[| i:I;  j:J |] ==> \
\     (INT i:I. A(i)) Un (INT j:J. B(j)) = (INT i:I. INT j:J. A(i) Un B(j))";
by (Blast_tac 1);
qed "Un_INT_distrib2";

Goal "a: A ==> (UN y:A. c) = c";
by (Blast_tac 1);
qed "UN_constant";

Goal "a: A ==> (INT y:A. c) = c";
by (Blast_tac 1);
qed "INT_constant";

Goal "(UN y: RepFun(A,f). B(y)) = (UN x:A. B(f(x)))";
by (Blast_tac 1);
qed "UN_RepFun";

Goal "x:A ==> (INT y: RepFun(A,f). B(y)) = (INT x:A. B(f(x)))";
by (Blast_tac 1);
qed "INT_RepFun";

Addsimps [UN_RepFun, INT_RepFun];


(** Devlin, Fundamentals of Contemporary Set Theory, page 12, exercise 5: 
    Union of a family of unions **)

Goal "(UN i:I. A(i) Un B(i)) = (UN i:I. A(i))  Un  (UN i:I. B(i))";
by (Blast_tac 1);
qed "UN_Un_distrib";

Goal "i:I ==> (INT i:I. A(i) Int B(i)) = (INT i:I. A(i)) Int (INT i:I. B(i))";
by (Blast_tac 1);
qed "INT_Int_distrib";

Goal "(UN z:I Int J. A(z)) <= (UN z:I. A(z)) Int (UN z:J. A(z))";
by (Blast_tac 1);
qed "UN_Int_subset";

(** Devlin, page 12, exercise 5: Complements **)

Goal "i:I ==> B - (UN i:I. A(i)) = (INT i:I. B - A(i))";
by (Blast_tac 1);
qed "Diff_UN";

Goal "i:I ==> B - (INT i:I. A(i)) = (UN i:I. B - A(i))";
by (Blast_tac 1);
qed "Diff_INT";

(** Unions and Intersections with General Sum **)

(*Not suitable for rewriting: LOOPS!*)
Goal "Sigma(cons(a,B), C) = ({a}*C(a)) Un Sigma(B,C)";
by (Blast_tac 1);
qed "Sigma_cons1";

(*Not suitable for rewriting: LOOPS!*)
Goal "A * cons(b,B) = A*{b} Un A*B";
by (Blast_tac 1);
qed "Sigma_cons2";

Goal "Sigma(succ(A), B) = ({A}*B(A)) Un Sigma(A,B)";
by (Blast_tac 1);
qed "Sigma_succ1";

Goal "A * succ(B) = A*{B} Un A*B";
by (Blast_tac 1);
qed "Sigma_succ2";

Goal "(SUM x:(UN y:A. C(y)). B(x)) = (UN y:A. SUM x:C(y). B(x))";
by (Blast_tac 1);
qed "SUM_UN_distrib1";

Goal "(SUM i:I. UN j:J. C(i,j)) = (UN j:J. SUM i:I. C(i,j))";
by (Blast_tac 1);
qed "SUM_UN_distrib2";

Goal "(SUM i:I Un J. C(i)) = (SUM i:I. C(i)) Un (SUM j:J. C(j))";
by (Blast_tac 1);
qed "SUM_Un_distrib1";

Goal "(SUM i:I. A(i) Un B(i)) = (SUM i:I. A(i)) Un (SUM i:I. B(i))";
by (Blast_tac 1);
qed "SUM_Un_distrib2";

(*First-order version of the above, for rewriting*)
Goal "I * (A Un B) = I*A Un I*B";
by (rtac SUM_Un_distrib2 1);
qed "prod_Un_distrib2";

Goal "(SUM i:I Int J. C(i)) = (SUM i:I. C(i)) Int (SUM j:J. C(j))";
by (Blast_tac 1);
qed "SUM_Int_distrib1";

Goal "(SUM i:I. A(i) Int B(i)) = (SUM i:I. A(i)) Int (SUM i:I. B(i))";
by (Blast_tac 1);
qed "SUM_Int_distrib2";

(*First-order version of the above, for rewriting*)
Goal "I * (A Int B) = I*A Int I*B";
by (rtac SUM_Int_distrib2 1);
qed "prod_Int_distrib2";

(*Cf Aczel, Non-Well-Founded Sets, page 115*)
Goal "(SUM i:I. A(i)) = (UN i:I. {i} * A(i))";
by (Blast_tac 1);
qed "SUM_eq_UN";

(** Domain **)

Goal "b:B ==> domain(A*B) = A";
by (Blast_tac 1);
qed "domain_of_prod";

Goal "domain(0) = 0";
by (Blast_tac 1);
qed "domain_0";

Goal "domain(cons(<a,b>,r)) = cons(a, domain(r))";
by (Blast_tac 1);
qed "domain_cons";

Goal "domain(A Un B) = domain(A) Un domain(B)";
by (Blast_tac 1);
qed "domain_Un_eq";

Goal "domain(A Int B) <= domain(A) Int domain(B)";
by (Blast_tac 1);
qed "domain_Int_subset";

Goal "domain(A) - domain(B) <= domain(A - B)";
by (Blast_tac 1);
qed "domain_Diff_subset";

Goal "domain(converse(r)) = range(r)";
by (Blast_tac 1);
qed "domain_converse";

Addsimps [domain_0, domain_cons, domain_Un_eq, domain_converse];


(** Range **)

Goal "a:A ==> range(A*B) = B";
by (Blast_tac 1);
qed "range_of_prod";

Goal "range(0) = 0";
by (Blast_tac 1);
qed "range_0"; 

Goal "range(cons(<a,b>,r)) = cons(b, range(r))";
by (Blast_tac 1);
qed "range_cons";

Goal "range(A Un B) = range(A) Un range(B)";
by (Blast_tac 1);
qed "range_Un_eq";

Goal "range(A Int B) <= range(A) Int range(B)";
by (Blast_tac 1);
qed "range_Int_subset";

Goal "range(A) - range(B) <= range(A - B)";
by (Blast_tac 1);
qed "range_Diff_subset";

Goal "range(converse(r)) = domain(r)";
by (Blast_tac 1);
qed "range_converse";

Addsimps [range_0, range_cons, range_Un_eq, range_converse];


(** Field **)

Goal "field(A*A) = A";
by (Blast_tac 1);
qed "field_of_prod"; 

Goal "field(0) = 0";
by (Blast_tac 1);
qed "field_0"; 

Goal "field(cons(<a,b>,r)) = cons(a, cons(b, field(r)))";
by (rtac equalityI 1);
by (ALLGOALS Blast_tac) ;
qed "field_cons";

Goal "field(A Un B) = field(A) Un field(B)";
by (Blast_tac 1);
qed "field_Un_eq";

Goal "field(A Int B) <= field(A) Int field(B)";
by (Blast_tac 1);
qed "field_Int_subset";

Goal "field(A) - field(B) <= field(A - B)";
by (Blast_tac 1);
qed "field_Diff_subset";

Goal "field(converse(r)) = field(r)";
by (Blast_tac 1);
qed "field_converse";

Addsimps [field_0, field_cons, field_Un_eq, field_converse];


(** Image **)

Goal "r``0 = 0";
by (Blast_tac 1);
qed "image_0";

Goal "r``(A Un B) = (r``A) Un (r``B)";
by (Blast_tac 1);
qed "image_Un";

Goal "r``(A Int B) <= (r``A) Int (r``B)";
by (Blast_tac 1);
qed "image_Int_subset";

Goal "(r Int A*A)``B <= (r``B) Int A";
by (Blast_tac 1);
qed "image_Int_square_subset";

Goal "B<=A ==> (r Int A*A)``B = (r``B) Int A";
by (Blast_tac 1);
qed "image_Int_square";

Addsimps [image_0, image_Un];

(*Image laws for special relations*)
Goal "0``A = 0";
by (Blast_tac 1);
qed "image_0_left";
Addsimps [image_0_left];

Goal "(r Un s)``A = (r``A) Un (s``A)";
by (Blast_tac 1);
qed "image_Un_left";

Goal "(r Int s)``A <= (r``A) Int (s``A)";
by (Blast_tac 1);
qed "image_Int_subset_left";


(** Inverse Image **)

Goal "r-``0 = 0";
by (Blast_tac 1);
qed "vimage_0";

Goal "r-``(A Un B) = (r-``A) Un (r-``B)";
by (Blast_tac 1);
qed "vimage_Un";

Goal "r-``(A Int B) <= (r-``A) Int (r-``B)";
by (Blast_tac 1);
qed "vimage_Int_subset";

Goalw [function_def] "function(f) ==> f-``(A Int B) = (f-``A)  Int  (f-``B)";
by (Blast_tac 1);
qed "function_vimage_Int";

Goalw [function_def] "function(f) ==> f-``(A-B) = (f-``A) - (f-``B)";
by (Blast_tac 1);
qed "function_vimage_Diff";

Goalw [function_def] "function(f) ==> f `` (f-`` A) <= A";
by (Blast_tac 1);
qed "function_image_vimage";

Goal "(r Int A*A)-``B <= (r-``B) Int A";
by (Blast_tac 1);
qed "vimage_Int_square_subset";

Goal "B<=A ==> (r Int A*A)-``B = (r-``B) Int A";
by (Blast_tac 1);
qed "vimage_Int_square";

Addsimps [vimage_0, vimage_Un];


(*Invese image laws for special relations*)
Goal "0-``A = 0";
by (Blast_tac 1);
qed "vimage_0_left";
Addsimps [vimage_0_left];

Goal "(r Un s)-``A = (r-``A) Un (s-``A)";
by (Blast_tac 1);
qed "vimage_Un_left";

Goal "(r Int s)-``A <= (r-``A) Int (s-``A)";
by (Blast_tac 1);
qed "vimage_Int_subset_left";


(** Converse **)

Goal "converse(A Un B) = converse(A) Un converse(B)";
by (Blast_tac 1);
qed "converse_Un";

Goal "converse(A Int B) = converse(A) Int converse(B)";
by (Blast_tac 1);
qed "converse_Int";

Goal "converse(A - B) = converse(A) - converse(B)";
by (Blast_tac 1);
qed "converse_Diff";

Goal "converse(UN x:A. B(x)) = (UN x:A. converse(B(x)))";
by (Blast_tac 1);
qed "converse_UN";

(*Unfolding Inter avoids using excluded middle on A=0*)
Goalw [Inter_def] "converse(INT x:A. B(x)) = (INT x:A. converse(B(x)))";
by (Blast_tac 1);
qed "converse_INT";

Addsimps [converse_Un, converse_Int, converse_Diff, converse_UN, converse_INT];

(** Pow **)

Goal "Pow(0) = {0}";
by (Blast_tac 1);
qed "Pow_0";

Goal "Pow (cons(a,A)) = Pow(A) Un {cons(a,X) . X: Pow(A)}";
by (rtac equalityI 1);
by Safe_tac;
by (etac swap 1);
by (res_inst_tac [("a", "x-{a}")] RepFun_eqI 1);
by (ALLGOALS Blast_tac);
qed "Pow_insert";

Goal "Pow(A) Un Pow(B) <= Pow(A Un B)";
by (Blast_tac 1);
qed "Un_Pow_subset";

Goal "(UN x:A. Pow(B(x))) <= Pow(UN x:A. B(x))";
by (Blast_tac 1);
qed "UN_Pow_subset";

Goal "A <= Pow(Union(A))";
by (Blast_tac 1);
qed "subset_Pow_Union";

Goal "Union(Pow(A)) = A";
by (Blast_tac 1);
qed "Union_Pow_eq";

Goal "Pow(A Int B) = Pow(A) Int Pow(B)";
by (Blast_tac 1);
qed "Pow_Int_eq";

Goal "x:A ==> Pow(INT x:A. B(x)) = (INT x:A. Pow(B(x)))";
by (Blast_tac 1);
qed "Pow_INT_eq";

Addsimps [Pow_0, Union_Pow_eq, Pow_Int_eq];

(** RepFun **)

Goal "{f(x).x:A}=0 <-> A=0";
	(*blast_tac takes too long to find a good depth*)
by (Blast.depth_tac (claset() addSEs [equalityE]) 10 1);
qed "RepFun_eq_0_iff";

(** Collect **)

Goal "Collect(A Un B, P) = Collect(A,P) Un Collect(B,P)";
by (Blast_tac 1);
qed "Collect_Un";

Goal "Collect(A Int B, P) = Collect(A,P) Int Collect(B,P)";
by (Blast_tac 1);
qed "Collect_Int";

Goal "Collect(A - B, P) = Collect(A,P) - Collect(B,P)";
by (Blast_tac 1);
qed "Collect_Diff";

Goal "{x:cons(a,B). P(x)} = \
\     (if P(a) then cons(a, {x:B. P(x)}) else {x:B. P(x)})";
by (simp_tac (simpset() addsplits [split_if]) 1);
by (Blast_tac 1);
qed "Collect_cons";

