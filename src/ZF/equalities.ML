(*  Title: 	ZF/equalities
    ID:         $Id$
    Author: 	Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1992  University of Cambridge

Set Theory examples: Union, Intersection, Inclusion, etc.
    (Thanks also to Philippe de Groote.)
*)

(** Finite Sets **)

goal ZF.thy "cons(a, cons(b, C)) = cons(b, cons(a, C))";
by (fast_tac eq_cs 1);
val cons_commute = result();

goal ZF.thy "!!B. a: B ==> cons(a,B) = B";
by (fast_tac eq_cs 1);
val cons_absorb = result();

goal ZF.thy "!!B. a: B ==> cons(a, B-{a}) = B";
by (fast_tac eq_cs 1);
val cons_Diff = result();

goal ZF.thy "!!C. [| a: C;  ALL y:C. y=b |] ==> C = {b}";
by (fast_tac eq_cs 1);
val equal_singleton_lemma = result();
val equal_singleton = ballI RSN (2,equal_singleton_lemma);


(** Binary Intersection **)

goal ZF.thy "0 Int A = 0";
by (fast_tac eq_cs 1);
val Int_0 = result();

(*NOT an equality, but it seems to belong here...*)
goal ZF.thy "cons(a,B) Int C <= cons(a, B Int C)";
by (fast_tac eq_cs 1);
val Int_cons = result();

goal ZF.thy "A Int A = A";
by (fast_tac eq_cs 1);
val Int_absorb = result();

goal ZF.thy "A Int B = B Int A";
by (fast_tac eq_cs 1);
val Int_commute = result();

goal ZF.thy "(A Int B) Int C  =  A Int (B Int C)";
by (fast_tac eq_cs 1);
val Int_assoc = result();

goal ZF.thy "(A Un B) Int C  =  (A Int C) Un (B Int C)";
by (fast_tac eq_cs 1);
val Int_Un_distrib = result();

goal ZF.thy "A<=B <-> A Int B = A";
by (fast_tac (eq_cs addSEs [equalityE]) 1);
val subset_Int_iff = result();

(** Binary Union **)

goal ZF.thy "0 Un A = A";
by (fast_tac eq_cs 1);
val Un_0 = result();

goal ZF.thy "cons(a,B) Un C = cons(a, B Un C)";
by (fast_tac eq_cs 1);
val Un_cons = result();

goal ZF.thy "A Un A = A";
by (fast_tac eq_cs 1);
val Un_absorb = result();

goal ZF.thy "A Un B = B Un A";
by (fast_tac eq_cs 1);
val Un_commute = result();

goal ZF.thy "(A Un B) Un C  =  A Un (B Un C)";
by (fast_tac eq_cs 1);
val Un_assoc = result();

goal ZF.thy "(A Int B) Un C  =  (A Un C) Int (B Un C)";
by (fast_tac eq_cs 1);
val Un_Int_distrib = result();

goal ZF.thy "A<=B <-> A Un B = B";
by (fast_tac (eq_cs addSEs [equalityE]) 1);
val subset_Un_iff = result();

(** Simple properties of Diff -- set difference **)

goal ZF.thy "A-A = 0";
by (fast_tac eq_cs 1);
val Diff_cancel = result();

goal ZF.thy "0-A = 0";
by (fast_tac eq_cs 1);
val empty_Diff = result();

goal ZF.thy "A-0 = A";
by (fast_tac eq_cs 1);
val Diff_0 = result();

(*NOT SUITABLE FOR REWRITING since {a} == cons(a,0)*)
goal ZF.thy "A - cons(a,B) = A - B - {a}";
by (fast_tac eq_cs 1);
val Diff_cons = result();

(*NOT SUITABLE FOR REWRITING since {a} == cons(a,0)*)
goal ZF.thy "A - cons(a,B) = A - {a} - B";
by (fast_tac eq_cs 1);
val Diff_cons2 = result();

goal ZF.thy "A Int (B-A) = 0";
by (fast_tac eq_cs 1);
val Diff_disjoint = result();

goal ZF.thy "!!A B. A<=B ==> A Un (B-A) = B";
by (fast_tac eq_cs 1);
val Diff_partition = result();

goal ZF.thy "!!A B. [| A<=B; B<= C |] ==> (B - (C-A)) = A";
by (fast_tac eq_cs 1);
val double_complement = result();

goal ZF.thy
 "(A Int B) Un (B Int C) Un (C Int A) = (A Un B) Int (B Un C) Int (C Un A)";
by (fast_tac eq_cs 1);
val Un_Int_crazy = result();

goal ZF.thy "A - (B Un C) = (A-B) Int (A-C)";
by (fast_tac eq_cs 1);
val Diff_Un = result();

goal ZF.thy "A - (B Int C) = (A-B) Un (A-C)";
by (fast_tac eq_cs 1);
val Diff_Int = result();

(*Halmos, Naive Set Theory, page 16.*)
goal ZF.thy "(A Int B) Un C = A Int (B Un C)  <->  C<=A";
by (fast_tac (eq_cs addSEs [equalityE]) 1);
val Un_Int_assoc_iff = result();


(** Big Union and Intersection **)

goal ZF.thy "Union(0) = 0";
by (fast_tac eq_cs 1);
val Union_0 = result();

goal ZF.thy "Union(cons(a,B)) = a Un Union(B)";
by (fast_tac eq_cs 1);
val Union_cons = result();

goal ZF.thy "Union(A Un B) = Union(A) Un Union(B)";
by (fast_tac eq_cs 1);
val Union_Un_distrib = result();

goal ZF.thy "Union(C) Int A = 0 <-> (ALL B:C. B Int A = 0)";
by (fast_tac (eq_cs addSEs [equalityE]) 1);
val Union_disjoint = result();

(* A good challenge: Inter is ill-behaved on the empty set *)
goal ZF.thy "!!A B. [| a:A;  b:B |] ==> Inter(A Un B) = Inter(A) Int Inter(B)";
by (fast_tac eq_cs 1);
val Inter_Un_distrib = result();

goal ZF.thy "Union({b}) = b";
by (fast_tac eq_cs 1);
val Union_singleton = result();

goal ZF.thy "Inter({b}) = b";
by (fast_tac eq_cs 1);
val Inter_singleton = result();

(** Unions and Intersections of Families **)

goal ZF.thy "Union(A) = (UN x:A. x)";
by (fast_tac eq_cs 1);
val Union_eq_UN = result();

goalw ZF.thy [Inter_def] "Inter(A) = (INT x:A. x)";
by (fast_tac eq_cs 1);
val Inter_eq_INT = result();

(*Halmos, Naive Set Theory, page 35.*)
goal ZF.thy "B Int (UN i:I. A(i)) = (UN i:I. B Int A(i))";
by (fast_tac eq_cs 1);
val Int_UN_distrib = result();

goal ZF.thy "!!A B. i:I ==> B Un (INT i:I. A(i)) = (INT i:I. B Un A(i))";
by (fast_tac eq_cs 1);
val Un_INT_distrib = result();

goal ZF.thy
    "(UN i:I. A(i)) Int (UN j:J. B(j)) = (UN i:I. UN j:J. A(i) Int B(j))";
by (fast_tac eq_cs 1);
val Int_UN_distrib2 = result();

goal ZF.thy
    "!!I J. [| i:I;  j:J |] ==> \
\    (INT i:I. A(i)) Un (INT j:J. B(j)) = (INT i:I. INT j:J. A(i) Un B(j))";
by (fast_tac eq_cs 1);
val Un_INT_distrib2 = result();

goal ZF.thy "!!A. [| a: A;  ALL y:A. b(y)=b(a) |] ==> (UN y:A. b(y)) = b(a)";
by (fast_tac (eq_cs addSEs [equalityE]) 1);
val UN_singleton_lemma = result();
val UN_singleton = ballI RSN (2,UN_singleton_lemma);

goal ZF.thy "!!A. [| a: A;  ALL y:A. b(y)=b(a) |] ==> (INT y:A. b(y)) = b(a)";
by (fast_tac (eq_cs addSEs [equalityE]) 1);
val INT_singleton_lemma = result();
val INT_singleton = ballI RSN (2,INT_singleton_lemma);

(** Devlin, Fundamentals of Contemporary Set Theory, page 12, exercise 5: 
    Union of a family of unions **)

goal ZF.thy "(UN i:I. A(x) Un B(x)) = (UN i:I. A(x))  Un  (UN i:I. B(x))";
by (fast_tac eq_cs 1);
val UN_Un_distrib = result();

goal ZF.thy
    "!!A B. i:I ==> \
\           (INT i:I. A(x)  Int  B(x)) = (INT i:I. A(x)) Int (INT i:I. B(x))";
by (fast_tac eq_cs 1);
val INT_Int_distrib = result();

(** Devlin, page 12, exercise 5: Complements **)

goal ZF.thy "!!A B. i:I ==> B - (UN i:I. A(i)) = (INT i:I. B - A(i))";
by (fast_tac eq_cs 1);
val Diff_UN = result();

goal ZF.thy "!!A B. i:I ==> B - (INT i:I. A(i)) = (UN i:I. B - A(i))";
by (fast_tac eq_cs 1);
val Diff_INT = result();

(** Unions and Intersections with General Sum **)

goal ZF.thy "(SUM x:(UN y:A. C(y)). B(x)) = (UN y:A. SUM x:C(y). B(x))";
by (fast_tac eq_cs 1);
val SUM_UN_distrib1 = result();

goal ZF.thy "(SUM x:A. UN y:B. C(x,y)) = (UN y:B. SUM x:A. C(x,y))";
by (fast_tac eq_cs 1);
val SUM_UN_distrib2 = result();

goal ZF.thy "(SUM x:A Un B. C(x)) = (SUM x:A. C(x)) Un (SUM x:B. C(x))";
by (fast_tac eq_cs 1);
val SUM_Un_distrib1 = result();

goal ZF.thy
    "(SUM i:I. A(x) Un B(x)) = (SUM i:I. A(x)) Un (SUM i:I. B(x))";
by (fast_tac eq_cs 1);
val SUM_Un_distrib2 = result();

goal ZF.thy "(SUM x:A Int B. C(x)) = (SUM x:A. C(x)) Int (SUM x:B. C(x))";
by (fast_tac eq_cs 1);
val SUM_Int_distrib1 = result();

goal ZF.thy
    "(SUM i:I. A(x) Int B(x)) = (SUM i:I. A(x)) Int (SUM i:I. B(x))";
by (fast_tac eq_cs 1);
val SUM_Int_distrib2 = result();

(** Domain, Range and Field **)

goal ZF.thy "domain(A Un B) = domain(A) Un domain(B)";
by (fast_tac eq_cs 1);
val domain_Un_eq = result();

goal ZF.thy "domain(A Int B) <= domain(A) Int domain(B)";
by (fast_tac eq_cs 1);
val domain_Int_subset = result();

goal ZF.thy "domain(A) - domain(B) <= domain(A - B)";
by (fast_tac eq_cs 1);
val domain_diff_subset = result();

goal ZF.thy "range(A Un B) = range(A) Un range(B)";
by (fast_tac eq_cs 1);
val range_Un_eq = result();

goal ZF.thy "range(A Int B) <= range(A) Int range(B)";
by (fast_tac eq_cs 1);
val range_Int_subset = result();

goal ZF.thy "range(A) - range(B) <= range(A - B)";
by (fast_tac eq_cs 1);
val range_diff_subset = result();

goal ZF.thy "field(A Un B) = field(A) Un field(B)";
by (fast_tac eq_cs 1);
val field_Un_eq = result();

goal ZF.thy "field(A Int B) <= field(A) Int field(B)";
by (fast_tac eq_cs 1);
val field_Int_subset = result();

goal ZF.thy "field(A) - field(B) <= field(A - B)";
by (fast_tac eq_cs 1);
val field_diff_subset = result();


(** Converse **)

goal ZF.thy "converse(A Un B) = converse(A) Un converse(B)";
by (fast_tac eq_cs 1);
val converse_Un = result();

goal ZF.thy "converse(A Int B) = converse(A) Int converse(B)";
by (fast_tac eq_cs 1);
val converse_Int = result();

goal ZF.thy "converse(A) - converse(B) = converse(A - B)";
by (fast_tac eq_cs 1);
val converse_diff = result();

