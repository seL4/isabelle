(*  Title:      ZF/equalities
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1992  University of Cambridge

Set Theory examples: Union, Intersection, Inclusion, etc.
    (Thanks also to Philippe de Groote.)
*)

theory equalities = domrange:

(** Finite Sets **)

(* cons_def refers to Upair; reversing the equality LOOPS in rewriting!*)
lemma cons_eq: "{a} Un B = cons(a,B)"
by blast

lemma cons_commute: "cons(a, cons(b, C)) = cons(b, cons(a, C))"
by blast

lemma cons_absorb: "a: B ==> cons(a,B) = B"
by blast

lemma cons_Diff: "a: B ==> cons(a, B-{a}) = B"
by blast

lemma equal_singleton [rule_format]: "[| a: C;  ALL y:C. y=b |] ==> C = {b}"
by blast


(** Binary Intersection **)

(*NOT an equality, but it seems to belong here...*)
lemma Int_cons: "cons(a,B) Int C <= cons(a, B Int C)"
by blast

lemma Int_absorb [simp]: "A Int A = A"
by blast

lemma Int_left_absorb: "A Int (A Int B) = A Int B"
by blast

lemma Int_commute: "A Int B = B Int A"
by blast

lemma Int_left_commute: "A Int (B Int C) = B Int (A Int C)"
by blast

lemma Int_assoc: "(A Int B) Int C  =  A Int (B Int C)"
by blast

(*Intersection is an AC-operator*)
lemmas Int_ac= Int_assoc Int_left_absorb Int_commute Int_left_commute

lemma Int_Un_distrib: "A Int (B Un C) = (A Int B) Un (A Int C)"
by blast

lemma Int_Un_distrib2: "(B Un C) Int A = (B Int A) Un (C Int A)"
by blast

lemma subset_Int_iff: "A<=B <-> A Int B = A"
by (blast elim!: equalityE)

lemma subset_Int_iff2: "A<=B <-> B Int A = A"
by (blast elim!: equalityE)

lemma Int_Diff_eq: "C<=A ==> (A-B) Int C = C-B"
by blast

(** Binary Union **)

lemma Un_cons: "cons(a,B) Un C = cons(a, B Un C)"
by blast

lemma Un_absorb [simp]: "A Un A = A"
by blast

lemma Un_left_absorb: "A Un (A Un B) = A Un B"
by blast

lemma Un_commute: "A Un B = B Un A"
by blast

lemma Un_left_commute: "A Un (B Un C) = B Un (A Un C)"
by blast

lemma Un_assoc: "(A Un B) Un C  =  A Un (B Un C)"
by blast

(*Union is an AC-operator*)
lemmas Un_ac = Un_assoc Un_left_absorb Un_commute Un_left_commute

lemma Un_Int_distrib: "(A Int B) Un C  =  (A Un C) Int (B Un C)"
by blast

lemma subset_Un_iff: "A<=B <-> A Un B = B"
by (blast elim!: equalityE)

lemma subset_Un_iff2: "A<=B <-> B Un A = B"
by (blast elim!: equalityE)

lemma Un_empty [iff]: "(A Un B = 0) <-> (A = 0 & B = 0)"
by blast

lemma Un_eq_Union: "A Un B = Union({A, B})"
by blast

(** Simple properties of Diff -- set difference **)

lemma Diff_cancel: "A - A = 0"
by blast

lemma Diff_triv: "A  Int B = 0 ==> A - B = A"
by blast

lemma empty_Diff [simp]: "0 - A = 0"
by blast

lemma Diff_0 [simp]: "A - 0 = A"
by blast

lemma Diff_eq_0_iff: "A - B = 0 <-> A <= B"
by (blast elim: equalityE)

(*NOT SUITABLE FOR REWRITING since {a} == cons(a,0)*)
lemma Diff_cons: "A - cons(a,B) = A - B - {a}"
by blast

(*NOT SUITABLE FOR REWRITING since {a} == cons(a,0)*)
lemma Diff_cons2: "A - cons(a,B) = A - {a} - B"
by blast

lemma Diff_disjoint: "A Int (B-A) = 0"
by blast

lemma Diff_partition: "A<=B ==> A Un (B-A) = B"
by blast

lemma subset_Un_Diff: "A <= B Un (A - B)"
by blast

lemma double_complement: "[| A<=B; B<=C |] ==> B-(C-A) = A"
by blast

lemma double_complement_Un: "(A Un B) - (B-A) = A"
by blast

lemma Un_Int_crazy: 
 "(A Int B) Un (B Int C) Un (C Int A) = (A Un B) Int (B Un C) Int (C Un A)"
apply blast
done

lemma Diff_Un: "A - (B Un C) = (A-B) Int (A-C)"
by blast

lemma Diff_Int: "A - (B Int C) = (A-B) Un (A-C)"
by blast

lemma Un_Diff: "(A Un B) - C = (A - C) Un (B - C)"
by blast

lemma Int_Diff: "(A Int B) - C = A Int (B - C)"
by blast

lemma Diff_Int_distrib: "C Int (A-B) = (C Int A) - (C Int B)"
by blast

lemma Diff_Int_distrib2: "(A-B) Int C = (A Int C) - (B Int C)"
by blast

(*Halmos, Naive Set Theory, page 16.*)
lemma Un_Int_assoc_iff: "(A Int B) Un C = A Int (B Un C)  <->  C<=A"
by (blast elim!: equalityE)


(** Big Union and Intersection **)

lemma Union_cons [simp]: "Union(cons(a,B)) = a Un Union(B)"
by blast

lemma Union_Un_distrib: "Union(A Un B) = Union(A) Un Union(B)"
by blast

lemma Union_Int_subset: "Union(A Int B) <= Union(A) Int Union(B)"
by blast

lemma Union_disjoint: "Union(C) Int A = 0 <-> (ALL B:C. B Int A = 0)"
by (blast elim!: equalityE)

lemma Union_empty_iff: "Union(A) = 0 <-> (ALL B:A. B=0)"
by blast

lemma Inter_0: "Inter(0) = 0"
by (unfold Inter_def, blast)

lemma Inter_Un_subset: "[| z:A; z:B |] ==> Inter(A) Un Inter(B) <= Inter(A Int B)"
by blast

(* A good challenge: Inter is ill-behaved on the empty set *)
lemma Inter_Un_distrib:
     "[| a:A;  b:B |] ==> Inter(A Un B) = Inter(A) Int Inter(B)"
by blast

lemma Union_singleton: "Union({b}) = b"
by blast

lemma Inter_singleton: "Inter({b}) = b"
by blast

lemma Inter_cons [simp]:
     "Inter(cons(a,B)) = (if B=0 then a else a Int Inter(B))"
by force

(** Unions and Intersections of Families **)

lemma Union_eq_UN: "Union(A) = (UN x:A. x)"
by blast

lemma Inter_eq_INT: "Inter(A) = (INT x:A. x)"
by (unfold Inter_def, blast)

lemma UN_0 [simp]: "(UN i:0. A(i)) = 0"
by blast

lemma UN_singleton: "(UN x:A. {x}) = A"
by blast

lemma UN_Un: "(UN i: A Un B. C(i)) = (UN i: A. C(i)) Un (UN i:B. C(i))"
by blast

lemma INT_Un: "(INT i:I Un J. A(i)) = (if I=0 then INT j:J. A(j)  
                              else if J=0 then INT i:I. A(i)  
                              else ((INT i:I. A(i)) Int  (INT j:J. A(j))))"
apply auto
apply (blast intro!: equalityI)
done

lemma UN_UN_flatten: "(UN x : (UN y:A. B(y)). C(x)) = (UN y:A. UN x: B(y). C(x))"
by blast

(*Halmos, Naive Set Theory, page 35.*)
lemma Int_UN_distrib: "B Int (UN i:I. A(i)) = (UN i:I. B Int A(i))"
by blast

lemma Un_INT_distrib: "i:I ==> B Un (INT i:I. A(i)) = (INT i:I. B Un A(i))"
by blast

lemma Int_UN_distrib2:
     "(UN i:I. A(i)) Int (UN j:J. B(j)) = (UN i:I. UN j:J. A(i) Int B(j))"
by blast

lemma Un_INT_distrib2: "[| i:I;  j:J |] ==>  
      (INT i:I. A(i)) Un (INT j:J. B(j)) = (INT i:I. INT j:J. A(i) Un B(j))"
by blast

lemma UN_constant: "a: A ==> (UN y:A. c) = c"
by blast

lemma INT_constant: "a: A ==> (INT y:A. c) = c"
by blast

lemma UN_RepFun [simp]: "(UN y: RepFun(A,f). B(y)) = (UN x:A. B(f(x)))"
by blast

lemma INT_RepFun [simp]: "(INT x:RepFun(A,f). B(x))    = (INT a:A. B(f(a)))"
by (auto simp add: Inter_def)

lemma INT_Union_eq:
     "0 ~: A ==> (INT x: Union(A). B(x)) = (INT y:A. INT x:y. B(x))"
apply (simp add: Inter_def)
apply (subgoal_tac "ALL x:A. x~=0")
prefer 2 apply blast
apply force
done

lemma INT_UN_eq: "(ALL x:A. B(x) ~= 0)  
      ==> (INT z: (UN x:A. B(x)). C(z)) = (INT x:A. INT z: B(x). C(z))"
apply (subst INT_Union_eq, blast)
apply (simp add: Inter_def)
done


(** Devlin, Fundamentals of Contemporary Set Theory, page 12, exercise 5: 
    Union of a family of unions **)

lemma UN_Un_distrib:
     "(UN i:I. A(i) Un B(i)) = (UN i:I. A(i))  Un  (UN i:I. B(i))"
by blast

lemma INT_Int_distrib:
     "i:I ==> (INT i:I. A(i) Int B(i)) = (INT i:I. A(i)) Int (INT i:I. B(i))"
by blast

lemma UN_Int_subset:
     "(UN z:I Int J. A(z)) <= (UN z:I. A(z)) Int (UN z:J. A(z))"
by blast

(** Devlin, page 12, exercise 5: Complements **)

lemma Diff_UN: "i:I ==> B - (UN i:I. A(i)) = (INT i:I. B - A(i))"
by blast

lemma Diff_INT: "i:I ==> B - (INT i:I. A(i)) = (UN i:I. B - A(i))"
by blast

(** Unions and Intersections with General Sum **)

(*Not suitable for rewriting: LOOPS!*)
lemma Sigma_cons1: "Sigma(cons(a,B), C) = ({a}*C(a)) Un Sigma(B,C)"
by blast

(*Not suitable for rewriting: LOOPS!*)
lemma Sigma_cons2: "A * cons(b,B) = A*{b} Un A*B"
by blast

lemma Sigma_succ1: "Sigma(succ(A), B) = ({A}*B(A)) Un Sigma(A,B)"
by blast

lemma Sigma_succ2: "A * succ(B) = A*{B} Un A*B"
by blast

lemma SUM_UN_distrib1:
     "(SUM x:(UN y:A. C(y)). B(x)) = (UN y:A. SUM x:C(y). B(x))"
by blast

lemma SUM_UN_distrib2:
     "(SUM i:I. UN j:J. C(i,j)) = (UN j:J. SUM i:I. C(i,j))"
by blast

lemma SUM_Un_distrib1:
     "(SUM i:I Un J. C(i)) = (SUM i:I. C(i)) Un (SUM j:J. C(j))"
by blast

lemma SUM_Un_distrib2:
     "(SUM i:I. A(i) Un B(i)) = (SUM i:I. A(i)) Un (SUM i:I. B(i))"
by blast

(*First-order version of the above, for rewriting*)
lemma prod_Un_distrib2: "I * (A Un B) = I*A Un I*B"
by (rule SUM_Un_distrib2)

lemma SUM_Int_distrib1:
     "(SUM i:I Int J. C(i)) = (SUM i:I. C(i)) Int (SUM j:J. C(j))"
by blast

lemma SUM_Int_distrib2:
     "(SUM i:I. A(i) Int B(i)) = (SUM i:I. A(i)) Int (SUM i:I. B(i))"
by blast

(*First-order version of the above, for rewriting*)
lemma prod_Int_distrib2: "I * (A Int B) = I*A Int I*B"
by (rule SUM_Int_distrib2)

(*Cf Aczel, Non-Well-Founded Sets, page 115*)
lemma SUM_eq_UN: "(SUM i:I. A(i)) = (UN i:I. {i} * A(i))"
by blast

(** Domain **)

lemma domain_of_prod: "b:B ==> domain(A*B) = A"
by blast

lemma domain_0 [simp]: "domain(0) = 0"
by blast

lemma domain_cons [simp]: "domain(cons(<a,b>,r)) = cons(a, domain(r))"
by blast

lemma domain_Un_eq [simp]: "domain(A Un B) = domain(A) Un domain(B)"
by blast

lemma domain_Int_subset: "domain(A Int B) <= domain(A) Int domain(B)"
by blast

lemma domain_Diff_subset: "domain(A) - domain(B) <= domain(A - B)"
by blast

lemma domain_converse [simp]: "domain(converse(r)) = range(r)"
by blast

lemma domain_UN: "domain(UN x:A. B(x)) = (UN x:A. domain(B(x)))"
by blast

lemma domain_Union: "domain(Union(A)) = (UN x:A. domain(x))"
by blast


(** Range **)

lemma range_of_prod: "a:A ==> range(A*B) = B"
by blast

lemma range_0 [simp]: "range(0) = 0"
by blast

lemma range_cons [simp]: "range(cons(<a,b>,r)) = cons(b, range(r))"
by blast

lemma range_Un_eq [simp]: "range(A Un B) = range(A) Un range(B)"
by blast

lemma range_Int_subset: "range(A Int B) <= range(A) Int range(B)"
by blast

lemma range_Diff_subset: "range(A) - range(B) <= range(A - B)"
by blast

lemma range_converse [simp]: "range(converse(r)) = domain(r)"
by blast


(** Field **)

lemma field_of_prod: "field(A*A) = A"
by blast

lemma field_0 [simp]: "field(0) = 0"
by blast

lemma field_cons [simp]: "field(cons(<a,b>,r)) = cons(a, cons(b, field(r)))"
by blast

lemma field_Un_eq [simp]: "field(A Un B) = field(A) Un field(B)"
by blast

lemma field_Int_subset: "field(A Int B) <= field(A) Int field(B)"
by blast

lemma field_Diff_subset: "field(A) - field(B) <= field(A - B)"
by blast

lemma field_converse [simp]: "field(converse(r)) = field(r)"
by blast


(** Image **)

lemma image_0 [simp]: "r``0 = 0"
by blast

lemma image_Un [simp]: "r``(A Un B) = (r``A) Un (r``B)"
by blast

lemma image_Int_subset: "r``(A Int B) <= (r``A) Int (r``B)"
by blast

lemma image_Int_square_subset: "(r Int A*A)``B <= (r``B) Int A"
by blast

lemma image_Int_square: "B<=A ==> (r Int A*A)``B = (r``B) Int A"
by blast


(*Image laws for special relations*)
lemma image_0_left [simp]: "0``A = 0"
by blast

lemma image_Un_left: "(r Un s)``A = (r``A) Un (s``A)"
by blast

lemma image_Int_subset_left: "(r Int s)``A <= (r``A) Int (s``A)"
by blast


(** Inverse Image **)

lemma vimage_0 [simp]: "r-``0 = 0"
by blast

lemma vimage_Un [simp]: "r-``(A Un B) = (r-``A) Un (r-``B)"
by blast

lemma vimage_Int_subset: "r-``(A Int B) <= (r-``A) Int (r-``B)"
by blast

(*NOT suitable for rewriting*)
lemma vimage_eq_UN: "f -``B = (UN y:B. f-``{y})"
by blast

lemma function_vimage_Int:
     "function(f) ==> f-``(A Int B) = (f-``A)  Int  (f-``B)"
by (unfold function_def, blast)

lemma function_vimage_Diff: "function(f) ==> f-``(A-B) = (f-``A) - (f-``B)"
by (unfold function_def, blast)

lemma function_image_vimage: "function(f) ==> f `` (f-`` A) <= A"
by (unfold function_def, blast)

lemma vimage_Int_square_subset: "(r Int A*A)-``B <= (r-``B) Int A"
by blast

lemma vimage_Int_square: "B<=A ==> (r Int A*A)-``B = (r-``B) Int A"
by blast



(*Invese image laws for special relations*)
lemma vimage_0_left [simp]: "0-``A = 0"
by blast

lemma vimage_Un_left: "(r Un s)-``A = (r-``A) Un (s-``A)"
by blast

lemma vimage_Int_subset_left: "(r Int s)-``A <= (r-``A) Int (s-``A)"
by blast


(** Converse **)

lemma converse_Un [simp]: "converse(A Un B) = converse(A) Un converse(B)"
by blast

lemma converse_Int [simp]: "converse(A Int B) = converse(A) Int converse(B)"
by blast

lemma converse_Diff [simp]: "converse(A - B) = converse(A) - converse(B)"
by blast

lemma converse_UN [simp]: "converse(UN x:A. B(x)) = (UN x:A. converse(B(x)))"
by blast

(*Unfolding Inter avoids using excluded middle on A=0*)
lemma converse_INT [simp]:
     "converse(INT x:A. B(x)) = (INT x:A. converse(B(x)))"
apply (unfold Inter_def, blast)
done

(** Pow **)

lemma Pow_0 [simp]: "Pow(0) = {0}"
by blast

lemma Pow_insert: "Pow (cons(a,A)) = Pow(A) Un {cons(a,X) . X: Pow(A)}"
apply (rule equalityI, safe)
apply (erule swap)
apply (rule_tac a = "x-{a}" in RepFun_eqI, auto) 
done

lemma Un_Pow_subset: "Pow(A) Un Pow(B) <= Pow(A Un B)"
by blast

lemma UN_Pow_subset: "(UN x:A. Pow(B(x))) <= Pow(UN x:A. B(x))"
by blast

lemma subset_Pow_Union: "A <= Pow(Union(A))"
by blast

lemma Union_Pow_eq [simp]: "Union(Pow(A)) = A"
by blast

lemma Pow_Int_eq [simp]: "Pow(A Int B) = Pow(A) Int Pow(B)"
by blast

lemma Pow_INT_eq: "x:A ==> Pow(INT x:A. B(x)) = (INT x:A. Pow(B(x)))"
by blast

(** RepFun **)

lemma RepFun_eq_0_iff [simp]: "{f(x).x:A}=0 <-> A=0"
by blast

lemma RepFun_constant [simp]: "{c. x:A} = (if A=0 then 0 else {c})"
apply auto
apply blast
done

(** Collect **)

lemma Collect_Un: "Collect(A Un B, P) = Collect(A,P) Un Collect(B,P)"
by blast

lemma Collect_Int: "Collect(A Int B, P) = Collect(A,P) Int Collect(B,P)"
by blast

lemma Collect_Diff: "Collect(A - B, P) = Collect(A,P) - Collect(B,P)"
by blast

lemma Collect_cons: "{x:cons(a,B). P(x)} =  
      (if P(a) then cons(a, {x:B. P(x)}) else {x:B. P(x)})"
by (simp, blast)

lemma Int_Collect_self_eq: "A Int Collect(A,P) = Collect(A,P)"
by blast

lemma Collect_Collect_eq [simp]:
     "Collect(Collect(A,P), Q) = Collect(A, %x. P(x) & Q(x))"
by blast

lemma Collect_Int_Collect_eq:
     "Collect(A,P) Int Collect(A,Q) = Collect(A, %x. P(x) & Q(x))"
by blast

ML
{*
val cons_eq = thm "cons_eq";
val cons_commute = thm "cons_commute";
val cons_absorb = thm "cons_absorb";
val cons_Diff = thm "cons_Diff";
val equal_singleton = thm "equal_singleton";
val Int_cons = thm "Int_cons";
val Int_absorb = thm "Int_absorb";
val Int_left_absorb = thm "Int_left_absorb";
val Int_commute = thm "Int_commute";
val Int_left_commute = thm "Int_left_commute";
val Int_assoc = thm "Int_assoc";
val Int_Un_distrib = thm "Int_Un_distrib";
val Int_Un_distrib2 = thm "Int_Un_distrib2";
val subset_Int_iff = thm "subset_Int_iff";
val subset_Int_iff2 = thm "subset_Int_iff2";
val Int_Diff_eq = thm "Int_Diff_eq";
val Un_cons = thm "Un_cons";
val Un_absorb = thm "Un_absorb";
val Un_left_absorb = thm "Un_left_absorb";
val Un_commute = thm "Un_commute";
val Un_left_commute = thm "Un_left_commute";
val Un_assoc = thm "Un_assoc";
val Un_Int_distrib = thm "Un_Int_distrib";
val subset_Un_iff = thm "subset_Un_iff";
val subset_Un_iff2 = thm "subset_Un_iff2";
val Un_empty = thm "Un_empty";
val Un_eq_Union = thm "Un_eq_Union";
val Diff_cancel = thm "Diff_cancel";
val Diff_triv = thm "Diff_triv";
val empty_Diff = thm "empty_Diff";
val Diff_0 = thm "Diff_0";
val Diff_eq_0_iff = thm "Diff_eq_0_iff";
val Diff_cons = thm "Diff_cons";
val Diff_cons2 = thm "Diff_cons2";
val Diff_disjoint = thm "Diff_disjoint";
val Diff_partition = thm "Diff_partition";
val subset_Un_Diff = thm "subset_Un_Diff";
val double_complement = thm "double_complement";
val double_complement_Un = thm "double_complement_Un";
val Un_Int_crazy = thm "Un_Int_crazy";
val Diff_Un = thm "Diff_Un";
val Diff_Int = thm "Diff_Int";
val Un_Diff = thm "Un_Diff";
val Int_Diff = thm "Int_Diff";
val Diff_Int_distrib = thm "Diff_Int_distrib";
val Diff_Int_distrib2 = thm "Diff_Int_distrib2";
val Un_Int_assoc_iff = thm "Un_Int_assoc_iff";
val Union_cons = thm "Union_cons";
val Union_Un_distrib = thm "Union_Un_distrib";
val Union_Int_subset = thm "Union_Int_subset";
val Union_disjoint = thm "Union_disjoint";
val Union_empty_iff = thm "Union_empty_iff";
val Inter_0 = thm "Inter_0";
val Inter_Un_subset = thm "Inter_Un_subset";
val Inter_Un_distrib = thm "Inter_Un_distrib";
val Union_singleton = thm "Union_singleton";
val Inter_singleton = thm "Inter_singleton";
val Inter_cons = thm "Inter_cons";
val Union_eq_UN = thm "Union_eq_UN";
val Inter_eq_INT = thm "Inter_eq_INT";
val UN_0 = thm "UN_0";
val UN_singleton = thm "UN_singleton";
val UN_Un = thm "UN_Un";
val INT_Un = thm "INT_Un";
val UN_UN_flatten = thm "UN_UN_flatten";
val Int_UN_distrib = thm "Int_UN_distrib";
val Un_INT_distrib = thm "Un_INT_distrib";
val Int_UN_distrib2 = thm "Int_UN_distrib2";
val Un_INT_distrib2 = thm "Un_INT_distrib2";
val UN_constant = thm "UN_constant";
val INT_constant = thm "INT_constant";
val UN_RepFun = thm "UN_RepFun";
val INT_RepFun = thm "INT_RepFun";
val INT_Union_eq = thm "INT_Union_eq";
val INT_UN_eq = thm "INT_UN_eq";
val UN_Un_distrib = thm "UN_Un_distrib";
val INT_Int_distrib = thm "INT_Int_distrib";
val UN_Int_subset = thm "UN_Int_subset";
val Diff_UN = thm "Diff_UN";
val Diff_INT = thm "Diff_INT";
val Sigma_cons1 = thm "Sigma_cons1";
val Sigma_cons2 = thm "Sigma_cons2";
val Sigma_succ1 = thm "Sigma_succ1";
val Sigma_succ2 = thm "Sigma_succ2";
val SUM_UN_distrib1 = thm "SUM_UN_distrib1";
val SUM_UN_distrib2 = thm "SUM_UN_distrib2";
val SUM_Un_distrib1 = thm "SUM_Un_distrib1";
val SUM_Un_distrib2 = thm "SUM_Un_distrib2";
val prod_Un_distrib2 = thm "prod_Un_distrib2";
val SUM_Int_distrib1 = thm "SUM_Int_distrib1";
val SUM_Int_distrib2 = thm "SUM_Int_distrib2";
val prod_Int_distrib2 = thm "prod_Int_distrib2";
val SUM_eq_UN = thm "SUM_eq_UN";
val domain_of_prod = thm "domain_of_prod";
val domain_0 = thm "domain_0";
val domain_cons = thm "domain_cons";
val domain_Un_eq = thm "domain_Un_eq";
val domain_Int_subset = thm "domain_Int_subset";
val domain_Diff_subset = thm "domain_Diff_subset";
val domain_converse = thm "domain_converse";
val domain_UN = thm "domain_UN";
val domain_Union = thm "domain_Union";
val range_of_prod = thm "range_of_prod";
val range_0 = thm "range_0";
val range_cons = thm "range_cons";
val range_Un_eq = thm "range_Un_eq";
val range_Int_subset = thm "range_Int_subset";
val range_Diff_subset = thm "range_Diff_subset";
val range_converse = thm "range_converse";
val field_of_prod = thm "field_of_prod";
val field_0 = thm "field_0";
val field_cons = thm "field_cons";
val field_Un_eq = thm "field_Un_eq";
val field_Int_subset = thm "field_Int_subset";
val field_Diff_subset = thm "field_Diff_subset";
val field_converse = thm "field_converse";
val image_0 = thm "image_0";
val image_Un = thm "image_Un";
val image_Int_subset = thm "image_Int_subset";
val image_Int_square_subset = thm "image_Int_square_subset";
val image_Int_square = thm "image_Int_square";
val image_0_left = thm "image_0_left";
val image_Un_left = thm "image_Un_left";
val image_Int_subset_left = thm "image_Int_subset_left";
val vimage_0 = thm "vimage_0";
val vimage_Un = thm "vimage_Un";
val vimage_Int_subset = thm "vimage_Int_subset";
val vimage_eq_UN = thm "vimage_eq_UN";
val function_vimage_Int = thm "function_vimage_Int";
val function_vimage_Diff = thm "function_vimage_Diff";
val function_image_vimage = thm "function_image_vimage";
val vimage_Int_square_subset = thm "vimage_Int_square_subset";
val vimage_Int_square = thm "vimage_Int_square";
val vimage_0_left = thm "vimage_0_left";
val vimage_Un_left = thm "vimage_Un_left";
val vimage_Int_subset_left = thm "vimage_Int_subset_left";
val converse_Un = thm "converse_Un";
val converse_Int = thm "converse_Int";
val converse_Diff = thm "converse_Diff";
val converse_UN = thm "converse_UN";
val converse_INT = thm "converse_INT";
val Pow_0 = thm "Pow_0";
val Pow_insert = thm "Pow_insert";
val Un_Pow_subset = thm "Un_Pow_subset";
val UN_Pow_subset = thm "UN_Pow_subset";
val subset_Pow_Union = thm "subset_Pow_Union";
val Union_Pow_eq = thm "Union_Pow_eq";
val Pow_Int_eq = thm "Pow_Int_eq";
val Pow_INT_eq = thm "Pow_INT_eq";
val RepFun_eq_0_iff = thm "RepFun_eq_0_iff";
val RepFun_constant = thm "RepFun_constant";
val Collect_Un = thm "Collect_Un";
val Collect_Int = thm "Collect_Int";
val Collect_Diff = thm "Collect_Diff";
val Collect_cons = thm "Collect_cons";
val Int_Collect_self_eq = thm "Int_Collect_self_eq";
val Collect_Collect_eq = thm "Collect_Collect_eq";
val Collect_Int_Collect_eq = thm "Collect_Int_Collect_eq";

val Int_ac = thms "Int_ac";
val Un_ac = thms "Un_ac";

*}

end

