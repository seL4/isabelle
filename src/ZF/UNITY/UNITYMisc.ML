(*  Title:      HOL/UNITY/UNITYMisc.ML
    ID:         $Id$
    Author:     Sidi O Ehmety, Computer Laboratory
    Copyright   2001  University of Cambridge

Some miscellaneous and add-hoc set theory concepts.

*)

Goalw [measure_def, less_than_def] 
         "less_than(A) = {<x,y>:A*A. x<y}";
by Auto_tac;
qed "less_than_equals";

Goalw [less_than_def] "wf(less_than(A))";
by (rtac wf_measure 1);
qed "wf_less_than";

Goalw [less_than_def, measure_def]
       "less_than(A)<= A*A";
by Auto_tac;
qed "less_than_subset";

Goalw [less_than_def, measure_def]
"<x,y>:less_than(A) <-> (x:A & y:A & x<y)";
by Auto_tac;
qed "less_than_iff";

Goalw [lessThan_def]
"i:lessThan(k,A) <-> i:A & i<k";
by Auto_tac;
qed "lessThan_iff";

Goalw [greaterThan_def]
"i:greaterThan(k,A) <-> i:A & k<i";
by Auto_tac;
qed "greaterThan_iff";



(** Needed for WF reasoning in WFair.ML **)

Goal "k:A ==>less_than(A)``{k} = greaterThan(k, A)";
by (rtac equalityI 1);
by (auto_tac (claset(), simpset() addsimps 
                [less_than_iff,greaterThan_iff]));
qed "Image_less_than";

Goal "k:A ==> less_than(A)-`` {k} = lessThan(k, A)";
by (rtac equalityI 1);
by (auto_tac (claset(), simpset() addsimps 
                [less_than_iff,lessThan_iff]));
qed "Image_inverse_less_than";

Addsimps [Image_less_than, Image_inverse_less_than];


(** Ad-hoc set-theory rules **)

Goal "(C Int A) Un (C Int B) = C Int (A Un B)";
by (Blast_tac 1);
qed "Int_Un_distrib2";

Goal "C Int (A - B) = (C Int A) - (C Int B)";
by (Blast_tac 1);
qed "Diff_Int_distrib";

Goal "(A - B) Int C = (A Int C) - (B Int C)";
by (Blast_tac 1);
qed "Diff_Int_distrib2";

Goal "A Un (A Un B) = A Un B";
by (Blast_tac 1);
qed "double_Un";

Goal "A Un (B Un C) = B Un (A Un C)";
by (Blast_tac 1);
qed "Un_assoc2";


val Un_ac = [Un_assoc, double_Un, Un_commute, Un_assoc2, Un_absorb];

Goal "A Un B = Union({A, B})";
by (Blast_tac 1);
qed "Un_eq_Union";

Goal "(UN x:A. {x}) = A";
by (Blast_tac 1);
qed "UN_singleton";


Goal "Union(B) Int A = (UN b:B. b Int A)";
by Auto_tac;
qed "Int_Union_Union";

Goal "A Int Union(B) = (UN b:B. A Int b)";
by Auto_tac;
qed "Int_Union_Union2";

(** Intersection **)
Goal "A Int (A Int B) = A Int B";
by (Blast_tac 1);
qed "double_Int";

Goal "A Int (B Int C) = B Int (A Int C)";
by (Blast_tac 1);
qed "Int_assoc2";

val Int_ac = [Int_assoc, double_Int, Int_commute, Int_assoc2];
  
Goal "A  Int B = 0 ==> A - B = A";
by (Blast_tac 1);
qed "Diff_triv";

Goal "A Int B - C = A Int (B - C)";
by (Blast_tac 1);
qed "Int_Diff";

Goal "f -``B = (UN y:B. f-``{y})";
by (Blast_tac 1);
qed "vimage_eq_UN";

Goal "A Un B - (A - B) = B";
by (Blast_tac 1);
qed "Un_Diff_Diff";
AddIffs [Un_Diff_Diff];

(*** INT simps ***)

Goal 
"i:I ==> (INT i:I. A(i)) Un B = (INT i:I. A(i) Un B)";
by Auto_tac;
qed "INT_Un_distrib";

Goal
 "!!C. c: C ==> (INT x:C. cons(a, B(x))) = cons(a, (INT x:C. B(x)))";
by Auto_tac;
qed "INT_cons";

Goal 
"i:I ==> (INT i:I. A(i)) Int B = (INT i:I. A(i) Int B)";
by Auto_tac;
qed "INT_Int_distrib2";

Goal 
"i:I ==> B Int (INT i:I. A(i)) = (INT i:I. B Int A(i))";
by Auto_tac;
qed "Int_INT_distrib";

val INT_simps = [Un_INT_distrib, Un_INT_distrib2, 
                 INT_constant, INT_Int_distrib, Diff_INT, 
                 INT_Un_distrib,INT_cons, INT_Int_distrib2, Int_INT_distrib, Inter_0];


(*** UN ***)
Goal
"!!C. c: C ==> cons(a, (UN x:C. B(x))) = (UN x:C. cons(a, B(x)))";
by Auto_tac;
qed "UN_cons";

Goal
 "!!C. c: C ==> B Un (UN x:C. A(x)) = (UN x:C. B  Un A(x))";
by Auto_tac;
qed "Un_UN_distrib";

Goal
"!!C. c: C ==> (UN x:C. B(x)) Un A   =  (UN x:C. B(x) Un A)";
by Auto_tac;
qed "UN_Un_distrib2";

Goal "(UN x:C. B(x)) Int A  = (UN x:C. B(x) Int A)";
by Auto_tac;
qed "UN_Int_distrib";

val UN_simps = [UN_cons, Un_UN_distrib, UN_Un_distrib2, UN_Un_distrib, UN_Int_distrib, UN_0];

(** Needed in State theory for the current definition of variables 
where they are indexed by lists  **)

Goal "i:list(nat) ==> i:univ(0)";
by (dres_inst_tac [("B", "0")] list_into_univ 1);
by (blast_tac (claset() addIs [nat_into_univ]) 1);
by (assume_tac 1);
qed "list_nat_into_univ";

(** To be moved to Update theory **)

Goalw [update_def] 
  "[| f:Pi(A,B); x:A; y:B(x) |] ==> f(x:=y):Pi(A, B)";
by (asm_simp_tac (simpset() addsimps [domain_of_fun, cons_absorb, 
                                      apply_funtype, lam_type]) 1);
qed "update_type2";

(** Simplication rules for Collect; To be moved elsewhere **)
Goal "{x:A. P(x)} Int A = {x:A. P(x)}";
by Auto_tac;
qed "Collect_Int2";

Goal "A Int {x:A. P(x)} = {x:A. P(x)}";
by Auto_tac;
qed "Collect_Int3";

AddIffs [Collect_Int2, Collect_Int3];


Goal "{x:A. P(x) | Q(x)} = Collect(A, P) Un Collect(A, Q)";
by Auto_tac;
qed "Collect_disj_eq";

Goal "{x:A. P(x) & Q(x)} = Collect(A, P) Int Collect(A, Q)";
by Auto_tac;
qed "Collect_conj_eq";



