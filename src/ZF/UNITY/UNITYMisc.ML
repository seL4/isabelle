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

Goal "Union(B) Int A = (UN b:B. b Int A)";
by Auto_tac;
qed "Int_Union_Union";

Goal "A Int Union(B) = (UN b:B. A Int b)";
by Auto_tac;
qed "Int_Union_Union2";

Goal "A Un B - (A - B) = B";
by (Blast_tac 1);
qed "Un_Diff_Diff";
AddIffs [Un_Diff_Diff];


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



