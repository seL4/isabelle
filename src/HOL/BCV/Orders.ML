(*  Title:      HOL/BCV/Orders.ML
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   1999 TUM
*)

Delrules[le_maxI1, le_maxI2];

(** option **)
section "option";

Goalw [option_def] "None : option A";
by (Simp_tac 1);
qed "None_in_option";
AddIffs [None_in_option];

Goalw [option_def] "(Some x : option A) = (x:A)";
by (Auto_tac);
qed "Some_in_option";
AddIffs [Some_in_option];

Goalw [less_option,le_option]
 "Some x < opt = (? y. opt = Some y & x < (y::'a::order))";
by (simp_tac (simpset() addsimps [order_less_le] addsplits [option.split]) 1);
qed_spec_mp "Some_less_conv";
AddIffs [Some_less_conv];

Goalw [less_option,le_option] "None < x = (? a. x = Some a)";
by (asm_simp_tac (simpset() addsplits [option.split]) 1);
qed_spec_mp "None_less_iff";
AddIffs [None_less_iff];


Goalw [acc_def] "acc A ==> acc(option A)";
by (asm_full_simp_tac (simpset() addsimps [wf_eq_minimal]) 1);
by (Clarify_tac 1);
by (case_tac "? a. Some a : Q" 1);
 by (eres_inst_tac [("x","{a . Some a : Q}")] allE 1);
 by (Blast_tac 1);
by (cases_tac "x" 1);
 by (Fast_tac 1);
by (Blast_tac 1);
qed "acc_option";
Addsimps [acc_option];
AddSIs [acc_option];


(** list **)
section "list";

Goalw [le_list] "~ [] <= x#xs";
by (Simp_tac 1);
qed "Nil_notle_Cons";

Goalw [le_list] "~ x#xs <= []";
by (Simp_tac 1);
qed "Cons_notle_Nil";

AddIffs [Nil_notle_Cons,Cons_notle_Nil];

Goalw [le_list] "x#xs <= y#ys = (x <= y & xs <= ys)";
by (rtac iffI 1);
 by (Asm_full_simp_tac 1);
 by (Clarify_tac 1);
 by (rtac conjI 1);
  by (eres_inst_tac [("x","0")] allE 1);
  by (Asm_full_simp_tac 1);
 by (Clarify_tac 1);
 by (eres_inst_tac [("x","Suc i")] allE 1);
 by (Asm_full_simp_tac 1);
by (Asm_full_simp_tac 1);
by (Clarify_tac 1);
by (cases_tac "i" 1);
by (ALLGOALS Asm_simp_tac);
qed "Cons_le_Cons";
AddIffs [Cons_le_Cons];

Goal "(x#xs <= ys) = (? z zs. ys = z#zs & x <= z & xs <= zs)";
by (cases_tac "ys" 1);
by (ALLGOALS Asm_simp_tac);
qed "Cons_le_iff";

Goal "(xs <= y#ys) = (? z zs. xs = z#zs & z <= y & zs <= ys)";
by (cases_tac "xs" 1);
by (ALLGOALS Asm_simp_tac);
qed "le_Cons_iff";

Goalw [less_list]
 "x#xs < y#ys = (x < (y::'a::order) & xs <= ys  |  x = y & xs < ys)";
by (simp_tac (simpset() addsimps [order_less_le]) 1);
by (Blast_tac 1);
qed "Cons_less_Cons";
AddIffs [Cons_less_Cons];

Goalw [le_list]
 "[| i<size xs; xs <= ys; x <= y |] ==> xs[i:=x] <= ys[i:=y]";
by (asm_full_simp_tac (simpset() addsimps [nth_list_update]) 1);
qed "list_update_le_cong";

Goal "!i < length xs. (xs[i := x] <= xs) = ((x::'a::order) <= xs!i)";
by (induct_tac "xs" 1);
 by (Simp_tac 1);
by (asm_simp_tac (simpset() addsplits [nat.split]) 1);
qed_spec_mp "list_update_le_conv";

Goalw [listsn_def] "xs : listsn n A ==> length xs = n";
by (Blast_tac 1);
qed "listsnE_length";
Addsimps [listsnE_length];

Goalw [listsn_def] "xs : listsn n A ==> set xs <= A";
by (Blast_tac 1);
qed "listsnE_set";
Addsimps [listsnE_set];

Goalw [listsn_def] "listsn 0 A = {[]}";
by (Auto_tac); 
qed "listsn_0";
Addsimps [listsn_0];

Goalw [listsn_def]
 "(xs : listsn (Suc n) A) = (? y:A. ? ys:listsn n A. xs = y#ys)";
by (cases_tac "xs" 1);
by (Auto_tac);
qed "in_listsn_Suc_iff";


Goal "? a. a:A ==> ? xs. xs : listsn n A";
by (induct_tac "n" 1);
 by (Simp_tac 1);
by (asm_simp_tac (simpset() addsimps [in_listsn_Suc_iff]) 1);
by (Blast_tac 1);
qed "listsn_not_empty";


Goal "!i n. length xs = n --> set xs <= A --> i < n --> (xs!i) : A";
by (induct_tac "xs" 1);
 by (Simp_tac 1);
by (asm_full_simp_tac (simpset() addsimps [nth_Cons] addsplits [nat.split]) 1);
qed_spec_mp "nth_in";
Addsimps [nth_in];

Goal "[| xs : listsn n A; i < n |] ==> (xs!i) : A";
by (blast_tac (HOL_cs addIs [nth_in,listsnE_length,listsnE_set]) 1);
qed "listsnE_nth_in";

Goalw [listsn_def]
 "[| xs : listsn n A; x:A; i < n |] ==> xs[i := x] : listsn n A";
by (Asm_full_simp_tac 1);
by (blast_tac (claset() addDs [set_update_subset_insert RS subsetD]) 1);
qed "list_update_in_listsn";
Addsimps [list_update_in_listsn];
AddSIs [list_update_in_listsn];


Goalw [acc_def] "acc(A) ==> acc(listsn n A)";
by (asm_full_simp_tac (simpset() addsimps [wf_eq_minimal]) 1);
by (induct_tac "n" 1);
 by (simp_tac (simpset() addcongs [conj_cong]) 1);
by (simp_tac (simpset() addsimps [in_listsn_Suc_iff]) 1);
by (Clarify_tac 1);
by (rename_tac "M m" 1);
by (case_tac "? x xs. x:A & xs:listsn n A & x#xs : M" 1);
 by (etac thin_rl 2);
 by (etac thin_rl 2);
 by (Blast_tac 2);
by (eres_inst_tac [("x","{a. a:A & (? xs. xs:listsn n A & a#xs:M)}")] allE 1);
by (etac impE 1);
 by (Blast_tac 1);
by (thin_tac "? x xs. ?P x xs" 1);
by (Clarify_tac 1);
by (rename_tac "maxA xs" 1);
by (eres_inst_tac [("x","{xs. xs:listsn n A & maxA#xs : M}")] allE 1);
by (Blast_tac 1);
qed "acc_listsn";
Addsimps [acc_listsn];
AddSIs [acc_listsn];
