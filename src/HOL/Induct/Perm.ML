(*  Title:      HOL/ex/Perm.ML
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1995  University of Cambridge

Permutations: example of an inductive definition
*)

(*It would be nice to prove
    xs <~~> ys = (!x. count xs x = count ys x)
See mset on HOL/ex/Sorting.thy
*)

Goal "l <~~> l";
by (induct_tac "l" 1);
by (REPEAT (ares_tac perm.intrs 1));
qed "perm_refl";
AddIffs [perm_refl];

(** Some examples of rule induction on permutations **)

(*The form of the premise lets the induction bind xs and ys.*)
Goal "xs <~~> ys ==> xs=[] --> ys=[]";
by (etac perm.induct 1);
by (ALLGOALS Asm_simp_tac);
qed "perm_Nil_lemma";

(*A more general version is actually easier to understand!*)
Goal "xs <~~> ys ==> length(xs) = length(ys)";
by (etac perm.induct 1);
by (ALLGOALS Asm_simp_tac);
qed "perm_length";

Goal "xs <~~> ys ==> ys <~~> xs";
by (etac perm.induct 1);
by (REPEAT (ares_tac perm.intrs 1));
qed "perm_sym";

Goal "xs <~~> ys ==> x mem xs --> x mem ys";
by (etac perm.induct 1);
by (Fast_tac 4);
by (ALLGOALS Asm_simp_tac);
val perm_mem_lemma = result();

bind_thm ("perm_mem", perm_mem_lemma RS mp);

(** Ways of making new permutations **)

(*We can insert the head anywhere in the list*)
Goal "a # xs @ ys <~~> xs @ a # ys";
by (induct_tac "xs" 1);
by (ALLGOALS Simp_tac);
by (etac ([perm.swap, perm.Cons] MRS perm.trans) 1);
qed "perm_append_Cons";

Goal "xs@ys <~~> ys@xs";
by (induct_tac "xs" 1);
by (ALLGOALS Simp_tac);
by (etac ([perm.Cons, perm_append_Cons] MRS perm.trans) 1);
qed "perm_append_swap";


Goal "a # xs <~~> xs @ [a]";
by (rtac perm.trans 1);
by (rtac perm_append_swap 2);
by (Simp_tac 1);
qed "perm_append_single";

Goal "rev xs <~~> xs";
by (induct_tac "xs" 1);
by (ALLGOALS Simp_tac);
by (rtac (perm_append_single RS perm_sym RS perm.trans) 1);
by (etac perm.Cons 1);
qed "perm_rev";

Goal "xs <~~> ys ==> l@xs <~~> l@ys";
by (induct_tac "l" 1);
by (Simp_tac 1);
by (asm_simp_tac (simpset() addsimps [perm.Cons]) 1);
qed "perm_append1";

Goal "xs <~~> ys ==> xs@l <~~> ys@l";
by (rtac (perm_append_swap RS perm.trans) 1);
by (etac (perm_append1 RS perm.trans) 1);
by (rtac perm_append_swap 1);
qed "perm_append2";

(** Further results mostly by Thomas Marthedal Rasmussen **)

val perm_rules = [perm.trans, perm.swap, perm.Cons];

Goal "[] <~~> xs ==> xs = []";
by (rtac mp 1);
by (res_inst_tac [("ys","xs"),("xs","[]")] perm_Nil_lemma 1);
by Auto_tac;
qed "perm_empty_imp";

Goal "([] <~~> xs) = (xs = [])";
by (blast_tac (claset() addIs [perm_empty_imp]) 1);
qed "perm_empty";
AddIffs [perm_empty];

Goal "(xs <~~> []) = (xs = [])";
by Auto_tac;
by (etac (perm_sym RS perm_empty_imp) 1);
qed "perm_empty2";
AddIffs [perm_empty2];

Goal "ys <~~> xs ==> xs=[y] --> ys=[y]";
by (etac perm.induct 1);
by Auto_tac;
qed_spec_mp "perm_sing_imp";

Goal "(ys <~~> [y]) = (ys = [y])"; 
by (blast_tac (claset() addIs [perm_sing_imp]) 1);
qed "perm_sing_eq";
AddIffs [perm_sing_eq];

Goal "([y] <~~> ys) = (ys = [y])"; 
by Auto_tac;
by (dtac perm_sym 1);
by Auto_tac;
qed "perm_sing_eq2";
AddIffs [perm_sing_eq2];

Goal "x:set ys --> ys <~~> x#(remove x ys)";
by (induct_tac "ys" 1);
by (auto_tac (claset() addIs perm_rules, simpset()));
qed_spec_mp "perm_remove"; 

Goal "remove x (remove y l) = remove y (remove x l)";
by (induct_tac "l" 1);
by Auto_tac;
qed "remove_commute";

(*Congruence rule*)
Goal "xs <~~> ys ==> remove z xs <~~> remove z ys";
by (etac perm.induct 1);
by (auto_tac (claset() addIs perm_rules, simpset()));
by Auto_tac;
qed "perm_remove_perm";

Goal "remove z (z#xs) = xs";
by Auto_tac;
qed "remove_hd";
Addsimps [remove_hd];

Goal "z#xs <~~> z#ys ==> xs <~~> ys";
by (dres_inst_tac [("z","z")] perm_remove_perm 1);
by Auto_tac;
qed "cons_perm_imp_perm";

Goal "(z#xs <~~> z#ys) = (xs <~~> ys)";
by (blast_tac (claset() addIs [cons_perm_imp_perm, perm.Cons]) 1);
qed "cons_perm_eq";
AddIffs [cons_perm_eq];

Goal "ALL xs ys. zs@xs <~~> zs@ys --> xs <~~> ys";
by (res_inst_tac [("xs","zs")] rev_induct 1);
by (ALLGOALS Full_simp_tac);
by (blast_tac (claset() addSDs [spec]) 1);
qed_spec_mp "append_perm_imp_perm";

Goal "(zs@xs <~~> zs@ys) = (xs <~~> ys)";
by (blast_tac (claset() addIs [append_perm_imp_perm, perm_append1]) 1);
qed "perm_append1_eq";
AddIffs [perm_append1_eq];

Goal "(xs@zs <~~> ys@zs) = (xs <~~> ys)";
by (safe_tac (claset() addSIs [perm_append2]));
by (rtac append_perm_imp_perm 1);
by (rtac (perm_append_swap RS perm.trans) 1);
(*Not clear why this blast_tac alone can't find the proof.*)
by (blast_tac (claset() addIs [perm_append_swap, perm.trans]) 1);
qed "perm_append2_eq";
AddIffs [perm_append2_eq];
