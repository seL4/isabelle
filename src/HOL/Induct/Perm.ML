(*  Title:      HOL/ex/Perm.ML
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1995  University of Cambridge

Permutations: example of an inductive definition
*)

(*It would be nice to prove (for "multiset", defined on HOL/ex/Sorting.thy)
    xs <~~> ys = (ALL x. multiset xs x = multiset ys x)
*)

AddIs perm.intrs;

Goal "l <~~> l";
by (induct_tac "l" 1);
by Auto_tac;
qed "perm_refl";
AddIffs [perm_refl];

(** Some examples of rule induction on permutations **)

(*The form of the premise lets the induction bind xs and ys.*)
Goal "xs <~~> ys ==> xs=[] --> ys=[]";
by (etac perm.induct 1);
by (ALLGOALS Asm_simp_tac);
bind_thm ("xperm_empty_imp",    (* [] <~~> ys ==> ys=[] *)
	  [refl, result()] MRS rev_mp);

(*This more general theorem is easier to understand!*)
Goal "xs <~~> ys ==> length(xs) = length(ys)";
by (etac perm.induct 1);
by (ALLGOALS Asm_simp_tac);
qed "perm_length";

Goal "[] <~~> xs ==> xs=[]";
by (dtac perm_length 1);
by Auto_tac;
qed "perm_empty_imp";

Goal "xs <~~> ys ==> ys <~~> xs";
by (etac perm.induct 1);
by Auto_tac;
qed "perm_sym";

Goal "xs <~~> ys ==> x mem xs --> x mem ys";
by (etac perm.induct 1);
by Auto_tac;
val perm_mem_lemma = result();

bind_thm ("perm_mem", perm_mem_lemma RS mp);

(** Ways of making new permutations **)

(*We can insert the head anywhere in the list*)
Goal "a # xs @ ys <~~> xs @ a # ys";
by (induct_tac "xs" 1);
by Auto_tac;
qed "perm_append_Cons";

Goal "xs@ys <~~> ys@xs";
by (induct_tac "xs" 1);
by (ALLGOALS Simp_tac);
by (blast_tac (claset() addIs [perm_append_Cons]) 1);
qed "perm_append_swap";

Goal "a # xs <~~> xs @ [a]";
by (rtac perm.trans 1);
by (rtac perm_append_swap 2);
by (Simp_tac 1);
qed "perm_append_single";

Goal "rev xs <~~> xs";
by (induct_tac "xs" 1);
by (ALLGOALS Simp_tac);
by (blast_tac (claset() addIs [perm_sym, perm_append_single]) 1);
qed "perm_rev";

Goal "xs <~~> ys ==> l@xs <~~> l@ys";
by (induct_tac "l" 1);
by Auto_tac;
qed "perm_append1";

Goal "xs <~~> ys ==> xs@l <~~> ys@l";
by (blast_tac (claset() addSIs [perm_append_swap, perm_append1]) 1);
qed "perm_append2";

(** Further results mostly by Thomas Marthedal Rasmussen **)

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
by (blast_tac (claset() addDs [perm_sym]) 1);
qed "perm_sing_eq2";
AddIffs [perm_sing_eq2];

Goal "x:set ys --> ys <~~> x#(remove x ys)";
by (induct_tac "ys" 1);
by Auto_tac;
qed_spec_mp "perm_remove"; 

Goal "remove x (remove y l) = remove y (remove x l)";
by (induct_tac "l" 1);
by Auto_tac;
qed "remove_commute";

(*Congruence rule*)
Goal "xs <~~> ys ==> remove z xs <~~> remove z ys";
by (etac perm.induct 1);
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
by (blast_tac (claset() addIs [cons_perm_imp_perm]) 1);
qed "cons_perm_eq";
AddIffs [cons_perm_eq];

Goal "ALL xs ys. zs@xs <~~> zs@ys --> xs <~~> ys";
by (rev_induct_tac "zs" 1);
by (ALLGOALS Full_simp_tac);
by (Blast_tac 1);
qed_spec_mp "append_perm_imp_perm";

Goal "(zs@xs <~~> zs@ys) = (xs <~~> ys)";
by (blast_tac (claset() addIs [append_perm_imp_perm, perm_append1]) 1);
qed "perm_append1_eq";
AddIffs [perm_append1_eq];

Goal "(xs@zs <~~> ys@zs) = (xs <~~> ys)";
by (safe_tac (claset() addSIs [perm_append2]));
by (rtac append_perm_imp_perm 1);
by (rtac (perm_append_swap RS perm.trans) 1);
(*The previous step helps this blast_tac call succeed quickly.*)
by (blast_tac (claset() addIs [perm_append_swap]) 1);
qed "perm_append2_eq";
AddIffs [perm_append2_eq];
