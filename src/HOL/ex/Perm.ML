(*  Title: 	HOL/ex/Perm.ML
    ID:         $Id$
    Author: 	Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1995  University of Cambridge

Permutations: example of an inductive definition
*)

(*It would be nice to prove
    xs <~~> ys = (!x. count xs x = count ys x)
See mset on HOL/ex/Sorting.thy
*)

open Perm;

goal Perm.thy "l <~~> l";
by (list.induct_tac "l" 1);
by (REPEAT (ares_tac perm.intrs 1));
qed "perm_refl";

val perm_induct = standard (perm.mutual_induct RS spec RS spec RSN (2,rev_mp));


(** Some examples of rule induction on permutations **)

(*The form of the premise lets the induction bind xs and ys.*)
goal Perm.thy "!!xs. xs <~~> ys ==> xs=[] --> ys=[]";
by (etac perm_induct 1);
by (ALLGOALS Asm_simp_tac);
qed "perm_Nil_lemma";

(*A more general version is actually easier to understand!*)
goal Perm.thy "!!xs. xs <~~> ys ==> length(xs) = length(ys)";
by (etac perm_induct 1);
by (ALLGOALS Asm_simp_tac);
qed "perm_length";

goal Perm.thy "!!xs. xs <~~> ys ==> ys <~~> xs";
by (etac perm_induct 1);
by (REPEAT (ares_tac perm.intrs 1));
qed "perm_sym";

goal Perm.thy "!!xs. [| xs <~~> ys |] ==> x mem xs --> x mem ys";
by (etac perm_induct 1);
by (fast_tac HOL_cs 4);
by (ALLGOALS (asm_simp_tac (!simpset setloop split_tac [expand_if])));
val perm_mem_lemma = result();

bind_thm ("perm_mem", perm_mem_lemma RS mp);

(** Ways of making new permutations **)

(*We can insert the head anywhere in the list*)
goal Perm.thy "a # xs @ ys <~~> xs @ a # ys";
by (list.induct_tac "xs" 1);
by (simp_tac (!simpset addsimps [perm_refl]) 1);
by (Simp_tac 1);
by (etac ([perm.swap, perm.Cons] MRS perm.trans) 1);
qed "perm_append_Cons";

(*single steps
by (rtac perm.trans 1);
by (rtac perm.swap 1);
by (rtac perm.Cons 1);
*)

goal Perm.thy "xs@ys <~~> ys@xs";
by (list.induct_tac "xs" 1);
by (simp_tac (!simpset addsimps [perm_refl]) 1);
by (Simp_tac 1);
by (etac ([perm.Cons, perm_append_Cons] MRS perm.trans) 1);
qed "perm_append_swap";


goal Perm.thy "a # xs <~~> xs @ [a]";
by (rtac perm.trans 1);
br perm_append_swap 2;
by (simp_tac (!simpset addsimps [perm_refl]) 1);
qed "perm_append_single";

goal Perm.thy "rev xs <~~> xs";
by (list.induct_tac "xs" 1);
by (simp_tac (!simpset addsimps [perm_refl]) 1);
by (Simp_tac 1);
by (rtac (perm_append_single RS perm_sym RS perm.trans) 1);
by (etac perm.Cons 1);
qed "perm_rev";

goal Perm.thy "!!xs. xs <~~> ys ==> l@xs <~~> l@ys";
by (list.induct_tac "l" 1);
by (Simp_tac 1);
by (asm_simp_tac (!simpset addsimps [perm.Cons]) 1);
qed "perm_append1";

goal Perm.thy "!!xs. xs <~~> ys ==> xs@l <~~> ys@l";
by (rtac (perm_append_swap RS perm.trans) 1);
by (etac (perm_append1 RS perm.trans) 1);
by (rtac perm_append_swap 1);
qed "perm_append2";

