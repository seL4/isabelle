(*  Title:      HOL/Lex/Prefix.thy
    ID:         $Id$
    Author:     Richard Mayr & Tobias Nipkow
    Copyright   1995 TUM
*)

open Prefix;

val [maj,min] = goal Prefix.thy "[| Q([]); !! y ys. Q(y#ys) |] ==> ! l. Q(l)";
by (rtac allI 1);
by (list.induct_tac "l" 1);
by (rtac maj 1);
by (rtac min 1);
val list_cases = result();

goalw Prefix.thy [prefix_def] "[] <= xs";
by (simp_tac (simpset() addsimps [eq_sym_conv]) 1);
qed "Nil_prefix";
Addsimps[Nil_prefix];

goalw Prefix.thy [prefix_def] "(xs <= []) = (xs = [])";
by (list.induct_tac "xs" 1);
by (Simp_tac 1);
by (Simp_tac 1);
qed "prefix_Nil";
Addsimps [prefix_Nil];

(* nicht sehr elegant bewiesen - Induktion eigentlich ueberfluessig *)
goalw Prefix.thy [prefix_def]
   "(xs <= y#ys) = (xs=[] | (? zs. xs=y#zs & zs <= ys))";
by (list.induct_tac "xs" 1);
by (Simp_tac 1);
by (Simp_tac 1);
by (Fast_tac 1);
qed "prefix_Cons";

goalw Prefix.thy [prefix_def] "(x#xs <= y#ys) = (x=y & xs<=ys)";
by(Simp_tac 1);
by (Fast_tac 1);
qed"Cons_prefix_Cons";
Addsimps [Cons_prefix_Cons];
