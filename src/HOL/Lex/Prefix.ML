(*  Title:      HOL/Lex/Prefix.thy
    ID:         $Id$
    Author:     Richard Mayr & Tobias Nipkow
    Copyright   1995 TUM
*)

(* Junk: *)
val [maj,min] = goal Prefix.thy "[| Q([]); !! y ys. Q(y#ys) |] ==> ! l. Q(l)";
by (rtac allI 1);
by (list.induct_tac "l" 1);
by (rtac maj 1);
by (rtac min 1);
val list_cases = result();

(** <= is a partial order: **)

goalw thy [prefix_def] "xs <= (xs::'a list)";
by(Simp_tac 1);
qed "prefix_refl";
AddIffs[prefix_refl];

goalw thy [prefix_def] "!!xs::'a list. [| xs <= ys; ys <= zs |] ==> xs <= zs";
by(Clarify_tac 1);
by(Simp_tac 1);
qed "prefix_trans";

goalw thy [prefix_def] "!!xs::'a list. [| xs <= ys; ys <= xs |] ==> xs = ys";
by(Clarify_tac 1);
by(Asm_full_simp_tac 1);
qed "prefix_antisym";

(** recursion equations **)

goalw Prefix.thy [prefix_def] "[] <= xs";
by (simp_tac (simpset() addsimps [eq_sym_conv]) 1);
qed "Nil_prefix";
AddIffs[Nil_prefix];

goalw Prefix.thy [prefix_def] "(xs <= []) = (xs = [])";
by (list.induct_tac "xs" 1);
by (Simp_tac 1);
by (Simp_tac 1);
qed "prefix_Nil";
Addsimps [prefix_Nil];

goalw thy [prefix_def] "(xs <= ys@[y]) = (xs = ys@[y] | xs <= ys)";
br iffI 1;
 be exE 1;
 by(rename_tac "zs" 1);
 by(res_inst_tac [("xs","zs")] snoc_eq_cases 1);
  by(Asm_full_simp_tac 1);
 by(hyp_subst_tac 1);
 by(asm_full_simp_tac (simpset() delsimps [append_assoc]
                                 addsimps [append_assoc RS sym])1);
be disjE 1;
 by(Asm_simp_tac 1);
by(Clarify_tac 1);
by (Simp_tac 1);
qed "prefix_snoc";
Addsimps [prefix_snoc];

goalw Prefix.thy [prefix_def] "(x#xs <= y#ys) = (x=y & xs<=ys)";
by (Simp_tac 1);
by (Fast_tac 1);
qed"Cons_prefix_Cons";
Addsimps [Cons_prefix_Cons];

goal thy "(xs@ys <= xs@zs) = (ys <= zs)";
by (induct_tac "xs" 1);
by(ALLGOALS Asm_simp_tac);
qed "same_prefix_prefix";
Addsimps [same_prefix_prefix];

AddIffs
 [simplify (simpset()) (read_instantiate [("zs","[]")] same_prefix_prefix)];

goalw thy [prefix_def] "!!xs. xs <= ys ==> xs <= ys@zs";
by(Clarify_tac 1);
by (Simp_tac 1);
qed "prefix_prefix";
Addsimps [prefix_prefix];

(* nicht sehr elegant bewiesen - Induktion eigentlich ueberfluessig *)
goalw Prefix.thy [prefix_def]
   "(xs <= y#ys) = (xs=[] | (? zs. xs=y#zs & zs <= ys))";
by (list.induct_tac "xs" 1);
by (Simp_tac 1);
by (Simp_tac 1);
by (Fast_tac 1);
qed "prefix_Cons";

goal thy "(xs <= ys@zs) = (xs <= ys | (? us. xs = ys@us & us <= zs))";
by(res_inst_tac [("xs","zs")] snoc_induct 1);
 by(Simp_tac 1);
 by(Blast_tac 1);
by(asm_full_simp_tac (simpset() delsimps [append_assoc]
                                addsimps [append_assoc RS sym])1);
by(Simp_tac 1);
by(Blast_tac 1);
qed "prefix_append";
