(*  Title:      HOL/Lex/Prefix.thy
    ID:         $Id$
    Author:     Richard Mayr & Tobias Nipkow
    Copyright   1995 TUM
*)

(** <= is a partial order: **)

Goalw [prefix_def] "xs <= (xs::'a list)";
by (Simp_tac 1);
qed "prefix_refl";
AddIffs[prefix_refl];

Goalw [prefix_def] "!!xs::'a list. [| xs <= ys; ys <= zs |] ==> xs <= zs";
by (Clarify_tac 1);
by (Simp_tac 1);
qed "prefix_trans";

Goalw [prefix_def] "!!xs::'a list. [| xs <= ys; ys <= xs |] ==> xs = ys";
by (Clarify_tac 1);
by (Asm_full_simp_tac 1);
qed "prefix_antisym";

Goalw [strict_prefix_def] "!!xs::'a list. (xs < zs) = (xs <= zs & xs ~= zs)";
by Auto_tac;
qed "prefix_less_le";


(** recursion equations **)

Goalw [prefix_def] "[] <= xs";
by (simp_tac (simpset() addsimps [eq_sym_conv]) 1);
qed "Nil_prefix";
AddIffs[Nil_prefix];

Goalw [prefix_def] "(xs <= []) = (xs = [])";
by (induct_tac "xs" 1);
by (Simp_tac 1);
by (Simp_tac 1);
qed "prefix_Nil";
Addsimps [prefix_Nil];

Goalw [prefix_def] "(xs <= ys@[y]) = (xs = ys@[y] | xs <= ys)";
by (rtac iffI 1);
 by (etac exE 1);
 by (rename_tac "zs" 1);
 by (res_inst_tac [("xs","zs")] rev_exhaust 1);
  by (Asm_full_simp_tac 1);
 by (hyp_subst_tac 1);
 by (asm_full_simp_tac (simpset() delsimps [append_assoc]
                                 addsimps [append_assoc RS sym])1);
by (Force_tac 1);
qed "prefix_snoc";
Addsimps [prefix_snoc];

Goalw [prefix_def] "(x#xs <= y#ys) = (x=y & xs<=ys)";
by (Simp_tac 1);
by (Fast_tac 1);
qed"Cons_prefix_Cons";
Addsimps [Cons_prefix_Cons];

Goal "(xs@ys <= xs@zs) = (ys <= zs)";
by (induct_tac "xs" 1);
by (ALLGOALS Asm_simp_tac);
qed "same_prefix_prefix";
Addsimps [same_prefix_prefix];

AddIffs   (* (xs@ys <= xs) = (ys <= []) *)
 [simplify (simpset()) (read_instantiate [("zs","[]")] same_prefix_prefix)];

Goalw [prefix_def] "xs <= ys ==> xs <= ys@zs";
by (Clarify_tac 1);
by (Simp_tac 1);
qed "prefix_prefix";
Addsimps [prefix_prefix];

Goalw [prefix_def]
   "(xs <= y#ys) = (xs=[] | (? zs. xs=y#zs & zs <= ys))";
by (case_tac "xs" 1);
by Auto_tac;
qed "prefix_Cons";

Goal "(xs <= ys@zs) = (xs <= ys | (? us. xs = ys@us & us <= zs))";
by (rev_induct_tac "zs" 1);
 by (Force_tac 1);
by (asm_full_simp_tac (simpset() delsimps [append_assoc]
                                 addsimps [append_assoc RS sym])1);
by (Simp_tac 1);
by (Blast_tac 1);
qed "prefix_append";

Goalw [prefix_def]
  "[| xs <= ys; length xs < length ys |] ==> xs @ [ys ! length xs] <= ys";
by (auto_tac(claset(), simpset() addsimps [nth_append]));
by (case_tac "ys" 1);
by Auto_tac;
qed "append_one_prefix";

Goalw [prefix_def] "xs <= ys ==> length xs <= length ys";
by Auto_tac;
qed "prefix_length_le";

Goal "mono length";
by (blast_tac (claset() addIs [monoI, prefix_length_le]) 1);
qed "mono_length";
