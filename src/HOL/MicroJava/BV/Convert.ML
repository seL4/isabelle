(*  Title:      HOL/MicroJava/BV/Convert.ML
    ID:         $Id$
    Author:     Cornelia Pusch
    Copyright   1999 Technische Universitaet Muenchen
*)


Goalw[sup_ty_opt_def] "G \\<turnstile> t <=o t";
by (exhaust_tac "t" 1);
by Auto_tac;
qed "sup_ty_opt_refl";
Addsimps [sup_ty_opt_refl];

Goalw[sup_loc_def] "G \\<turnstile> t <=l t";
by (induct_tac "t" 1);
by Auto_tac;
qed "sup_loc_refl";
Addsimps [sup_loc_refl];

Goalw[sup_state_def] "G \\<turnstile> s <=s s";
by Auto_tac;
qed "sup_state_refl";
Addsimps [sup_state_refl];

val widen_PrimT_conv1 =
 prove_typerel "(G \\<turnstile> PrimT x \\<preceq> T) = (T = PrimT x)"
 [ prove_widen_lemma "G\\<turnstile>S\\<preceq>T \\<Longrightarrow> S = PrimT x \\<longrightarrow> T = PrimT x"];
Addsimps [widen_PrimT_conv1];

Goalw [sup_ty_opt_def] "(G \\<turnstile> None <=o any) = (any = None)";
by(simp_tac (simpset() addsplits [option.split]) 1);
qed "anyConvNone";
Addsimps [anyConvNone];

Goalw [sup_ty_opt_def] "(G \\<turnstile> Some ty' <=o Some ty) = (G \\<turnstile> ty' \\<preceq> ty)";
by(Simp_tac 1);
qed "SomeanyConvSome";
Addsimps [SomeanyConvSome];

Goal
"(G \\<turnstile> Some(PrimT Integer) <=o X) = (X=None \\<or> (X=Some(PrimT Integer)))";
by (simp_tac (simpset() setloop (split_tac [ty.split,option.split]) addsimps [sup_ty_opt_def]) 1);
qed "sup_PTS_eq";



Goalw [sup_loc_def] "CFS \\<turnstile> [] <=l XT = (XT=[])";
by(Simp_tac 1);
qed "sup_loc_Nil";
AddIffs [sup_loc_Nil];


Goalw [sup_loc_def]
"CFS \\<turnstile> (Y#YT) <=l XT = (\\<exists>X XT'. XT=X#XT' \\<and> CFS \\<turnstile> Y <=o X \\<and> CFS \\<turnstile> YT <=l XT')";
by(simp_tac (simpset() addsimps [list_all2_Cons1]) 1);
qed "sup_loc_Cons";
AddIffs [sup_loc_Cons];

