(*  Title:      HOL/MicroJava/BV/Convert.ML
    ID:         $Id$
    Author:     Cornelia Pusch
    Copyright   1999 Technische Universitaet Muenchen
*)

val widen_PrimT_conv1 =
 prove_typerel "(G \\<turnstile> PrimT x \\<preceq> T) = (T = PrimT x)"
 [ prove_widen_lemma "G\\<turnstile>S\\<preceq>T \\<Longrightarrow> S = PrimT x \\<longrightarrow> T = PrimT x"];
Addsimps [widen_PrimT_conv1];

Goalw [sup_ty_opt_def] "(G \\<turnstile> any >= None) = (any = None)";
by(simp_tac (simpset() addsplits [option.split]) 1);
qed "anyConvNone";
Addsimps [anyConvNone];

Goalw [sup_ty_opt_def] "(G \\<turnstile> Some ty >= Some ty') = (G \\<turnstile> ty' \\<preceq> ty)";
by(Simp_tac 1);
qed "SomeanyConvSome";
Addsimps [SomeanyConvSome];

Goal
"(G \\<turnstile> X >= Some(PrimT Integer)) = (X=None \\<or> (X=Some(PrimT Integer)))";
by (simp_tac (simpset() setloop (split_tac [ty.split,option.split]) addsimps [sup_ty_opt_def]) 1);
qed "sup_PTS_eq";



Goal
"CFS \\<turnstile> XT >>= [] = (XT=[])";
by (case_tac "XT=[]" 1);
by (asm_simp_tac (simpset() addsimps [sup_loc_def]) 1);
by (fast_tac (claset() addss (simpset() addsimps [sup_loc_def,neq_Nil_conv])) 1);
qed "sup_loc_Nil";

Goal
"CFS \\<turnstile> XT >>= (Y#YT) = (\\<exists>X XT'. XT=X#XT' \\<and> CFS \\<turnstile> X>=Y \\<and> CFS \\<turnstile> XT'>>=YT)";
by (case_tac "XT=[]" 1);
by (asm_simp_tac (simpset() addsimps [sup_loc_def]) 1);
by (fast_tac (claset() addss (simpset() addsimps [sup_loc_def,neq_Nil_conv])) 1);
qed "sup_loc_Cons";
