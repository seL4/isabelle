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


Goal "\\<forall> b. G \\<turnstile> a <=l b \\<longrightarrow> length a = length b";
by (induct_tac "a" 1);
 by (Simp_tac 1);
by (Clarsimp_tac 1);
qed_spec_mp "sup_loc_length";

Goal "\\<forall> n b. (G \\<turnstile> a <=l b) \\<longrightarrow> n < length a \\<longrightarrow> (G \\<turnstile> (a!n) <=o (b!n))";
by (induct_tac "a" 1);
 by (Simp_tac 1);
by (Clarsimp_tac 1);
by (exhaust_tac "n" 1);
 by (Asm_full_simp_tac 1);
by (eres_inst_tac [("x","nat")] allE 1);
by (smp_tac 1 1);
by (Asm_full_simp_tac 1);
qed_spec_mp "sup_loc_nth";

Goalw[sup_state_def]
"(G \\<turnstile> (x, y) <=s (a, b)) \\<Longrightarrow> length x = length a";
by (Clarsimp_tac 1);
bd sup_loc_length 1;
by Auto_tac;
qed "sup_state_length_fst";

Goalw[sup_state_def] 
"(G \\<turnstile> (x, y) <=s (a, b)) \\<longrightarrow> length y = length b";
by (clarsimp_tac (claset(), simpset() addsimps [sup_loc_length]) 1);
qed "sup_state_length_snd";

Goal "\\<forall>b. length a = length b \\<longrightarrow> (G \\<turnstile> (a@x) <=l (b@y)) = ((G \\<turnstile> a <=l b) \\<and> (G \\<turnstile> x <=l y))";
by (induct_tac "a" 1);
 by (Clarsimp_tac 1);
by (Clarify_tac 1);
by (exhaust_tac "b" 1);
 by (Clarsimp_tac 1);  
by (Clarsimp_tac 1);
qed_spec_mp "sup_loc_append";


Goalw[sup_state_def] 
"length a = length b \\<Longrightarrow> (G \\<turnstile> (i,a@x) <=s (j,b@y)) = ((G \\<turnstile> (i,a) <=s (j,b)) \\<and> (G \\<turnstile> (i,x) <=s (j,y)))";
by (auto_tac (claset(), simpset() addsimps [sup_loc_append]));
qed "sup_state_append_snd";

Goalw[sup_state_def]
"length a = length b \\<Longrightarrow> (G \\<turnstile> (a@x,i) <=s (b@y,j)) = ((G \\<turnstile> (a,i) <=s (b,j)) \\<and> (G \\<turnstile> (x,i) <=s (y,j)))";
by (auto_tac (claset(), simpset() addsimps [sup_loc_append]));
qed "sup_state_append_fst";


Goal "\\<forall> b. (G \\<turnstile> (rev a) <=l rev b) = (G \\<turnstile> a <=l b)";
by (induct_tac "a" 1);
 by (Simp_tac 1);
by (Clarsimp_tac 1);
by Safe_tac;
 by (clarsimp_tac (claset(), simpset() addsimps [sup_loc_append, sup_loc_length]) 2);
by (exhaust_tac "b" 1); 
 bd sup_loc_length 1;
 by (Clarsimp_tac 1);
by (clarsimp_tac (claset(), simpset() addsimps [sup_loc_append, sup_loc_length]) 1);
by (subgoal_tac "length (rev list) = length (rev lista)" 1);
 bd sup_loc_length 2;
 by (Clarsimp_tac 2);
by (dres_inst_tac [("G","G"),("x","[a]"),("y","[aa]")] sup_loc_append 1);
by (Clarsimp_tac 1);
qed_spec_mp "sup_loc_rev";

Goalw[sup_state_def]
"(G \\<turnstile> (rev a,x) <=s (rev b,y)) = (G \\<turnstile> (a,x) <=s (b,y))";
by (auto_tac (claset(), simpset() addsimps [sup_loc_rev, rev_map RS sym]));
qed "sup_state_rev_fst";

Goal "map x a = Y # YT \\<longrightarrow> map x (tl a) = YT \\<and> x (hd a) = Y \\<and> (\\<exists> y yt. a = y#yt)";
by (exhaust_tac "a" 1);
by Auto_tac;
qed_spec_mp "map_hd_tl";

Goalw[sup_state_def]
"(G \\<turnstile> (x#xt, a) <=s (yt, b)) = (\\<exists>y yt'. yt=y#yt' \\<and> (G \\<turnstile> x \\<preceq> y) \\<and> (G \\<turnstile> (xt,a) <=s (yt',b)))";
by Auto_tac;
bd map_hd_tl 1;
by Auto_tac;
qed "sup_state_Cons1";

Goalw [sup_loc_def]
"CFS \\<turnstile> YT <=l (X#XT) = (\\<exists>Y YT'. YT=Y#YT' \\<and> CFS \\<turnstile> Y <=o X \\<and> CFS \\<turnstile> YT' <=l XT)";
by(simp_tac (simpset() addsimps [list_all2_Cons2]) 1);
qed "sup_loc_Cons2";

Goalw[sup_state_def]
"(G \\<turnstile> (xt, a) <=s (y#yt, b)) = (\\<exists>x xt'. xt=x#xt' \\<and> (G \\<turnstile> x \\<preceq> y) \\<and> (G \\<turnstile> (xt',a) <=s (yt,b)))";
by (auto_tac (claset(), simpset() addsimps [sup_loc_Cons2]));
bd map_hd_tl 1;
by Auto_tac;
qed "sup_state_Cons2"; 

Goalw[sup_state_def] 
"G \\<turnstile> (a, x) <=s (b, y) \\<Longrightarrow> G \\<turnstile> (c, x) <=s (c, y)";
by Auto_tac;
qed "sup_state_ignore_fst";

Goalw[sup_ty_opt_def] 
"\\<lbrakk>G \\<turnstile> a <=o b; G \\<turnstile> b <=o c\\<rbrakk> \\<Longrightarrow> G \\<turnstile> a <=o c";
by (exhaust_tac "c" 1);
 by (Clarsimp_tac 1);
by (Clarsimp_tac 1);
by (exhaust_tac "a" 1);
 by (Clarsimp_tac 1);
 by (exhaust_tac "b" 1);
  by (Clarsimp_tac 1);
 by (Clarsimp_tac 1);
by (exhaust_tac "b" 1);
 by (Clarsimp_tac 1);
by (Clarsimp_tac 1);
be widen_trans 1;
ba 1;
qed "sup_ty_opt_trans";

Goal "\\<lbrakk>G \\<turnstile> a <=l b; G \\<turnstile> b <=l c\\<rbrakk> \\<Longrightarrow> \\<forall> n. n < length a \\<longrightarrow> G \\<turnstile> a!n <=o c!n";
by (Clarify_tac 1);
by (forward_tac [sup_loc_length] 1);
bd sup_loc_nth 1;
 ba 1;
bd sup_loc_nth 1;
 by (Force_tac 1);
bd sup_ty_opt_trans 1;
 ba 1;
ba 1;
qed "sup_loc_all_trans";

Goal "\\<forall> b. length a = length b \\<longrightarrow> (\\<forall> n. n < length a \\<longrightarrow> (G \\<turnstile> (a!n) <=o (b!n))) \\<longrightarrow> (G \\<turnstile> a <=l b)";
by (induct_tac "a" 1);
 by (Clarsimp_tac 1);
by (Clarsimp_tac 1);
by (exhaust_tac "b=[]" 1);
 by (Clarsimp_tac 1);
by (Clarsimp_tac 1);
by (asm_full_simp_tac (simpset() addsimps [neq_Nil_conv]) 1);
by (Clarify_tac 1);
by (res_inst_tac [("x","y")] exI 1);
by (res_inst_tac [("x","ys")] exI 1);
by (eres_inst_tac [("x","ys")] allE 1);
by (Full_simp_tac 1);
by (Clarify_tac 1);
be impE 1;
 by (Clarsimp_tac 1);
 by (eres_inst_tac [("x","Suc n")] allE 1);
 by (Clarsimp_tac 1);
by (eres_inst_tac [("x","0")] allE 1);
by (Clarsimp_tac 1);
qed_spec_mp "all_nth_sup_loc";

Goal "\\<lbrakk>G \\<turnstile> a <=l b; G \\<turnstile> b <=l c\\<rbrakk> \\<Longrightarrow> G \\<turnstile> a <=l c";
by (forward_tac [sup_loc_all_trans] 1);
 ba 1;
bd sup_loc_length 1;
bd sup_loc_length 1;
br all_nth_sup_loc 1;
 by (Clarsimp_tac 1);
ba 1;
qed "sup_loc_trans";

Goalw[sup_state_def] 
"\\<lbrakk>G \\<turnstile> a <=s b; G \\<turnstile> b <=s c\\<rbrakk> \\<Longrightarrow> G \\<turnstile> a <=s c";
by Safe_tac;
 br sup_loc_trans 1;
  ba 1;
 ba 1;
br sup_loc_trans 1;
 ba 1;
ba 1;
qed "sup_state_trans";

Goalw[sup_ty_opt_def] "G \\<turnstile> a <=o Some b \\<Longrightarrow> \\<exists> x. a = Some x";
by (exhaust_tac "a" 1);
 by Auto_tac;
qed "sup_ty_opt_some";


Goalw[sup_loc_def]
"\\<forall> n y. (G \\<turnstile> a <=o b) \\<longrightarrow> n < length y \\<longrightarrow> (G \\<turnstile> x <=l y) \\<longrightarrow> (G \\<turnstile> x[n := a] <=l y[n := b])";
by (induct_tac "x" 1);
 by (Simp_tac 1);
by (clarsimp_tac ((claset(), simpset()) addIffs [sup_loc_Cons2]) 1);
by (exhaust_tac "n" 1);
 by (clarsimp_tac (claset(), simpset() addsimps [list_all2_Cons1]) 1);
by (clarsimp_tac (claset(), simpset() addsimps [list_all2_Cons1]) 1);
qed_spec_mp "sup_loc_update";
