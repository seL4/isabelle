(*  Title:      HOL/MicroJava/BV/Correct.ML
    ID:         $Id$
    Author:     Cornelia Pusch
    Copyright   1999 Technische Universitaet Muenchen
*)

(** sup_heap **)

Goalw [hext_def]
 "hp x = None \\<longrightarrow> hp \\<le>| (hp((newref hp) \\<mapsto> obj))";
by (asm_full_simp_tac (simpset() addsimps []) 1);
by (Clarify_tac 1);
bd newref_None 1;
back();
by (asm_full_simp_tac (simpset() addsimps []) 1);
qed_spec_mp "sup_heap_newref";


Goalw [hext_def]
"hp a = Some (C,od') \\<longrightarrow> hp \\<le>| (hp(a \\<mapsto> (C,od)))";
by (asm_full_simp_tac (simpset() addsimps []) 1);
qed_spec_mp "sup_heap_update_value";


(** approx_val **)

Goalw [approx_val_def]
"approx_val G hp x None";
by (Asm_full_simp_tac 1);
qed_spec_mp "approx_val_None";


Goalw [approx_val_def]
"approx_val G hp Null (Some(RefT x))";
by(Simp_tac 1);
by (fast_tac (claset() addIs widen.intrs) 1);
qed_spec_mp "approx_val_Null";


Goal
"\\<lbrakk> wf_prog wt G \\<rbrakk> \
\\\<Longrightarrow> approx_val G hp v (Some T) \\<longrightarrow> G\\<turnstile> T\\<preceq>T' \\<longrightarrow> approx_val G hp v (Some T')";
by (cases_tac "T" 1);
 by (Asm_simp_tac 1);
by (fast_tac (claset() addIs [conf_widen] addss (simpset()addsimps[approx_val_def])) 1);
qed_spec_mp "approx_val_imp_approx_val_assConvertible";


Goal
"approx_val G hp val at \\<longrightarrow> hp \\<le>| hp' \\<longrightarrow> approx_val G hp' val at";
by (asm_full_simp_tac (simpset() setloop (split_tac [option.split]) 
	addsimps [approx_val_def]) 1);
by(blast_tac (claset() addIs [conf_hext]) 1);
qed_spec_mp "approx_val_imp_approx_val_sup_heap";

Goal
"\\<lbrakk> hp a = Some obj' ; G,hp\\<turnstile> v\\<Colon>\\<preceq>T ; obj_ty obj = obj_ty obj' \\<rbrakk> \
\\\<Longrightarrow>G,(hp(a\\<mapsto>obj))\\<turnstile> v\\<Colon>\\<preceq>T";
by (cases_tac "v" 1);
by (auto_tac (claset() , simpset() addsimps [obj_ty_def,conf_def] addsplits [option.split]));
qed_spec_mp "approx_val_imp_approx_val_heap_update";


Goal
"wf_prog wt G \\<Longrightarrow> approx_val G h val us \\<longrightarrow> G \\<turnstile> us <=o us' \\<longrightarrow> approx_val G h val us'";
by (asm_simp_tac (simpset() addsimps [sup_PTS_eq,approx_val_def] addsplits [option.split,val_.split,ty.split]) 1);
by(blast_tac (claset() addIs [conf_widen]) 1);
qed_spec_mp "approx_val_imp_approx_val_sup";


Goalw [approx_loc_def,list_all2_def]
"\\<lbrakk> wf_prog wt G; approx_loc G hp loc LT; idx < length LT ; val = loc ! idx ; G \\<turnstile> LT ! idx <=o at\\<rbrakk> \
\\\<Longrightarrow> approx_val G hp val at";
by (fast_tac (claset() addIs [approx_val_imp_approx_val_sup] addss (simpset() addsimps 
	[split_def,all_set_conv_all_nth])) 1);
qed "approx_loc_imp_approx_val_sup";


(** approx_loc **)

Goalw [approx_loc_def]
"approx_loc G hp (s#xs) (l#ls) = \
\   (approx_val G hp s l \\<and> approx_loc G hp xs ls)";
by (Simp_tac 1);
qed "approx_loc_Cons";
AddIffs [approx_loc_Cons];


Goalw [approx_stk_def,approx_loc_def,list_all2_def]
"\\<lbrakk> wf_prog wt G \\<rbrakk> \
\\\<Longrightarrow> (\\<forall>tt'\\<in>set (zip tys_n ts). tt' \\<in> widen G) \\<longrightarrow> \
\     length tys_n = length ts \\<longrightarrow> approx_stk G hp s tys_n \\<longrightarrow> approx_loc G hp s (map Some ts)";
by (force_tac (claset() addIs [approx_val_imp_approx_val_assConvertible], simpset() 
	addsimps [all_set_conv_all_nth,split_def]) 1);
qed_spec_mp "assConv_approx_stk_imp_approx_loc";


Goalw [approx_loc_def,list_all2_def]
"\\<forall> lvars. approx_loc G hp lvars lt \\<longrightarrow>  hp \\<le>| hp' \\<longrightarrow> approx_loc G hp' lvars lt";
by (cases_tac "lt" 1);
 by (Asm_simp_tac 1);
by (force_tac (claset() addIs [approx_val_imp_approx_val_sup_heap],
	       simpset() addsimps [neq_Nil_conv]) 1);
qed_spec_mp "approx_loc_imp_approx_loc_sup_heap";


Goalw [sup_loc_def,approx_loc_def,list_all2_def]
"wf_prog wt G \\<Longrightarrow> approx_loc G hp lvars lt \\<longrightarrow> G \\<turnstile> lt <=l lt' \\<longrightarrow> approx_loc G hp lvars lt'";
by (auto_tac (claset() , simpset() addsimps [all_set_conv_all_nth,split_def]));
by (auto_tac (claset() addEs [approx_val_imp_approx_val_sup] , simpset()));
qed_spec_mp "approx_loc_imp_approx_loc_sup";


Goalw [approx_loc_def,list_all2_def]
"\\<forall>loc idx x X. (approx_loc G hp loc LT) \\<longrightarrow> (approx_val G hp x X) \
\ \\<longrightarrow> (approx_loc G hp (loc[idx:=x]) (LT[idx:=X]))";
by (fast_tac (claset() addDs [set_update_subset_insert RS subsetD]
              addss (simpset() addsimps [zip_update])) 1);
qed_spec_mp "approx_loc_imp_approx_loc_subst";


Goalw [approx_loc_def,list_all2_def]
"\\<forall>L1 l2 L2. length l1=length L1 \
\ \\<longrightarrow> approx_loc G hp (l1@l2) (L1@L2) = (approx_loc G hp l1 L1 \\<and> approx_loc G hp l2 L2)";
by(simp_tac (simpset() addcongs [conj_cong] addsimps [zip_append]) 1);
by(Blast_tac 1);
qed_spec_mp "approx_loc_append";


(** approx_stk **)

Goalw [approx_stk_def,approx_loc_def,list_all2_def]
"approx_stk G hp (rev s) (rev t) = approx_stk G hp s t";
by (fast_tac (claset() addss (simpset() addsimps [zip_rev,rev_map RS sym])) 1);
qed_spec_mp "approx_stk_rev_lem";

Goal 
"approx_stk G hp (rev s) t = approx_stk G hp s (rev t)";
by (fast_tac (claset() addIs [approx_stk_rev_lem RS subst] addss (simpset()))  1);
qed_spec_mp "approx_stk_rev";

Goalw [approx_stk_def]
"\\<forall> lvars. approx_stk G hp lvars lt \\<longrightarrow> hp \\<le>| hp' \\<longrightarrow> approx_stk G hp' lvars lt";
by (fast_tac (claset() addIs [approx_loc_imp_approx_loc_sup_heap])  1);
qed_spec_mp "approx_stk_imp_approx_stk_sup_heap";


Goalw [approx_stk_def]
"wf_prog wt G \\<Longrightarrow> approx_stk G hp lvars st \\<longrightarrow> G \\<turnstile> (map Some st) <=l (map Some st') \\<longrightarrow> approx_stk G hp lvars st'";
by (fast_tac (claset() addIs [approx_loc_imp_approx_loc_sup])  1);
qed_spec_mp "approx_stk_imp_approx_stk_sup";

Goalw [approx_stk_def,approx_loc_def]
"approx_stk G hp [] []";
by (Simp_tac 1);
qed "approx_stk_Nil";
AddIffs [approx_stk_Nil];

Goalw [approx_stk_def,approx_loc_def]
"approx_stk G hp (x # stk) (S#ST) = (approx_val G hp x (Some S) \\<and> approx_stk G hp stk ST)";
by (Simp_tac 1);
qed "approx_stk_Cons";
AddIffs [approx_stk_Cons];

Goalw [approx_stk_def,approx_loc_def]
"approx_stk G hp stk (S#ST') = \
\ (\\<exists>s stk'. stk = s#stk' \\<and> approx_val G hp s (Some S) \\<and> approx_stk G hp stk' ST')";
by (asm_full_simp_tac (simpset() addsimps [list_all2_Cons2]) 1);
qed "approx_stk_Cons_lemma";
AddIffs [approx_stk_Cons_lemma];


Goalw [approx_stk_def,approx_loc_def]
"approx_stk G hp stk (S@ST')  \
\ \\<Longrightarrow> (\\<exists>s stk'. stk = s@stk' \\<and> length s = length S \\<and> length stk' = length ST' \\<and> \
\             approx_stk G hp s S \\<and> approx_stk G hp stk' ST')";
by(asm_full_simp_tac (simpset() addsimps [list_all2_append2]) 1);
qed_spec_mp "approx_stk_append_lemma";


(** oconf **)

Goalw [oconf_def,lconf_def]
"\\<lbrakk> is_class G C; wf_prog wt G \\<rbrakk> \\<Longrightarrow> \
\G,h\\<turnstile> (C, map_of (map (\\<lambda>(f,fT).(f,default_val fT)) (fields(G,C))))\\<surd>";
by (asm_full_simp_tac (simpset() addsimps [map_of_map]) 1);
by (force_tac (claset() addIs [defval_conf]
                        addDs [map_of_SomeD,is_type_fields],simpset()) 1);
qed "correct_init_obj";


Goalw [oconf_def,lconf_def]
"\\<lbrakk> map_of (fields (G, oT)) FD = Some T ; G,hp\\<turnstile>v\\<Colon>\\<preceq>T ; \
\   G,hp\\<turnstile>(oT,fs)\\<surd> \\<rbrakk>  \
\\\<Longrightarrow> G,hp\\<turnstile>(oT, fs(FD\\<mapsto>v))\\<surd>";
by (asm_full_simp_tac (simpset() addsplits [ty.split]) 1);
qed_spec_mp "oconf_imp_oconf_field_update";


Goalw [oconf_def,lconf_def]
"hp x = None \\<longrightarrow> G,hp\\<turnstile>obj\\<surd>  \\<longrightarrow>  G,hp\\<turnstile>obj'\\<surd> \
\  \\<longrightarrow> G,(hp(newref hp\\<mapsto>obj'))\\<turnstile>obj\\<surd>";
by (Asm_full_simp_tac 1);
by (fast_tac (claset() addIs [conf_hext,sup_heap_newref]) 1);
qed_spec_mp "oconf_imp_oconf_heap_newref";

Goalw [oconf_def,lconf_def]
"hp a = Some obj'  \\<longrightarrow> obj_ty obj' = obj_ty obj'' \\<longrightarrow> G,hp\\<turnstile>obj\\<surd> \
\  \\<longrightarrow> G,hp(a\\<mapsto>obj'')\\<turnstile>obj\\<surd>";
by (Asm_full_simp_tac 1);
by (fast_tac (claset() addIs [approx_val_imp_approx_val_heap_update] addss (simpset())) 1);
qed_spec_mp "oconf_imp_oconf_heap_update";


(** hconf **)


Goal "hp x = None \\<longrightarrow> G\\<turnstile>h hp\\<surd> \\<longrightarrow> G,hp\\<turnstile>obj\\<surd> \\<longrightarrow> G\\<turnstile>h hp(newref hp\\<mapsto>obj)\\<surd>";
by (asm_full_simp_tac (simpset() addsplits [split_split] 
				 addsimps [hconf_def]) 1);
 by (fast_tac (claset()addIs[oconf_imp_oconf_heap_newref] addss (simpset())) 1);
qed_spec_mp "hconf_imp_hconf_newref";


Goal "map_of (fields (G, oT)) (F, D) = Some T \\<and> hp oloc = Some(oT,fs) \\<and> \
\ G,hp\\<turnstile>v\\<Colon>\\<preceq>T \\<and> G\\<turnstile>h hp\\<surd> \\<longrightarrow> G\\<turnstile>h hp(oloc \\<mapsto> (oT, fs((F,D)\\<mapsto>v)))\\<surd>";
by (asm_full_simp_tac (simpset() addsimps [hconf_def]) 1);
by (fast_tac (claset() addIs 
        [oconf_imp_oconf_heap_update, oconf_imp_oconf_field_update]
        addss (simpset() addsimps [obj_ty_def])) 1);
qed_spec_mp "hconf_imp_hconf_field_update";


(** correct_frames **)

Delsimps [fun_upd_apply]; 
Goal
"\\<forall>rT C sig. correct_frames G hp phi rT sig frs \\<longrightarrow> \
\    hp a = Some (C,od) \\<longrightarrow> map_of (fields (G, C)) fl = Some fd \\<longrightarrow> \
\    G,hp\\<turnstile>v\\<Colon>\\<preceq>fd \
\ \\<longrightarrow> correct_frames G (hp(a \\<mapsto> (C, od(fl\\<mapsto>v)))) phi rT sig frs";
by (induct_tac "frs" 1);
 by (Asm_full_simp_tac 1);
by (asm_full_simp_tac (simpset() addsimps [split_def,correct_frame_def]) 1);
by (fast_tac (claset() addIs [approx_stk_imp_approx_stk_sup_heap,
				approx_loc_imp_approx_loc_sup_heap,
				sup_heap_update_value] addss (simpset())) 1);
qed_spec_mp "correct_frames_imp_correct_frames_field_update";


Goal
"\\<forall>rT C sig. hp x = None \\<longrightarrow> correct_frames G hp phi rT sig frs \\<and> \
\    oconf G hp obj \
\ \\<longrightarrow> correct_frames G (hp(newref hp \\<mapsto> obj)) phi rT sig frs";
by (induct_tac "frs" 1);
by  (asm_full_simp_tac (simpset() addsimps []) 1);
by (asm_full_simp_tac (simpset() addsimps [split_def,correct_frame_def]) 1);
by (fast_tac (claset() addIs [approx_stk_imp_approx_stk_sup_heap,
				approx_loc_imp_approx_loc_sup_heap,
				hconf_imp_hconf_newref,
				sup_heap_newref] addss (simpset())) 1);
qed_spec_mp "correct_frames_imp_correct_frames_newref";

