(*  Title:      HOL/MicroJava/BV/BVSpecTypeSafe.ML
    ID:         $Id$
    Author:     Cornelia Pusch
    Copyright   1999 Technische Universitaet Muenchen
*)

val defs1 = exec.simps@[split_def,thm "sup_state_def",correct_state_def,
		correct_frame_def, thm "wt_instr_def"];

Goalw [correct_state_def,Let_def,correct_frame_def,split_def]
"\\<lbrakk> wt_jvm_prog G phi; \
\   method (G,C) sig = Some (C,rT,maxl,ins); \
\   G,phi \\<turnstile>JVM (None, hp, (stk,loc,C,sig,pc)#frs)\\<surd> \\<rbrakk> \
\\\<Longrightarrow> wt_instr (ins!pc) G rT (phi C sig) (length ins) pc";
by (Asm_full_simp_tac 1);
by(blast_tac (claset() addIs [thm "wt_jvm_prog_impl_wt_instr"]) 1);
qed "wt_jvm_prog_impl_wt_instr_cor";


Delsimps [split_paired_All]; 


(******* LS *******)


Goal
"\\<lbrakk> wf_prog wt G; \
\  method (G,C) sig = Some (C,rT,maxl,ins); \
\  ins!pc = Load idx; \
\  wt_instr (ins!pc) G rT (phi C sig) (length ins) pc; \
\  Some state' = exec (G, None, hp, (stk,loc,C,sig,pc)#frs); \
\  G,phi \\<turnstile>JVM (None, hp, (stk,loc,C,sig,pc)#frs)\\<surd> \\<rbrakk> \
\\\<Longrightarrow> G,phi \\<turnstile>JVM state'\\<surd>";
by (case_tac "phi C sig!pc" 1);
by (fast_tac (claset() addIs [approx_stk_imp_approx_stk_sup,approx_loc_imp_approx_val_sup,
	approx_loc_imp_approx_loc_sup] 
	addss (simpset() addsimps [map_eq_Cons]@defs1)) 1);
qed "Load_correct";


Goal 
"\\<lbrakk> wf_prog wt G; \
\  method (G,C) sig = Some (C,rT,maxl,ins); \
\  ins!pc = Store idx; \
\  wt_instr (ins!pc) G rT (phi C sig) (length ins) pc; \
\  Some state' = exec (G, None, hp, (stk,loc,C,sig,pc)#frs) ; \
\  G,phi \\<turnstile>JVM (None, hp, (stk,loc,C,sig,pc)#frs)\\<surd> \\<rbrakk> \
\\\<Longrightarrow> G,phi \\<turnstile>JVM state'\\<surd>";
by (fast_tac (claset() addIs [approx_stk_imp_approx_stk_sup,approx_loc_imp_approx_loc_subst RSN(2, approx_loc_imp_approx_loc_sup)]
	addss (simpset() addsimps [map_eq_Cons]@defs1)) 1);
qed "Store_correct";


Goalw [conf_def] "G,h \\<turnstile> Intg i \\<Colon>\\<preceq> PrimT Integer";
by(Simp_tac 1);
qed "conf_Intg_Integer";
AddIffs [conf_Intg_Integer];

Goal
"\\<lbrakk> wf_prog wt G; \
\  method (G,C) sig = Some (C,rT,maxl,ins); \
\  ins!pc = Bipush i; \
\  wt_instr (ins!pc) G rT (phi C sig) (length ins) pc; \
\  Some state' = exec (G, None, hp, (stk,loc,C,sig,pc)#frs) ; \
\  G,phi \\<turnstile>JVM (None, hp, (stk,loc,C,sig,pc)#frs)\\<surd> \\<rbrakk> \
\\\<Longrightarrow> G,phi \\<turnstile>JVM state'\\<surd>";
by (case_tac "phi C sig ! pc" 1);
by (fast_tac (claset()addIs [approx_stk_imp_approx_stk_sup,approx_loc_imp_approx_loc_sup]
	addss (simpset() addsimps [approx_val_def,thm "sup_PTS_eq",map_eq_Cons]@defs1)) 1);
qed "Bipush_correct";

Goal "G \\<turnstile> T' \\<preceq> T \\<Longrightarrow> T' = NT \\<longrightarrow> (T=NT | (\\<exists>C. T = Class C))";
be widen.induct 1;
by(Auto_tac);
by(rename_tac "R" 1);
by(case_tac "R" 1);
by(Auto_tac);
val lemma = result();

Goal "G \\<turnstile> NT \\<preceq> T = (T=NT | (\\<exists>C. T = Class C))";
by(force_tac (claset() addIs widen.intrs addDs [lemma],simpset()) 1);
qed "NT_subtype_conv";

Goal 
"\\<lbrakk> wf_prog wt G; \
\  method (G,C) sig = Some (C,rT,maxl,ins); \
\  ins!pc =  Aconst_null; \
\  wt_instr (ins!pc) G rT (phi C sig) (length ins) pc; \
\  Some state' = exec (G, None, hp, (stk,loc,C,sig,pc)#frs) ; \
\  G,phi \\<turnstile>JVM (None, hp, (stk,loc,C,sig,pc)#frs)\\<surd> \\<rbrakk> \
\\\<Longrightarrow> G,phi \\<turnstile>JVM state'\\<surd>";
by (case_tac "phi C sig ! pc" 1);
by (fast_tac (claset() addIs [approx_stk_imp_approx_stk_sup,approx_loc_imp_approx_loc_sup]
	addss (simpset() addsimps [approx_val_Null,NT_subtype_conv,map_eq_Cons]@defs1)) 1);
qed "Aconst_null_correct";


Goalw [cast_ok_def]
 "\\<lbrakk> wf_prog ok G; G,h\\<turnstile>v\\<Colon>\\<preceq>RefT rt; cast_ok G C h v ; G\\<turnstile>Class C\\<preceq>T; is_class G C \\<rbrakk> \
\ \\<Longrightarrow> G,h\\<turnstile>v\\<Colon>\\<preceq>T";
by (forward_tac [widen_Class] 1);
by (Clarify_tac 1);
be disjE 1;
 by (asm_full_simp_tac (simpset() addsimps [widen.null]) 1);
by (asm_full_simp_tac (simpset() addsimps [conf_def]) 1);
by (Clarify_tac 1);
by (asm_full_simp_tac (simpset() addsimps [obj_ty_def]) 1);
by (case_tac "v" 1);
by (ALLGOALS (fast_tac  (claset() addIs [rtrancl_trans] addss (simpset() addsimps [widen.null]))));
qed "Cast_conf2";

Goal
"\\<lbrakk> wf_prog wt G; \
\  method (G,C) sig = Some (C,rT,maxl,ins); \
\  ins!pc = Checkcast D; \
\  wt_instr (ins!pc) G rT (phi C sig) (length ins) pc; \
\  Some state' = exec (G, None, hp, (stk,loc,C,sig,pc)#frs) ; \
\  G,phi \\<turnstile>JVM (None, hp, (stk,loc,C,sig,pc)#frs)\\<surd> \\<rbrakk> \
\\\<Longrightarrow> G,phi \\<turnstile>JVM state'\\<surd>";
by (asm_full_simp_tac (simpset() addsimps [map_eq_Cons,
		raise_xcpt_def]@defs1 addsplits [option.split]) 1);
by (fast_tac (claset() addIs [approx_stk_imp_approx_stk_sup,approx_loc_imp_approx_loc_sup,Cast_conf2] 
	addss (simpset() addsimps [map_eq_Cons,approx_val_def])) 1);
qed "Checkcast_correct";

Goal
"\\<lbrakk> wf_prog wt G; \
\  method (G,C) sig = Some (C,rT,maxl,ins); \
\  ins!pc = Getfield F D; \
\  wt_instr (ins!pc) G rT (phi C sig) (length ins) pc; \
\  Some state' = exec (G, None, hp, (stk,loc,C,sig,pc)#frs) ; \
\  G,phi \\<turnstile>JVM (None, hp, (stk,loc,C,sig,pc)#frs)\\<surd> \\<rbrakk> \
\\\<Longrightarrow> G,phi \\<turnstile>JVM state'\\<surd>";
by (asm_full_simp_tac (simpset() addsimps [raise_xcpt_def]@defs1 addsplits [option.split]) 1);
by (Clarify_tac 1);
by (asm_full_simp_tac (simpset() addsimps [thm "sup_state_def",map_eq_Cons]) 1);
by (Clarify_tac 1);
by (asm_full_simp_tac (simpset() addsimps [approx_val_def]) 1);

by (forward_tac [conf_widen] 1);
  ba 1;
 ba 1;
bd conf_RefTD 1;
by (Clarify_tac 1);
by (asm_full_simp_tac (simpset() addsimps []) 1); 

br conjI 1;
 bd widen_cfs_fields 1;
   ba 1;
  ba 1;
 by (fast_tac (claset() addIs [conf_widen] addss (simpset() addsimps [hconf_def,oconf_def,lconf_def])) 1);
by (fast_tac (claset() addIs [approx_stk_imp_approx_stk_sup,approx_loc_imp_approx_loc_sup]) 1);
qed "Getfield_correct";



Goal
"\\<lbrakk> wf_prog wt G; \
\  method (G,C) sig = Some (C,rT,maxl,ins); \
\  ins!pc = Putfield F D; \
\  wt_instr (ins!pc) G rT (phi C sig) (length ins) pc; \
\  Some state' = exec (G, None, hp, (stk,loc,C,sig,pc)#frs) ; \
\  G,phi \\<turnstile>JVM (None, hp, (stk,loc,C,sig,pc)#frs)\\<surd> \\<rbrakk> \
\\\<Longrightarrow> G,phi \\<turnstile>JVM state'\\<surd>";
by (asm_full_simp_tac (simpset() addsimps [raise_xcpt_def]@defs1 addsplits [option.split]) 1);
by (Clarify_tac 1);
by (asm_full_simp_tac (simpset() addsimps [thm "sup_state_def",map_eq_Cons]) 1);
by (Clarify_tac 1);
by (asm_full_simp_tac (simpset() addsimps [approx_val_def]) 1);

by (forward_tac [conf_widen] 1);
  ba 2;
 ba 1;
by (fast_tac (claset() addDs [conf_RefTD,widen_cfs_fields] 
	addIs [sup_heap_update_value,approx_stk_imp_approx_stk_sup_heap RSN(2,approx_stk_imp_approx_stk_sup),
		approx_loc_imp_approx_loc_sup_heap RSN(2,approx_loc_imp_approx_loc_sup),
		hconf_imp_hconf_field_update,
		correct_frames_imp_correct_frames_field_update,conf_widen] addss (simpset())) 1);
qed "Putfield_correct";

Goal "(\\<forall>x y. P(x,y)) = (\\<forall>z. P z)";
by(Fast_tac 1);
qed "collapse_paired_All";

Goal
"\\<lbrakk> wf_prog wt G; \
\  method (G,C) sig = Some (C,rT,maxl,ins); \
\  ins!pc = New cl_idx; \
\  wt_instr (ins!pc) G rT (phi C sig) (length ins) pc; \
\  Some state' = exec (G, None, hp, (stk,loc,C,sig,pc)#frs) ; \
\  G,phi \\<turnstile>JVM (None, hp, (stk,loc,C,sig,pc)#frs)\\<surd> \\<rbrakk> \
\\\<Longrightarrow> G,phi \\<turnstile>JVM state'\\<surd>";
by (case_tac "phi C sig ! pc" 1);
by (fast_tac (claset() addSDs [collapse_paired_All RS iffD1]addIs [sup_heap_newref,
		approx_stk_imp_approx_stk_sup_heap RSN(2,approx_stk_imp_approx_stk_sup),
		approx_loc_imp_approx_loc_sup_heap RSN(2,approx_loc_imp_approx_loc_sup),
		hconf_imp_hconf_newref,correct_frames_imp_correct_frames_newref,
		rewrite_rule [split_def] correct_init_obj]
	addss (simpset() addsimps [NT_subtype_conv,approx_val_def,conf_def,
		fun_upd_apply,map_eq_Cons,is_class_def,raise_xcpt_def,init_vars_def]@defs1 
	addsplits [option.split])) 1);
qed "New_correct";



Delsimps (thms "app.simps");

(****** Method Invocation ******)

Goal
"\\<lbrakk> wt_jvm_prog G phi; \
\  method (G,C) sig = Some (C,rT,maxl,ins); \
\  ins ! pc = Invoke C' mn pTs; \
\  wt_instr (ins!pc) G rT (phi C sig) (length ins) pc; \
\  Some state' = exec (G, None, hp, (stk,loc,C,sig,pc)#frs) ; \
\  G,phi \\<turnstile>JVM (None, hp, (stk,loc,C,sig,pc)#frs)\\<surd> \\<rbrakk> \
\\\<Longrightarrow> G,phi \\<turnstile>JVM state'\\<surd>";
by(case_tac "phi C sig ! pc" 1);
by(forward_tac [thm "wt_jvm_progD"] 1);
by(etac exE 1);
by(asm_full_simp_tac (simpset() addsimps defs1) 1);
by(Clarify_tac 1);
by(asm_full_simp_tac (simpset() addsimps [raise_xcpt_def] addsplits [option.split]) 1);
by(Clarify_tac 1);
bd approx_stk_append_lemma 1;
by(clarsimp_tac (claset(), simpset() addsimps [approx_val_def]) 1);

by (subgoal_tac "\\<exists> D'. X = Class D'" 1);
 bd widen_RefT2 2;
 by (Clarsimp_tac 2);
 bd conf_RefTD 2;
 by (Clarsimp_tac 2);
 bd widen_Class 2;
 by (Clarsimp_tac 2);

by (Clarsimp_tac 1);
bd conf_RefTD 1;
by (Clarify_tac 1);
by(rename_tac "oloc oT ofs T'" 1);
by (asm_full_simp_tac (simpset() addsimps defs1) 1);
by (subgoal_tac "G\\<turnstile>oT\\<preceq>C C'" 1);
 bd widen.subcls 2;
 bd widen.subcls 2;
 by (((dtac widen_trans) THEN' atac THEN' Blast_tac) 2);
bd subtype_widen_methd 1;
  ba 1;
 ba 1;
by (Clarify_tac 1);
bd subtype_widen_methd 1;
  ba 1;
 ba 1;
be exE 1;
by(rename_tac "oT'" 1);
by (Clarify_tac 1);
by(subgoal_tac "G \\<turnstile> oT \\<preceq>C oT'" 1);
 by(forw_inst_tac [("C","oT")] method_wf_mdecl 2); 
  ba 2;
 by (Blast_tac 2);
by (asm_full_simp_tac (simpset() addsimps defs1) 1);
by(forward_tac [method_in_md] 1);
 ba 1;
 back();
 back();
 back();
by (Clarify_tac 1);
by (asm_full_simp_tac (simpset() addsimps defs1) 1);
by (forward_tac [thm "wt_jvm_prog_impl_wt_start"] 1);
 ba 1;
 back();
by (asm_full_simp_tac (simpset() addsimps [thm "wt_start_def",thm "sup_state_def"]) 1);
by (Clarify_tac 1);

(** approx_loc **)
br conjI 1;
 br approx_loc_imp_approx_loc_sup 1;
   ba 1;
  by (Fast_tac 2);
 by (asm_full_simp_tac (simpset() addsimps [split_def,approx_val_def,approx_loc_append]) 1);
 br conjI 1;
  br conf_widen 1;
    ba 1;
   by (Fast_tac 2);
  by (asm_full_simp_tac (simpset() addsimps [conf_def]) 1);
 br conjI 1;
  by (fast_tac (claset() addIs [approx_stk_rev RS iffD2 RSN(4,assConv_approx_stk_imp_approx_loc)] 
	addss (simpset() addsimps [split_def,approx_val_def])) 1);
 by (asm_simp_tac (simpset() addsimps [list_all2_def,split_def,approx_loc_def,approx_val_None,set_replicate_conv_if]) 1);
 
br conjI 1;
 by (asm_simp_tac (simpset() addsimps [min_def]) 1);
br exI 1;
br exI 1;
br conjI 1;
 by(Blast_tac 1);
by (Clarsimp_tac 1);

by (fast_tac (claset()
       addIs [approx_stk_imp_approx_stk_sup,approx_loc_imp_approx_loc_sup]
       addss (simpset()addsimps [map_eq_Cons])) 1);
qed "Invoke_correct";

Addsimps (thms "app.simps");


Delsimps [map_append];
Goal
"\\<lbrakk> wt_jvm_prog G phi; \
\  method (G,C) sig = Some (C,rT,maxl,ins); \
\  ins ! pc = Return; \
\  wt_instr (ins!pc) G rT (phi C sig) (length ins) pc; \
\  Some state' = exec (G, None, hp, (stk,loc,C,sig,pc)#frs) ; \
\  G,phi \\<turnstile>JVM (None, hp, (stk,loc,C,sig,pc)#frs)\\<surd> \\<rbrakk> \
\\\<Longrightarrow> G,phi \\<turnstile>JVM state'\\<surd>";
by (asm_full_simp_tac (simpset() addsimps (neq_Nil_conv::defs1) addsplits [split_if_asm]) 1);
by (Clarify_tac 1);
by (asm_full_simp_tac (simpset() addsimps [map_eq_Cons]@defs1) 1);
by (Clarify_tac 1);
by (asm_full_simp_tac (simpset() addsimps defs1) 1);
by (forward_tac [thm "wt_jvm_prog_impl_wt_instr"] 1);
  by(EVERY1[atac, etac Suc_lessD]);
by(rewtac (thm "wt_jvm_prog_def"));
by (case_tac "phi ab (ac, b) ! k" 1);
by (fast_tac (claset()
 addDs [subcls_widen_methd]
 addEs [rotate_prems 1 widen_trans]
 addIs [conf_widen]
 addss (simpset() addsimps [approx_val_def,append_eq_conv_conj,map_eq_Cons]@defs1)) 1);
qed "Return_correct";
Addsimps [map_append];



Goal 
"\\<lbrakk> wf_prog wt G; \
\  method (G,C) sig = Some (C,rT,maxl,ins); \
\  ins ! pc = Goto branch; \
\  wt_instr (ins!pc) G rT (phi C sig) (length ins) pc; \
\  Some state' = exec (G, None, hp, (stk,loc,C,sig,pc)#frs) ; \
\  G,phi \\<turnstile>JVM (None, hp, (stk,loc,C,sig,pc)#frs)\\<surd> \\<rbrakk> \
\\\<Longrightarrow> G,phi \\<turnstile>JVM state'\\<surd>";
by (fast_tac (claset() addIs [approx_loc_imp_approx_loc_sup,approx_stk_imp_approx_stk_sup]
	addss (simpset() addsimps defs1)) 1);
qed "Goto_correct";


Goal 
"\\<lbrakk> wf_prog wt G; \
\  method (G,C) sig = Some (C,rT,maxl,ins); \
\  ins!pc = Ifcmpeq branch; \
\  wt_instr (ins!pc) G rT (phi C sig) (length ins) pc; \
\  Some state' = exec (G, None, hp, (stk,loc,C,sig,pc)#frs) ; \
\  G,phi \\<turnstile>JVM (None, hp, (stk,loc,C,sig,pc)#frs)\\<surd> \\<rbrakk> \
\\\<Longrightarrow> G,phi \\<turnstile>JVM state'\\<surd>";
by (fast_tac (claset() addIs [approx_stk_imp_approx_stk_sup,approx_loc_imp_approx_loc_sup] addss (simpset() addsimps defs1)) 1);
qed "Ifcmpeq_correct";


Goal 
"\\<lbrakk> wf_prog wt G; \
\  method (G,C) sig = Some (C,rT,maxl,ins); \
\  ins ! pc = Pop; \
\  wt_instr (ins!pc) G rT (phi C sig) (length ins) pc; \
\  Some state' = exec (G, None, hp, (stk,loc,C,sig,pc)#frs) ; \
\  G,phi \\<turnstile>JVM (None, hp, (stk,loc,C,sig,pc)#frs)\\<surd> \\<rbrakk> \
\\\<Longrightarrow> G,phi \\<turnstile>JVM state'\\<surd>";
by (fast_tac (claset() addIs [approx_stk_imp_approx_stk_sup,approx_loc_imp_approx_loc_sup] addss (simpset() addsimps defs1)) 1);
qed "Pop_correct";


Goal 
"\\<lbrakk> wf_prog wt G; \
\  method (G,C) sig = Some (C,rT,maxl,ins); \
\  ins ! pc = Dup; \
\  wt_instr (ins!pc) G rT (phi C sig) (length ins) pc; \
\  Some state' = exec (G, None, hp, (stk,loc,C,sig,pc)#frs) ; \
\  G,phi \\<turnstile>JVM (None, hp, (stk,loc,C,sig,pc)#frs)\\<surd> \\<rbrakk> \
\\\<Longrightarrow> G,phi \\<turnstile>JVM state'\\<surd>";
by (fast_tac (claset() addIs [approx_stk_imp_approx_stk_sup,approx_val_imp_approx_val_sup,approx_loc_imp_approx_loc_sup] 
	addss (simpset() addsimps [map_eq_Cons]@defs1)) 1);
qed "Dup_correct";



Goal 
"\\<lbrakk> wf_prog wt G; \
\  method (G,C) sig = Some (C,rT,maxl,ins); \
\  ins ! pc = Dup_x1; \
\  wt_instr (ins!pc) G rT (phi C sig) (length ins) pc; \
\  Some state' = exec (G, None, hp, (stk,loc,C,sig,pc)#frs) ; \
\  G,phi \\<turnstile>JVM (None, hp, (stk,loc,C,sig,pc)#frs)\\<surd> \\<rbrakk> \
\\\<Longrightarrow> G,phi \\<turnstile>JVM state'\\<surd>";
by (fast_tac (claset() addIs [approx_stk_imp_approx_stk_sup,approx_val_imp_approx_val_sup,approx_loc_imp_approx_loc_sup] 
	addss (simpset() addsimps [map_eq_Cons]@defs1)) 1);
qed "Dup_x1_correct";

Goal 
"\\<lbrakk> wf_prog wt G; \
\  method (G,C) sig = Some (C,rT,maxl,ins); \
\  ins ! pc = Dup_x2; \
\  wt_instr (ins!pc) G rT (phi C sig) (length ins) pc; \
\  Some state' = exec (G, None, hp, (stk,loc,C,sig,pc)#frs) ; \
\  G,phi \\<turnstile>JVM (None, hp, (stk,loc,C,sig,pc)#frs)\\<surd> \\<rbrakk> \
\\\<Longrightarrow> G,phi \\<turnstile>JVM state'\\<surd>";
by (fast_tac (claset() addIs [approx_stk_imp_approx_stk_sup,approx_val_imp_approx_val_sup,approx_loc_imp_approx_loc_sup] 
	addss (simpset() addsimps [map_eq_Cons]@defs1)) 1);
qed "Dup_x2_correct";

Goal 
"\\<lbrakk> wf_prog wt G; \
\  method (G,C) sig = Some (C,rT,maxl,ins); \
\  ins ! pc = Swap; \
\  wt_instr (ins!pc) G rT (phi C sig) (length ins) pc; \
\  Some state' = exec (G, None, hp, (stk,loc,C,sig,pc)#frs) ; \
\  G,phi \\<turnstile>JVM (None, hp, (stk,loc,C,sig,pc)#frs)\\<surd> \\<rbrakk> \
\\\<Longrightarrow> G,phi \\<turnstile>JVM state'\\<surd>";
by (fast_tac (claset() addIs [approx_stk_imp_approx_stk_sup,approx_val_imp_approx_val_sup,approx_loc_imp_approx_loc_sup] 
	addss (simpset() addsimps [map_eq_Cons]@defs1)) 1);
qed "Swap_correct";


Goal 
"\\<lbrakk> wf_prog wt G; \
\  method (G,C) sig = Some (C,rT,maxl,ins); \
\  ins ! pc = IAdd; \
\  wt_instr (ins!pc) G rT (phi C sig) (length ins) pc; \
\  Some state' = exec (G, None, hp, (stk,loc,C,sig,pc)#frs) ; \
\  G,phi \\<turnstile>JVM (None, hp, (stk,loc,C,sig,pc)#frs)\\<surd> \\<rbrakk> \
\\\<Longrightarrow> G,phi \\<turnstile>JVM state'\\<surd>";
by (fast_tac (claset() addIs [approx_stk_imp_approx_stk_sup,approx_val_imp_approx_val_sup,approx_loc_imp_approx_loc_sup]
  addss (simpset() addsimps [map_eq_Cons, approx_val_def]@defs1)) 1);
qed "IAdd_correct";



(** instr correct **)

Goal
"\\<lbrakk> wt_jvm_prog G phi; \
\  method (G,C) sig = Some (C,rT,maxl,ins); \
\  Some state' = exec (G, None, hp, (stk,loc,C,sig,pc)#frs) ; \
\  G,phi \\<turnstile>JVM (None, hp, (stk,loc,C,sig,pc)#frs)\\<surd> \\<rbrakk> \
\\\<Longrightarrow> G,phi \\<turnstile>JVM state'\\<surd>";
by(forward_tac [wt_jvm_prog_impl_wt_instr_cor] 1);
  ba 1;
 ba 1;
by(case_tac "ins!pc" 1);
by(fast_tac (claset() addIs [Invoke_correct]) 9);
by(fast_tac (claset() addIs [Return_correct]) 9);
by(rewtac (thm "wt_jvm_prog_def"));
by (ALLGOALS (fast_tac (claset() addIs 
      [Load_correct,Store_correct,Bipush_correct,Aconst_null_correct,
       Checkcast_correct,Getfield_correct,Putfield_correct,New_correct,
       Goto_correct,Ifcmpeq_correct,Pop_correct,Dup_correct,
       Dup_x1_correct,Dup_x2_correct,Swap_correct,IAdd_correct])));
qed "instr_correct";


(** Main **)

Goalw [correct_state_def,Let_def]
 "G,phi \\<turnstile>JVM (None, hp, (stk,loc,C,sig,pc)#frs)\\<surd> \
\ \\<Longrightarrow> \\<exists>meth. method (G,C) sig = Some(C,meth)";
by(Asm_full_simp_tac 1);
by(Blast_tac 1);
qed "correct_state_impl_Some_method";

Goal
"\\<And>state. \\<lbrakk> wt_jvm_prog G phi; G,phi \\<turnstile>JVM state\\<surd>\\<rbrakk> \
\ \\<Longrightarrow> exec (G,state) = Some state' \\<longrightarrow> G,phi \\<turnstile>JVM state'\\<surd>";
by(split_all_tac 1);
by(rename_tac "xp hp frs" 1);
by (case_tac "xp" 1);
 by (case_tac "frs" 1);
  by (asm_full_simp_tac (simpset() addsimps exec.simps) 1);
 by(split_all_tac 1);
 by(hyp_subst_tac 1);
 by(forward_tac [correct_state_impl_Some_method] 1);
 by (force_tac (claset() addIs [instr_correct], simpset() addsplits [split_if_asm] addsimps exec.simps@[split_def]) 1);
by (case_tac "frs" 1);
 by (ALLGOALS(asm_full_simp_tac (simpset() addsimps exec.simps)));
qed_spec_mp "BV_correct_1";

(*******)
Goal
"\\<lbrakk> xp=None; frs\\<noteq>[] \\<rbrakk> \\<Longrightarrow> (\\<exists>state'. exec (G,xp,hp,frs) = Some state')";
by (auto_tac (claset() addIs [BV_correct_1],
             (simpset() addsplits [instr.split] addsimps [neq_Nil_conv]@defs1)));
by (case_tac "(snd (snd (snd (the (method (G, ab) (ac, b)))))) ! ba" 1);
by (ALLGOALS (asm_simp_tac (simpset() addsimps defs1)));
val lemma = result();

Goal
"\\<lbrakk> wt_jvm_prog G phi; G,phi \\<turnstile>JVM (xp,hp,frs)\\<surd>; xp=None; frs\\<noteq>[] \\<rbrakk> \
\ \\<Longrightarrow> \\<exists>state'. exec(G,xp,hp,frs) = Some state' \\<and> G,phi \\<turnstile>JVM state'\\<surd>";
by (dres_inst_tac [("G","G"),("hp","hp")] lemma 1);
ba 1;
by (fast_tac (claset() addIs [BV_correct_1]) 1);
qed "L1";
(*******)

Goalw [exec_all_def]
"\\<lbrakk> wt_jvm_prog G phi; G \\<turnstile> s -jvm\\<rightarrow> t \\<rbrakk> \\<Longrightarrow> G,phi \\<turnstile>JVM s\\<surd> \\<longrightarrow> G,phi \\<turnstile>JVM t\\<surd>";
be rtrancl_induct 1;
 by (Simp_tac 1);
by (fast_tac (claset() addIs [BV_correct_1] addss (simpset())) 1);
qed_spec_mp "BV_correct";


Goal
"\\<lbrakk> wt_jvm_prog G phi; G \\<turnstile> s0 -jvm\\<rightarrow> (None,hp,(stk,loc,C,sig,pc)#frs); G,phi \\<turnstile>JVM s0 \\<surd>\\<rbrakk> \
\ \\<Longrightarrow>  approx_stk G hp stk (fst (((phi  C)  sig) ! pc)) \\<and> approx_loc G hp loc (snd (((phi  C)  sig) ! pc)) ";
bd BV_correct 1;
ba 1;
ba 1;
by (asm_full_simp_tac (simpset() addsimps [correct_state_def,correct_frame_def,split_def] 
	addsplits [option.split_asm]) 1);
qed_spec_mp "BV_correct_initial";
