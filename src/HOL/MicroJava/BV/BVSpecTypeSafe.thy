(*  Title:      HOL/MicroJava/BV/BVSpecTypeSafe.thy
    ID:         $Id$
    Author:     Cornelia Pusch
    Copyright   1999 Technische Universitaet Muenchen

Proof that the specification of the bytecode verifier only admits type safe
programs.
*)

header "Type Safety Proof"

theory BVSpecTypeSafe = Correct:

lemmas defs1 = sup_state_def correct_state_def correct_frame_def wt_instr_def step_def
lemmas [simp del] = split_paired_All

lemma wt_jvm_prog_impl_wt_instr_cor:
  "[| wt_jvm_prog G phi; method (G,C) sig = Some (C,rT,maxl,ins); 
      G,phi \<turnstile>JVM (None, hp, (stk,loc,C,sig,pc)#frs)\<surd> |] 
  ==> wt_instr (ins!pc) G rT (phi C sig) (length ins) pc"
apply (unfold correct_state_def Let_def correct_frame_def)
apply simp
apply (blast intro: wt_jvm_prog_impl_wt_instr)
done

lemma Load_correct:
"\<lbrakk> wf_prog wt G;
   method (G,C) sig = Some (C,rT,maxl,ins); 
   ins!pc = Load idx; 
   wt_instr (ins!pc) G rT (phi C sig) (length ins) pc; 
   Some state' = exec (G, None, hp, (stk,loc,C,sig,pc)#frs); 
   G,phi \<turnstile>JVM (None, hp, (stk,loc,C,sig,pc)#frs)\<surd> \<rbrakk> 
\<Longrightarrow> G,phi \<turnstile>JVM state'\<surd>"
apply (clarsimp simp add: defs1 map_eq_Cons)
apply (rule conjI)
 apply (rule approx_loc_imp_approx_val_sup)
 apply simp+
apply (blast intro: approx_stk_imp_approx_stk_sup approx_loc_imp_approx_loc_sup)
done

lemma Store_correct:
"\<lbrakk> wf_prog wt G;
  method (G,C) sig = Some (C,rT,maxl,ins);
  ins!pc = Store idx;
  wt_instr (ins!pc) G rT (phi C sig) (length ins) pc;
  Some state' = exec (G, None, hp, (stk,loc,C,sig,pc)#frs);
  G,phi \<turnstile>JVM (None, hp, (stk,loc,C,sig,pc)#frs)\<surd> \<rbrakk>
\<Longrightarrow> G,phi \<turnstile>JVM state'\<surd>"
apply (clarsimp simp add: defs1 map_eq_Cons)
apply (rule conjI)
 apply (blast intro: approx_stk_imp_approx_stk_sup)
apply (blast intro: approx_loc_imp_approx_loc_subst approx_loc_imp_approx_loc_sup)
done


lemma conf_Intg_Integer [iff]:
  "G,h \<turnstile> Intg i \<Colon>\<preceq> PrimT Integer"
by (simp add: conf_def)


lemma Bipush_correct:
"\<lbrakk> wf_prog wt G;
  method (G,C) sig = Some (C,rT,maxl,ins); 
  ins!pc = Bipush i; 
  wt_instr (ins!pc) G rT (phi C sig) (length ins) pc; 
  Some state' = exec (G, None, hp, (stk,loc,C,sig,pc)#frs);
  G,phi \<turnstile>JVM (None, hp, (stk,loc,C,sig,pc)#frs)\<surd> \<rbrakk>
\<Longrightarrow> G,phi \<turnstile>JVM state'\<surd>"
apply (clarsimp simp add: defs1 approx_val_def sup_PTS_eq map_eq_Cons)
apply (blast intro: approx_stk_imp_approx_stk_sup approx_loc_imp_approx_loc_sup)
done

lemma NT_subtype_conv:
  "G \<turnstile> NT \<preceq> T = (T=NT \<or> (\<exists>C. T = Class C))"
proof -
  have "\<And>T T'. G \<turnstile> T' \<preceq> T \<Longrightarrow> T' = NT \<longrightarrow> (T=NT | (\<exists>C. T = Class C))"
    apply (erule widen.induct)
    apply auto
    apply (case_tac R)
    apply auto
    done
  note l = this

  show ?thesis 
    by (force intro: null dest: l)
qed

lemma Aconst_null_correct:
"\<lbrakk> wf_prog wt G;
  method (G,C) sig = Some (C,rT,maxl,ins); 
  ins!pc =  Aconst_null; 
  wt_instr (ins!pc) G rT (phi C sig) (length ins) pc; 
  Some state' = exec (G, None, hp, (stk,loc,C,sig,pc)#frs); 
  G,phi \<turnstile>JVM (None, hp, (stk,loc,C,sig,pc)#frs)\<surd> \<rbrakk> 
\<Longrightarrow> G,phi \<turnstile>JVM state'\<surd>"
apply (clarsimp simp add: defs1 map_eq_Cons)
apply (rule conjI)
 apply (force simp add: approx_val_Null NT_subtype_conv)
apply (blast intro: approx_stk_imp_approx_stk_sup approx_loc_imp_approx_loc_sup)
done


lemma Cast_conf2:
  "\<lbrakk>wf_prog ok G; G,h\<turnstile>v\<Colon>\<preceq>RefT rt; cast_ok G C h v; G\<turnstile>Class C\<preceq>T; is_class G C\<rbrakk> 
  \<Longrightarrow> G,h\<turnstile>v\<Colon>\<preceq>T"
apply (unfold cast_ok_def)
apply (frule widen_Class)
apply (elim exE disjE)
 apply (simp add: null)
apply (clarsimp simp add: conf_def obj_ty_def)
apply (cases v)
apply (auto intro: null rtrancl_trans)
done


lemma Checkcast_correct:
"\<lbrakk> wf_prog wt G;
  method (G,C) sig = Some (C,rT,maxl,ins); 
  ins!pc = Checkcast D; 
  wt_instr (ins!pc) G rT (phi C sig) (length ins) pc; 
  Some state' = exec (G, None, hp, (stk,loc,C,sig,pc)#frs) ; 
  G,phi \<turnstile>JVM (None, hp, (stk,loc,C,sig,pc)#frs)\<surd> \<rbrakk> 
\<Longrightarrow> G,phi \<turnstile>JVM state'\<surd>"
apply (clarsimp simp add: defs1 map_eq_Cons raise_xcpt_def approx_val_def)
apply (blast intro: approx_stk_imp_approx_stk_sup approx_loc_imp_approx_loc_sup Cast_conf2)
done


lemma Getfield_correct:
"\<lbrakk> wf_prog wt G;
  method (G,C) sig = Some (C,rT,maxl,ins); 
  ins!pc = Getfield F D; 
  wt_instr (ins!pc) G rT (phi C sig) (length ins) pc; 
  Some state' = exec (G, None, hp, (stk,loc,C,sig,pc)#frs) ; 
  G,phi \<turnstile>JVM (None, hp, (stk,loc,C,sig,pc)#frs)\<surd> \<rbrakk> 
\<Longrightarrow> G,phi \<turnstile>JVM state'\<surd>"
apply (clarsimp simp add: defs1 raise_xcpt_def map_eq_Cons approx_val_def split: option.split)
apply (frule conf_widen)
apply assumption+
apply (drule conf_RefTD)
apply (clarsimp simp add: defs1 approx_val_def)
apply (rule conjI)
 apply (drule widen_cfs_fields)
 apply assumption+
 apply (force intro: conf_widen simp add: hconf_def oconf_def lconf_def)
apply (blast intro: approx_stk_imp_approx_stk_sup approx_loc_imp_approx_loc_sup)
done

lemma Putfield_correct:
"\<lbrakk> wf_prog wt G;
  method (G,C) sig = Some (C,rT,maxl,ins); 
  ins!pc = Putfield F D; 
  wt_instr (ins!pc) G rT (phi C sig) (length ins) pc; 
  Some state' = exec (G, None, hp, (stk,loc,C,sig,pc)#frs) ; 
  G,phi \<turnstile>JVM (None, hp, (stk,loc,C,sig,pc)#frs)\<surd> \<rbrakk> 
\<Longrightarrow> G,phi \<turnstile>JVM state'\<surd>"
apply (clarsimp simp add: defs1 raise_xcpt_def split: option.split List.split)
apply (clarsimp simp add: approx_val_def)
apply (frule conf_widen)
prefer 2
apply assumption
apply assumption
apply (drule conf_RefTD)
apply clarsimp
apply (blast intro: sup_heap_update_value approx_stk_imp_approx_stk_sup_heap
  approx_stk_imp_approx_stk_sup
  approx_loc_imp_approx_loc_sup_heap approx_loc_imp_approx_loc_sup
  hconf_imp_hconf_field_update
  correct_frames_imp_correct_frames_field_update conf_widen dest: widen_cfs_fields)
done

lemma collapse_paired_All:
  "(\<forall>x y. P(x,y)) = (\<forall>z. P z)"
  by fast

lemma New_correct:
"\<lbrakk> wf_prog wt G;
  method (G,C) sig = Some (C,rT,maxl,ins); 
  ins!pc = New cl_idx; 
  wt_instr (ins!pc) G rT (phi C sig) (length ins) pc; 
  Some state' = exec (G, None, hp, (stk,loc,C,sig,pc)#frs) ; 
  G,phi \<turnstile>JVM (None, hp, (stk,loc,C,sig,pc)#frs)\<surd> \<rbrakk> 
\<Longrightarrow> G,phi \<turnstile>JVM state'\<surd>"
apply (clarsimp simp add: NT_subtype_conv approx_val_def conf_def
		   fun_upd_apply map_eq_Cons is_class_def raise_xcpt_def init_vars_def defs1 
       split: option.split)
apply (force dest!: iffD1 [OF collapse_paired_All]
            intro: sup_heap_newref approx_stk_imp_approx_stk_sup_heap approx_stk_imp_approx_stk_sup
                   approx_loc_imp_approx_loc_sup_heap approx_loc_imp_approx_loc_sup
                   hconf_imp_hconf_newref correct_frames_imp_correct_frames_newref
                   correct_init_obj simp add:  NT_subtype_conv approx_val_def conf_def
		   fun_upd_apply map_eq_Cons is_class_def raise_xcpt_def init_vars_def defs1 
       split: option.split)
done


(****** Method Invocation ******)

lemmas [simp del] = split_paired_Ex

lemma Invoke_correct:
"\<lbrakk> wt_jvm_prog G phi; 
  method (G,C) sig = Some (C,rT,maxl,ins); 
  ins ! pc = Invoke C' mn pTs; 
  wt_instr (ins!pc) G rT (phi C sig) (length ins) pc; 
  Some state' = exec (G, None, hp, (stk,loc,C,sig,pc)#frs) ; 
  G,phi \<turnstile>JVM (None, hp, (stk,loc,C,sig,pc)#frs)\<surd> \<rbrakk> 
\<Longrightarrow> G,phi \<turnstile>JVM state'\<surd>" 
proof -
  assume wtprog: "wt_jvm_prog G phi"
  assume method: "method (G,C) sig = Some (C,rT,maxl,ins)"
  assume ins:    "ins ! pc = Invoke C' mn pTs"
  assume wti:    "wt_instr (ins!pc) G rT (phi C sig) (length ins) pc"
  assume state': "Some state' = exec (G, None, hp, (stk,loc,C,sig,pc)#frs)"
  assume approx: "G,phi \<turnstile>JVM (None, hp, (stk,loc,C,sig,pc)#frs)\<surd>"
  
  from wtprog 
  obtain wfmb where
    wfprog: "wf_prog wfmb G" 
    by (simp add: wt_jvm_prog_def)

  from ins method approx
  obtain s where
    heap_ok: "G\<turnstile>h hp\<surd>" and
    phi_pc:  "phi C sig!pc = Some s" and
    frame:   "correct_frame G hp s maxl ins (stk, loc, C, sig, pc)" and
    frames:  "correct_frames G hp phi rT sig frs"
    by (clarsimp simp add: correct_state_def)

  from ins wti phi_pc
  obtain apTs X ST LT D' rT body where 
    s: "s = (rev apTs @ X # ST, LT)" and
    l: "length apTs = length pTs" and
    X: "G\<turnstile> X \<preceq> Class C'" and
    w: "\<forall>x\<in>set (zip apTs pTs). x \<in> widen G" and
    mC': "method (G, C') (mn, pTs) = Some (D', rT, body)" and
    pc:  "Suc pc < length ins" and
    step: "G \<turnstile> step (Invoke C' mn pTs) G (Some s) <=' phi C sig!Suc pc"
    by (simp add: wt_instr_def) (elim exE conjE, rule that)

  from step
  obtain ST' LT' where
    s': "phi C sig ! Suc pc = Some (ST', LT')"
    by (simp add: step_def split_paired_Ex) (elim, rule that)

  from X 
  obtain T where
    X_Ref: "X = RefT T"
    by - (drule widen_RefT2, erule exE, rule that)
  
  from s ins frame 
  obtain 
    a_stk: "approx_stk G hp stk (rev apTs @ X # ST)" and
    a_loc: "approx_loc G hp loc LT" and
    suc_l: "length loc = Suc (length (snd sig) + maxl)"
    by (simp add: correct_frame_def)

  from a_stk
  obtain opTs stk' oX where
    opTs:   "approx_stk G hp opTs (rev apTs)" and
    oX:     "approx_val G hp oX (Ok X)" and
    a_stk': "approx_stk G hp stk' ST" and
    stk':   "stk = opTs @ oX # stk'" and
    l_o:    "length opTs = length apTs" 
            "length stk' = length ST" 
    by - (drule approx_stk_append_lemma, simp, elim, simp)

  from oX 
  have "\<exists>T'. typeof (option_map obj_ty \<circ> hp) oX = Some T' \<and> G \<turnstile> T' \<preceq> X"
    by (clarsimp simp add: approx_val_def conf_def)

  with X_Ref
  obtain T' where
    oX_Ref: "typeof (option_map obj_ty \<circ> hp) oX = Some (RefT T')"
            "G \<turnstile> RefT T' \<preceq> X" 
    apply (elim, simp)
    apply (frule widen_RefT2)
    by (elim, simp)

  from stk' l_o l
  have oX_pos: "last (take (Suc (length pTs)) stk) = oX" 
    by simp

  with state' method ins 
  have Null_ok: "oX = Null \<Longrightarrow> ?thesis"
    by (simp add: correct_state_def raise_xcpt_def)
  
  { fix ref
    assume oX_Addr: "oX = Addr ref"
    
    with oX_Ref
    obtain obj where
      loc: "hp ref = Some obj" "obj_ty obj = RefT T'"
      by clarsimp

    then 
    obtain D where
      obj_ty: "obj_ty obj = Class D"
      by (auto simp add: obj_ty_def)

    with X_Ref oX_Ref loc
    obtain D: "G \<turnstile> Class D \<preceq> X"
      by simp

    with X_Ref
    obtain X' where 
      X': "X = Class X'"
      by - (drule widen_Class, elim, rule that)
      
    with X
    have "G \<turnstile> X' \<preceq>C C'" 
      by simp

    with mC' wfprog
    obtain D0 rT0 maxl0 ins0 where
      mX: "method (G, X') (mn, pTs) = Some (D0, rT0, maxl0, ins0)" "G\<turnstile>rT0\<preceq>rT"
      by (auto dest: subtype_widen_methd)

    from X' D
    have "G \<turnstile> D \<preceq>C X'" 
      by simp

    with wfprog mX
    obtain D'' rT' mxl' ins' where
      mD: "method (G, D) (mn, pTs) = Some (D'', rT', mxl', ins')" 
          "G \<turnstile> rT' \<preceq> rT0"
      by (auto dest: subtype_widen_methd)

    from mX mD
    have rT': "G \<turnstile> rT' \<preceq> rT"
      by - (rule widen_trans)
    
    from mD wfprog
    obtain mD'': 
      "method (G, D'') (mn, pTs) = Some (D'', rT', mxl', ins')"
      "is_class G D''" 
      by (auto dest: method_in_md)
      
    from loc obj_ty
    have "fst (the (hp ref)) = D"
      by (simp add: obj_ty_def)

    with oX_Addr oX_pos state' method ins stk' l_o l loc obj_ty mD 
    have state'_val:
      "state' =
       Norm (hp, ([], Addr ref # rev opTs @ replicate mxl' arbitrary, 
                  D'', (mn, pTs), 0) # (stk', loc, C, sig, Suc pc) # frs)"
      (is "state' = Norm (hp, ?f # ?f' # frs)")
      by (simp add: raise_xcpt_def)
    
    from wtprog mD''
    have start: "wt_start G D'' pTs mxl' (phi D'' (mn, pTs)) \<and> ins' \<noteq> []"
      by (auto dest: wt_jvm_prog_impl_wt_start)
    
    then
    obtain LT0 where
      LT0: "phi D'' (mn, pTs) ! 0 = Some ([], LT0)"
      by (clarsimp simp add: wt_start_def sup_state_def)

    have c_f: "correct_frame G hp ([], LT0) mxl' ins' ?f"
    proof -
      from start LT0
      have sup_loc: 
        "G \<turnstile> (Ok (Class D'') # map Ok pTs @ replicate mxl' Err) <=l LT0"
        (is "G \<turnstile> ?LT <=l LT0")
        by (simp add: wt_start_def sup_state_def)

      have r: "approx_loc G hp (replicate mxl' arbitrary) (replicate mxl' Err)"
        by (simp add: approx_loc_def approx_val_Err list_all2_def set_replicate_conv_if)

      from wfprog mD
      have "G \<turnstile> Class D \<preceq> Class D''"
        by (auto dest: method_wf_mdecl)
      with obj_ty loc
      have a: "approx_val G hp (Addr ref) (Ok (Class D''))"
        by (simp add: approx_val_def conf_def)

      from w l
      have "\<forall>x\<in>set (zip (rev apTs) (rev pTs)). x \<in> widen G"
        by (auto simp add: zip_rev)
      with wfprog l l_o opTs
      have "approx_loc G hp opTs (map Ok (rev pTs))"
        by (auto intro: assConv_approx_stk_imp_approx_loc)
      hence "approx_stk G hp opTs (rev pTs)"
        by (simp add: approx_stk_def)
      hence "approx_stk G hp (rev opTs) pTs"
        by (simp add: approx_stk_rev)

      with r a l_o l
      have "approx_loc G hp (Addr ref # rev opTs @ replicate mxl' arbitrary) ?LT"
        (is "approx_loc G hp ?lt ?LT")
        by (auto simp add: approx_loc_append approx_stk_def)

      from wfprog this sup_loc
      have "approx_loc G hp ?lt LT0"
        by (rule approx_loc_imp_approx_loc_sup)

      with start l_o l
      show ?thesis
        by (simp add: correct_frame_def)
    qed

    have c_f': "correct_frame G hp (tl ST', LT') maxl ins ?f'"
    proof -    
      from s s' mC' step l
      have "G \<turnstile> LT <=l LT'"
        by (simp add: step_def sup_state_def)
      with wfprog a_loc
      have a: "approx_loc G hp loc LT'"
        by (rule approx_loc_imp_approx_loc_sup)
      moreover
      from s s' mC' step l
      have  "G \<turnstile> map Ok ST <=l map Ok (tl ST')"
        by (auto simp add: step_def sup_state_def map_eq_Cons)
      with wfprog a_stk'
      have "approx_stk G hp stk' (tl ST')"
        by (rule approx_stk_imp_approx_stk_sup)
      ultimately
      show ?thesis
        by (simp add: correct_frame_def suc_l pc)
    qed

    with state'_val heap_ok mD'' ins method phi_pc s X' l 
         frames s' LT0 c_f c_f'
    have ?thesis
      by (simp add: correct_state_def) (intro exI conjI, force+)
  }
  
  with Null_ok oX_Ref
  show "G,phi \<turnstile>JVM state'\<surd>"
    by - (cases oX, auto)
qed

lemmas [simp del] = map_append

lemma Return_correct:
"\<lbrakk> wt_jvm_prog G phi;  
  method (G,C) sig = Some (C,rT,maxl,ins); 
  ins ! pc = Return; 
  wt_instr (ins!pc) G rT (phi C sig) (length ins) pc; 
  Some state' = exec (G, None, hp, (stk,loc,C,sig,pc)#frs) ; 
  G,phi \<turnstile>JVM (None, hp, (stk,loc,C,sig,pc)#frs)\<surd> \<rbrakk> 
\<Longrightarrow> G,phi \<turnstile>JVM state'\<surd>"
apply (clarsimp simp add: neq_Nil_conv defs1 split: split_if_asm)
apply (frule wt_jvm_prog_impl_wt_instr)
apply (assumption, erule Suc_lessD)
apply (unfold wt_jvm_prog_def)
apply (fastsimp
  dest: subcls_widen_methd
  elim: widen_trans [COMP swap_prems_rl]
  intro: conf_widen
  simp: approx_val_def append_eq_conv_conj map_eq_Cons defs1)
done

lemmas [simp] = map_append

lemma Goto_correct:
"\<lbrakk> wf_prog wt G; 
  method (G,C) sig = Some (C,rT,maxl,ins); 
  ins ! pc = Goto branch; 
  wt_instr (ins!pc) G rT (phi C sig) (length ins) pc; 
  Some state' = exec (G, None, hp, (stk,loc,C,sig,pc)#frs) ; 
  G,phi \<turnstile>JVM (None, hp, (stk,loc,C,sig,pc)#frs)\<surd> \<rbrakk> 
\<Longrightarrow> G,phi \<turnstile>JVM state'\<surd>"
apply (clarsimp simp add: defs1)
apply (fast intro: approx_loc_imp_approx_loc_sup approx_stk_imp_approx_stk_sup)
done


lemma Ifcmpeq_correct:
"\<lbrakk> wf_prog wt G; 
  method (G,C) sig = Some (C,rT,maxl,ins); 
  ins ! pc = Ifcmpeq branch; 
  wt_instr (ins!pc) G rT (phi C sig) (length ins) pc; 
  Some state' = exec (G, None, hp, (stk,loc,C,sig,pc)#frs) ; 
  G,phi \<turnstile>JVM (None, hp, (stk,loc,C,sig,pc)#frs)\<surd> \<rbrakk> 
\<Longrightarrow> G,phi \<turnstile>JVM state'\<surd>"
apply (clarsimp simp add: defs1)
apply (fast intro: approx_loc_imp_approx_loc_sup approx_stk_imp_approx_stk_sup)
done

lemma Pop_correct:
"\<lbrakk> wf_prog wt G; 
  method (G,C) sig = Some (C,rT,maxl,ins); 
  ins ! pc = Pop;
  wt_instr (ins!pc) G rT (phi C sig) (length ins) pc; 
  Some state' = exec (G, None, hp, (stk,loc,C,sig,pc)#frs) ; 
  G,phi \<turnstile>JVM (None, hp, (stk,loc,C,sig,pc)#frs)\<surd> \<rbrakk> 
\<Longrightarrow> G,phi \<turnstile>JVM state'\<surd>"
apply (clarsimp simp add: defs1)
apply (fast intro: approx_loc_imp_approx_loc_sup approx_stk_imp_approx_stk_sup)
done

lemma Dup_correct:
"\<lbrakk> wf_prog wt G; 
  method (G,C) sig = Some (C,rT,maxl,ins); 
  ins ! pc = Dup;
  wt_instr (ins!pc) G rT (phi C sig) (length ins) pc; 
  Some state' = exec (G, None, hp, (stk,loc,C,sig,pc)#frs) ; 
  G,phi \<turnstile>JVM (None, hp, (stk,loc,C,sig,pc)#frs)\<surd> \<rbrakk> 
\<Longrightarrow> G,phi \<turnstile>JVM state'\<surd>"
apply (clarsimp simp add: defs1 map_eq_Cons)
apply (force intro: approx_stk_imp_approx_stk_sup approx_val_imp_approx_val_sup approx_loc_imp_approx_loc_sup
             simp add: defs1 map_eq_Cons)
done

lemma Dup_x1_correct:
"\<lbrakk> wf_prog wt G; 
  method (G,C) sig = Some (C,rT,maxl,ins); 
  ins ! pc = Dup_x1;
  wt_instr (ins!pc) G rT (phi C sig) (length ins) pc; 
  Some state' = exec (G, None, hp, (stk,loc,C,sig,pc)#frs) ; 
  G,phi \<turnstile>JVM (None, hp, (stk,loc,C,sig,pc)#frs)\<surd> \<rbrakk> 
\<Longrightarrow> G,phi \<turnstile>JVM state'\<surd>"
apply (clarsimp simp add: defs1 map_eq_Cons)
apply (force intro: approx_stk_imp_approx_stk_sup approx_val_imp_approx_val_sup approx_loc_imp_approx_loc_sup
             simp add: defs1 map_eq_Cons)
done

lemma Dup_x2_correct:
"\<lbrakk> wf_prog wt G; 
  method (G,C) sig = Some (C,rT,maxl,ins); 
  ins ! pc = Dup_x2;
  wt_instr (ins!pc) G rT (phi C sig) (length ins) pc; 
  Some state' = exec (G, None, hp, (stk,loc,C,sig,pc)#frs) ; 
  G,phi \<turnstile>JVM (None, hp, (stk,loc,C,sig,pc)#frs)\<surd> \<rbrakk> 
\<Longrightarrow> G,phi \<turnstile>JVM state'\<surd>"
apply (clarsimp simp add: defs1 map_eq_Cons)
apply (force intro: approx_stk_imp_approx_stk_sup approx_val_imp_approx_val_sup approx_loc_imp_approx_loc_sup
             simp add: defs1 map_eq_Cons)
done

lemma Swap_correct:
"\<lbrakk> wf_prog wt G; 
  method (G,C) sig = Some (C,rT,maxl,ins); 
  ins ! pc = Swap;
  wt_instr (ins!pc) G rT (phi C sig) (length ins) pc; 
  Some state' = exec (G, None, hp, (stk,loc,C,sig,pc)#frs) ; 
  G,phi \<turnstile>JVM (None, hp, (stk,loc,C,sig,pc)#frs)\<surd> \<rbrakk> 
\<Longrightarrow> G,phi \<turnstile>JVM state'\<surd>"
apply (clarsimp simp add: defs1 map_eq_Cons)
apply (force intro: approx_stk_imp_approx_stk_sup approx_val_imp_approx_val_sup approx_loc_imp_approx_loc_sup
             simp add: defs1 map_eq_Cons)
done

lemma IAdd_correct:
"\<lbrakk> wf_prog wt G; 
  method (G,C) sig = Some (C,rT,maxl,ins); 
  ins ! pc = IAdd; 
  wt_instr (ins!pc) G rT (phi C sig) (length ins) pc; 
  Some state' = exec (G, None, hp, (stk,loc,C,sig,pc)#frs) ; 
  G,phi \<turnstile>JVM (None, hp, (stk,loc,C,sig,pc)#frs)\<surd> \<rbrakk> 
\<Longrightarrow> G,phi \<turnstile>JVM state'\<surd>"
apply (clarsimp simp add: defs1 map_eq_Cons approx_val_def conf_def)
apply (blast intro: approx_stk_imp_approx_stk_sup approx_val_imp_approx_val_sup approx_loc_imp_approx_loc_sup)
done


(** instr correct **)

lemma instr_correct:
"\<lbrakk> wt_jvm_prog G phi; 
  method (G,C) sig = Some (C,rT,maxl,ins); 
  Some state' = exec (G, None, hp, (stk,loc,C,sig,pc)#frs); 
  G,phi \<turnstile>JVM (None, hp, (stk,loc,C,sig,pc)#frs)\<surd> \<rbrakk> 
\<Longrightarrow> G,phi \<turnstile>JVM state'\<surd>"
apply (frule wt_jvm_prog_impl_wt_instr_cor)
apply assumption+
apply (cases "ins!pc")
prefer 9
apply (blast intro: Invoke_correct)
prefer 9
apply (blast intro: Return_correct)
apply (unfold wt_jvm_prog_def)
apply (fast intro: Load_correct Store_correct Bipush_correct Aconst_null_correct 
       Checkcast_correct Getfield_correct Putfield_correct New_correct 
       Goto_correct Ifcmpeq_correct Pop_correct Dup_correct 
       Dup_x1_correct Dup_x2_correct Swap_correct IAdd_correct)+
done


(** Main **)

lemma correct_state_impl_Some_method:
  "G,phi \<turnstile>JVM (None, hp, (stk,loc,C,sig,pc)#frs)\<surd> 
  \<Longrightarrow> \<exists>meth. method (G,C) sig = Some(C,meth)"
by (auto simp add: correct_state_def Let_def)


lemma BV_correct_1 [rule_format]:
"\<And>state. \<lbrakk> wt_jvm_prog G phi; G,phi \<turnstile>JVM state\<surd>\<rbrakk> 
 \<Longrightarrow> exec (G,state) = Some state' \<longrightarrow> G,phi \<turnstile>JVM state'\<surd>"
apply (simp only: split_tupled_all)
apply (rename_tac xp hp frs)
apply (case_tac xp)
 apply (case_tac frs)
  apply simp
 apply (simp only: split_tupled_all)
 apply hypsubst
 apply (frule correct_state_impl_Some_method)
 apply (force intro: instr_correct)
apply (case_tac frs)
apply simp_all
done


lemma L0:
  "\<lbrakk> xp=None; frs\<noteq>[] \<rbrakk> \<Longrightarrow> (\<exists>state'. exec (G,xp,hp,frs) = Some state')"
by (clarsimp simp add: neq_Nil_conv simp del: split_paired_Ex)

lemma L1:
  "\<lbrakk>wt_jvm_prog G phi; G,phi \<turnstile>JVM (xp,hp,frs)\<surd>; xp=None; frs\<noteq>[]\<rbrakk> 
  \<Longrightarrow> \<exists>state'. exec(G,xp,hp,frs) = Some state' \<and> G,phi \<turnstile>JVM state'\<surd>"
apply (drule L0)
apply assumption
apply (fast intro: BV_correct_1)
done


theorem BV_correct [rule_format]:
"\<lbrakk> wt_jvm_prog G phi; G \<turnstile> s -jvm\<rightarrow> t \<rbrakk> \<Longrightarrow> G,phi \<turnstile>JVM s\<surd> \<longrightarrow> G,phi \<turnstile>JVM t\<surd>"
apply (unfold exec_all_def)
apply (erule rtrancl_induct)
 apply simp
apply (auto intro: BV_correct_1)
done


theorem BV_correct_initial:
"\<lbrakk> wt_jvm_prog G phi; G \<turnstile> s0 -jvm\<rightarrow> (None,hp,(stk,loc,C,sig,pc)#frs); G,phi \<turnstile>JVM s0 \<surd>\<rbrakk> 
 \<Longrightarrow>  approx_stk G hp stk (fst (the (((phi  C)  sig) ! pc))) \<and> approx_loc G hp loc (snd (the (((phi  C)  sig) ! pc)))"
apply (drule BV_correct)
apply assumption+
apply (simp add: correct_state_def correct_frame_def split_def split: option.splits)
done

end
