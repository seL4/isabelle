(*  Title:      HOL/MicroJava/BV/BVSpecTypeSafe.thy
    ID:         $Id$
    Author:     Cornelia Pusch
    Copyright   1999 Technische Universitaet Muenchen
Proof that the specification of the bytecode verifier only admits type safe
programs.
*)

header "BV Type Safety Proof"

theory BVSpecTypeSafe = Correct:

lemmas defs1 = sup_state_conv correct_state_def correct_frame_def 
               wt_instr_def step_def

lemmas widen_rules[intro] = approx_val_widen approx_loc_widen approx_stk_widen

lemmas [simp del] = split_paired_All

lemma wt_jvm_prog_impl_wt_instr_cor:
  "[| wt_jvm_prog G phi; method (G,C) sig = Some (C,rT,maxs,maxl,ins); 
      G,phi \<turnstile>JVM (None, hp, (stk,loc,C,sig,pc)#frs)\<surd> |] 
  ==> wt_instr (ins!pc) G rT (phi C sig) maxs (length ins) pc"
apply (unfold correct_state_def Let_def correct_frame_def)
apply simp
apply (blast intro: wt_jvm_prog_impl_wt_instr)
done

section {* Single Instructions *}

lemmas [iff] = not_Err_eq

lemma Load_correct:
"[| wf_prog wt G;
    method (G,C) sig = Some (C,rT,maxs,maxl,ins); 
    ins!pc = Load idx; 
    wt_instr (ins!pc) G rT (phi C sig) maxs (length ins) pc; 
    Some state' = exec (G, None, hp, (stk,loc,C,sig,pc)#frs); 
    G,phi \<turnstile>JVM (None, hp, (stk,loc,C,sig,pc)#frs)\<surd> |] 
==> G,phi \<turnstile>JVM state'\<surd>"
apply (clarsimp simp add: defs1 map_eq_Cons)
apply (blast intro: approx_loc_imp_approx_val_sup)
done

lemma Store_correct:
"[| wf_prog wt G;
  method (G,C) sig = Some (C,rT,maxs,maxl,ins);
  ins!pc = Store idx;
  wt_instr (ins!pc) G rT (phi C sig) maxs (length ins) pc;
  Some state' = exec (G, None, hp, (stk,loc,C,sig,pc)#frs);
  G,phi \<turnstile>JVM (None, hp, (stk,loc,C,sig,pc)#frs)\<surd> |]
==> G,phi \<turnstile>JVM state'\<surd>"
apply (clarsimp simp add: defs1 map_eq_Cons)
apply (blast intro: approx_loc_subst)
done


lemma LitPush_correct:
"[| wf_prog wt G;
    method (G,C) sig = Some (C,rT,maxs,maxl,ins); 
    ins!pc = LitPush v;
    wt_instr (ins!pc) G rT (phi C sig) maxs (length ins) pc; 
    Some state' = exec (G, None, hp, (stk,loc,C,sig,pc)#frs);
    G,phi \<turnstile>JVM (None, hp, (stk,loc,C,sig,pc)#frs)\<surd> |]
==> G,phi \<turnstile>JVM state'\<surd>" 
apply (clarsimp simp add: defs1 sup_PTS_eq map_eq_Cons)
apply (blast dest: conf_litval intro: conf_widen)
done


lemma Cast_conf2:
  "[| wf_prog ok G; G,h\<turnstile>v::\<preceq>RefT rt; cast_ok G C h v; 
      G\<turnstile>Class C\<preceq>T; is_class G C|] 
  ==> G,h\<turnstile>v::\<preceq>T"
apply (unfold cast_ok_def)
apply (frule widen_Class)
apply (elim exE disjE) 
 apply (simp add: null)
apply (clarsimp simp add: conf_def obj_ty_def)
apply (cases v)
apply (auto intro: rtrancl_trans)
done


lemma Checkcast_correct:
"[| wf_prog wt G;
    method (G,C) sig = Some (C,rT,maxs,maxl,ins); 
    ins!pc = Checkcast D; 
    wt_instr (ins!pc) G rT (phi C sig) maxs (length ins) pc; 
    Some state' = exec (G, None, hp, (stk,loc,C,sig,pc)#frs) ; 
    G,phi \<turnstile>JVM (None, hp, (stk,loc,C,sig,pc)#frs)\<surd> |] 
==> G,phi \<turnstile>JVM state'\<surd>"
apply (clarsimp simp add: defs1 map_eq_Cons raise_xcpt_def)
apply (blast intro: Cast_conf2)
done


lemma Getfield_correct:
"[| wf_prog wt G;
  method (G,C) sig = Some (C,rT,maxs,maxl,ins); 
  ins!pc = Getfield F D; 
  wt_instr (ins!pc) G rT (phi C sig) maxs (length ins) pc; 
  Some state' = exec (G, None, hp, (stk,loc,C,sig,pc)#frs) ; 
  G,phi \<turnstile>JVM (None, hp, (stk,loc,C,sig,pc)#frs)\<surd> |] 
==> G,phi \<turnstile>JVM state'\<surd>"
apply (clarsimp simp add: defs1 raise_xcpt_def map_eq_Cons
                split: option.split)
apply (frule conf_widen)
apply assumption+
apply (drule conf_RefTD)
apply (clarsimp simp add: defs1)
apply (rule conjI)
 apply (drule widen_cfs_fields)
 apply assumption+
 apply (force intro: conf_widen simp add: hconf_def oconf_def lconf_def)
apply blast
done

lemma Putfield_correct:
"[| wf_prog wt G;
  method (G,C) sig = Some (C,rT,maxs,maxl,ins); 
  ins!pc = Putfield F D; 
  wt_instr (ins!pc) G rT (phi C sig) maxs (length ins) pc; 
  Some state' = exec (G, None, hp, (stk,loc,C,sig,pc)#frs) ; 
  G,phi \<turnstile>JVM (None, hp, (stk,loc,C,sig,pc)#frs)\<surd> |] 
==> G,phi \<turnstile>JVM state'\<surd>"
apply (clarsimp simp add: defs1 raise_xcpt_def split: option.split List.split)
apply (frule conf_widen)
prefer 2
  apply assumption
 apply assumption
apply (drule conf_RefTD)
apply clarsimp
apply (blast 
       intro: 
         hext_upd_obj approx_stk_sup_heap
         approx_loc_sup_heap 
         hconf_field_update
         correct_frames_field_update conf_widen 
       dest: 
         widen_cfs_fields)
done

lemma New_correct:
"[| wf_prog wt G;
  method (G,C) sig = Some (C,rT,maxs,maxl,ins); 
  ins!pc = New X; 
  wt_instr (ins!pc) G rT (phi C sig) maxs (length ins) pc; 
  Some state' = exec (G, None, hp, (stk,loc,C,sig,pc)#frs) ; 
  G,phi \<turnstile>JVM (None, hp, (stk,loc,C,sig,pc)#frs)\<surd> |] 
==> G,phi \<turnstile>JVM state'\<surd>"
proof -
  assume wf:   "wf_prog wt G"
  assume meth: "method (G,C) sig = Some (C,rT,maxs,maxl,ins)"
  assume ins:  "ins!pc = New X"
  assume wt:   "wt_instr (ins!pc) G rT (phi C sig) maxs (length ins) pc"
  assume exec: "Some state' = exec (G, None, hp, (stk,loc,C,sig,pc)#frs)"
  assume conf: "G,phi \<turnstile>JVM (None, hp, (stk,loc,C,sig,pc)#frs)\<surd>"

  from ins conf meth
  obtain ST LT where
    heap_ok:    "G\<turnstile>h hp\<surd>" and
    phi_pc:     "phi C sig!pc = Some (ST,LT)" and
    is_class_C: "is_class G C" and
    frame:      "correct_frame G hp (ST,LT) maxl ins (stk, loc, C, sig, pc)" and
    frames:     "correct_frames G hp phi rT sig frs"
    by (auto simp add: correct_state_def iff del: not_None_eq)

  from phi_pc ins wt
  obtain ST' LT' where
    is_class_X: "is_class G X" and
    maxs:       "maxs < length ST" and
    suc_pc:     "Suc pc < length ins" and
    phi_suc:    "phi C sig ! Suc pc = Some (ST', LT')" and
    less:       "G \<turnstile> (Class X # ST, LT) <=s (ST', LT')"
    by (unfold wt_instr_def step_def) auto
 
  obtain oref xp' where
    new_Addr: "(oref,xp') = new_Addr hp"
    by (cases "new_Addr hp") auto  
  hence cases: 
    "hp oref = None \<and> xp' = None \<or> xp' = Some OutOfMemory"
    by (blast dest: new_AddrD)
  moreover
  { assume "xp' = Some OutOfMemory"
    with exec ins meth new_Addr [symmetric]
    have "state' = (Some OutOfMemory, hp, (stk,loc,C,sig,Suc pc)#frs)" by simp
    hence ?thesis by (simp add: correct_state_def)
  }
  moreover
  { assume hp: "hp oref = None" and "xp' = None"
    with exec ins meth new_Addr [symmetric]
    have state':
      "state' = Norm (hp(oref\<mapsto>(X, init_vars (fields (G, X)))), 
                      (Addr oref # stk, loc, C, sig, Suc pc) # frs)" 
      (is "state' = Norm (?hp', ?f # frs)")
      by simp    
    moreover
    from wf hp heap_ok is_class_X
    have hp': "G \<turnstile>h ?hp' \<surd>"
      by - (rule hconf_newref, 
            auto simp add: oconf_def dest: fields_is_type)
    moreover
    from hp
    have sup: "hp \<le>| ?hp'" by (rule hext_new)
    from hp frame less suc_pc wf
    have "correct_frame G ?hp' (ST', LT') maxl ins ?f"
      apply (unfold correct_frame_def sup_state_conv)
      apply (clarsimp simp add: map_eq_Cons conf_def fun_upd_apply approx_val_def)
      apply (blast intro: approx_stk_sup_heap approx_loc_sup_heap sup)
      done      
    moreover
    from hp frames wf heap_ok is_class_X
    have "correct_frames G ?hp' phi rT sig frs"
      by - (rule correct_frames_newref,
            auto simp add: oconf_def dest: fields_is_type)
    ultimately
    have ?thesis
      by (simp add: is_class_C meth phi_suc correct_state_def del: not_None_eq)
  }
  ultimately
  show ?thesis by auto
qed

lemmas [simp del] = split_paired_Ex

lemma Invoke_correct: 
"[| wt_jvm_prog G phi; 
  method (G,C) sig = Some (C,rT,maxs,maxl,ins); 
  ins ! pc = Invoke C' mn pTs; 
  wt_instr (ins!pc) G rT (phi C sig) maxs (length ins) pc; 
  Some state' = exec (G, None, hp, (stk,loc,C,sig,pc)#frs) ; 
  G,phi \<turnstile>JVM (None, hp, (stk,loc,C,sig,pc)#frs)\<surd> |] 
==> G,phi \<turnstile>JVM state'\<surd>" 
proof -
  assume wtprog: "wt_jvm_prog G phi"
  assume method: "method (G,C) sig = Some (C,rT,maxs,maxl,ins)"
  assume ins:    "ins ! pc = Invoke C' mn pTs"
  assume wti:    "wt_instr (ins!pc) G rT (phi C sig) maxs (length ins) pc"
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
    is_class_C: "is_class G C" and
    frame:   "correct_frame G hp s maxl ins (stk, loc, C, sig, pc)" and
    frames:  "correct_frames G hp phi rT sig frs"
    by (clarsimp simp add: correct_state_def iff del: not_None_eq)

  from ins wti phi_pc
  obtain apTs X ST LT D' rT body where 
    is_class: "is_class G C'" and
    s:  "s = (rev apTs @ X # ST, LT)" and
    l:  "length apTs = length pTs" and
    X:  "G\<turnstile> X \<preceq> Class C'" and
    w:  "\<forall>x\<in>set (zip apTs pTs). x \<in> widen G" and
    mC':"method (G, C') (mn, pTs) = Some (D', rT, body)" and
    pc: "Suc pc < length ins" and
    step: "G \<turnstile> step (Invoke C' mn pTs) G (Some s) <=' phi C sig!Suc pc"
    by (simp add: wt_instr_def del: not_None_eq) (elim exE conjE, rule that)

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
    oX:     "approx_val G hp oX (OK X)" and
    a_stk': "approx_stk G hp stk' ST" and
    stk':   "stk = opTs @ oX # stk'" and
    l_o:    "length opTs = length apTs" 
            "length stk' = length ST"  
    by - (drule approx_stk_append, simp, elim, simp)

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
  have oX_pos: "last (take (Suc (length pTs)) stk) = oX" by simp

  with state' method ins 
  have Null_ok: "oX = Null ==> ?thesis"
    by (simp add: correct_state_def raise_xcpt_def)
  
  { fix ref assume oX_Addr: "oX = Addr ref"
    
    with oX_Ref
    obtain obj where
      loc: "hp ref = Some obj" "obj_ty obj = RefT T'"
      by auto

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
    have X'_subcls: "G \<turnstile> X' \<preceq>C C'" 
      by simp

    with mC' wfprog
    obtain D0 rT0 maxs0 maxl0 ins0 where
      mX: "method (G, X') (mn, pTs) = Some (D0, rT0, maxs0, maxl0, ins0)" "G\<turnstile>rT0\<preceq>rT"
      by (auto dest: subtype_widen_methd intro: that)

    from X' D
    have D_subcls: "G \<turnstile> D \<preceq>C X'" 
      by simp

    with wfprog mX
    obtain D'' rT' mxs' mxl' ins' where
      mD: "method (G, D) (mn, pTs) = Some (D'', rT', mxs', mxl', ins')" 
          "G \<turnstile> rT' \<preceq> rT0"
      by (auto dest: subtype_widen_methd intro: that)

    from mX mD
    have rT': "G \<turnstile> rT' \<preceq> rT"
      by - (rule widen_trans)
    
    from is_class X'_subcls D_subcls
    have is_class_D: "is_class G D"
    by (auto dest: subcls_is_class2)

    with mD wfprog
    obtain mD'': 
      "method (G, D'') (mn, pTs) = Some (D'', rT', mxs', mxl', ins')"
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
      by (clarsimp simp add: wt_start_def sup_state_conv)

    have c_f: "correct_frame G hp ([], LT0) mxl' ins' ?f"
    proof -
      from start LT0
      have sup_loc: 
        "G \<turnstile> (OK (Class D'') # map OK pTs @ replicate mxl' Err) <=l LT0"
        (is "G \<turnstile> ?LT <=l LT0")
        by (simp add: wt_start_def sup_state_conv)

      have r: "approx_loc G hp (replicate mxl' arbitrary) (replicate mxl' Err)"
        by (simp add: approx_loc_def approx_val_Err 
                      list_all2_def set_replicate_conv_if)

      from wfprog mD is_class_D
      have "G \<turnstile> Class D \<preceq> Class D''"
        by (auto dest: method_wf_mdecl)
      with obj_ty loc
      have a: "approx_val G hp (Addr ref) (OK (Class D''))"
        by (simp add: approx_val_def conf_def)

      from opTs w l l_o wfprog 
      have "approx_stk G hp opTs (rev pTs)" 
	by (auto elim!: approx_stk_all_widen simp add: zip_rev)
      hence "approx_stk G hp (rev opTs) pTs" by (subst approx_stk_rev)

      with r a l_o l
      have "approx_loc G hp (Addr ref # rev opTs @ replicate mxl' arbitrary) ?LT"
        (is "approx_loc G hp ?lt ?LT")
        by (auto simp add: approx_loc_append approx_stk_def)

      from this sup_loc wfprog
      have "approx_loc G hp ?lt LT0" by (rule approx_loc_widen)
      with start l_o l
      show ?thesis by (simp add: correct_frame_def)
    qed

    have c_f': "correct_frame G hp (tl ST', LT') maxl ins ?f'"
    proof -    
      from s s' mC' step l
      have "G \<turnstile> LT <=l LT'"
        by (simp add: step_def sup_state_conv)
      with wfprog a_loc
      have a: "approx_loc G hp loc LT'"
        by - (rule approx_loc_widen)
      moreover
      from s s' mC' step l
      have  "G \<turnstile> map OK ST <=l map OK (tl ST')"
        by (auto simp add: step_def sup_state_conv map_eq_Cons)
      with wfprog a_stk'
      have "approx_stk G hp stk' (tl ST')"
        by - (rule approx_stk_widen)
      ultimately
      show ?thesis by (simp add: correct_frame_def suc_l pc)
    qed

    with state'_val heap_ok mD'' ins method phi_pc s X' l 
         frames s' LT0 c_f c_f' is_class_C
    have ?thesis 
      by (simp add: correct_state_def) (intro exI conjI, blast, assumption+)
  }
  
  with Null_ok oX_Ref
  show "G,phi \<turnstile>JVM state'\<surd>" by - (cases oX, auto)
qed

lemmas [simp del] = map_append

lemma Return_correct:
"[| wt_jvm_prog G phi; 
  method (G,C) sig = Some (C,rT,maxs,maxl,ins); 
  ins ! pc = Return; 
  wt_instr (ins!pc) G rT (phi C sig) maxs (length ins) pc; 
  Some state' = exec (G, None, hp, (stk,loc,C,sig,pc)#frs) ; 
  G,phi \<turnstile>JVM (None, hp, (stk,loc,C,sig,pc)#frs)\<surd> |] 
==> G,phi \<turnstile>JVM state'\<surd>"
apply (clarsimp simp add: neq_Nil_conv defs1 split: split_if_asm iff del: not_None_eq)
apply (frule wt_jvm_prog_impl_wt_instr)
apply (assumption, assumption, erule Suc_lessD)
apply (clarsimp simp add: map_eq_Cons append_eq_conv_conj defs1)
apply (unfold wt_jvm_prog_def)
apply (frule subcls_widen_methd, assumption+)
apply clarify
apply simp
apply (erule conf_widen, assumption)
apply (erule widen_trans)+
apply blast
done

lemmas [simp] = map_append

lemma Goto_correct:
"[| wf_prog wt G; 
  method (G,C) sig = Some (C,rT,maxs,maxl,ins); 
  ins ! pc = Goto branch; 
  wt_instr (ins!pc) G rT (phi C sig) maxs (length ins) pc; 
  Some state' = exec (G, None, hp, (stk,loc,C,sig,pc)#frs) ; 
  G,phi \<turnstile>JVM (None, hp, (stk,loc,C,sig,pc)#frs)\<surd> |] 
==> G,phi \<turnstile>JVM state'\<surd>"
apply (clarsimp simp add: defs1)
apply fast
done


lemma Ifcmpeq_correct:
"[| wf_prog wt G; 
  method (G,C) sig = Some (C,rT,maxs,maxl,ins); 
  ins ! pc = Ifcmpeq branch; 
  wt_instr (ins!pc) G rT (phi C sig) maxs (length ins) pc; 
  Some state' = exec (G, None, hp, (stk,loc,C,sig,pc)#frs) ; 
  G,phi \<turnstile>JVM (None, hp, (stk,loc,C,sig,pc)#frs)\<surd> |] 
==> G,phi \<turnstile>JVM state'\<surd>"
apply (clarsimp simp add: defs1)
apply fast
done

lemma Pop_correct:
"[| wf_prog wt G; 
  method (G,C) sig = Some (C,rT,maxs,maxl,ins); 
  ins ! pc = Pop;
  wt_instr (ins!pc) G rT (phi C sig) maxs (length ins) pc; 
  Some state' = exec (G, None, hp, (stk,loc,C,sig,pc)#frs) ; 
  G,phi \<turnstile>JVM (None, hp, (stk,loc,C,sig,pc)#frs)\<surd> |] 
==> G,phi \<turnstile>JVM state'\<surd>"
apply (clarsimp simp add: defs1)
apply fast
done

lemma Dup_correct:
"[| wf_prog wt G; 
  method (G,C) sig = Some (C,rT,maxs,maxl,ins); 
  ins ! pc = Dup;
  wt_instr (ins!pc) G rT (phi C sig) maxs (length ins) pc; 
  Some state' = exec (G, None, hp, (stk,loc,C,sig,pc)#frs) ; 
  G,phi \<turnstile>JVM (None, hp, (stk,loc,C,sig,pc)#frs)\<surd> |] 
==> G,phi \<turnstile>JVM state'\<surd>"
apply (clarsimp simp add: defs1 map_eq_Cons)
apply (blast intro: conf_widen)
done

lemma Dup_x1_correct:
"[| wf_prog wt G; 
  method (G,C) sig = Some (C,rT,maxs,maxl,ins); 
  ins ! pc = Dup_x1;
  wt_instr (ins!pc) G rT (phi C sig) maxs (length ins) pc; 
  Some state' = exec (G, None, hp, (stk,loc,C,sig,pc)#frs) ; 
  G,phi \<turnstile>JVM (None, hp, (stk,loc,C,sig,pc)#frs)\<surd> |] 
==> G,phi \<turnstile>JVM state'\<surd>"
apply (clarsimp simp add: defs1 map_eq_Cons)
apply (blast intro: conf_widen)
done

lemma Dup_x2_correct:
"[| wf_prog wt G; 
  method (G,C) sig = Some (C,rT,maxs,maxl,ins); 
  ins ! pc = Dup_x2;
  wt_instr (ins!pc) G rT (phi C sig) maxs (length ins) pc; 
  Some state' = exec (G, None, hp, (stk,loc,C,sig,pc)#frs) ; 
  G,phi \<turnstile>JVM (None, hp, (stk,loc,C,sig,pc)#frs)\<surd> |] 
==> G,phi \<turnstile>JVM state'\<surd>"
apply (clarsimp simp add: defs1 map_eq_Cons)
apply (blast intro: conf_widen)
done

lemma Swap_correct:
"[| wf_prog wt G; 
  method (G,C) sig = Some (C,rT,maxs,maxl,ins); 
  ins ! pc = Swap;
  wt_instr (ins!pc) G rT (phi C sig) maxs (length ins) pc; 
  Some state' = exec (G, None, hp, (stk,loc,C,sig,pc)#frs) ; 
  G,phi \<turnstile>JVM (None, hp, (stk,loc,C,sig,pc)#frs)\<surd> |] 
==> G,phi \<turnstile>JVM state'\<surd>"
apply (clarsimp simp add: defs1 map_eq_Cons)
apply (blast intro: conf_widen)
done

lemma IAdd_correct:
"[| wf_prog wt G; 
  method (G,C) sig = Some (C,rT,maxs,maxl,ins); 
  ins ! pc = IAdd; 
  wt_instr (ins!pc) G rT (phi C sig) maxs (length ins) pc; 
  Some state' = exec (G, None, hp, (stk,loc,C,sig,pc)#frs) ; 
  G,phi \<turnstile>JVM (None, hp, (stk,loc,C,sig,pc)#frs)\<surd> |] 
==> G,phi \<turnstile>JVM state'\<surd>"
apply (clarsimp simp add: defs1 map_eq_Cons approx_val_def conf_def)
apply blast
done


lemma instr_correct:
"[| wt_jvm_prog G phi;
  method (G,C) sig = Some (C,rT,maxs,maxl,ins); 
  Some state' = exec (G, None, hp, (stk,loc,C,sig,pc)#frs); 
  G,phi \<turnstile>JVM (None, hp, (stk,loc,C,sig,pc)#frs)\<surd> |] 
==> G,phi \<turnstile>JVM state'\<surd>"
apply (frule wt_jvm_prog_impl_wt_instr_cor)
apply assumption+
apply (cases "ins!pc")
prefer 8
apply (rule Invoke_correct, assumption+)
prefer 8
apply (rule Return_correct, assumption+)

apply (unfold wt_jvm_prog_def)
apply (rule Load_correct, assumption+)
apply (rule Store_correct, assumption+)
apply (rule LitPush_correct, assumption+)
apply (rule New_correct, assumption+)
apply (rule Getfield_correct, assumption+)
apply (rule Putfield_correct, assumption+)
apply (rule Checkcast_correct, assumption+)
apply (rule Pop_correct, assumption+)
apply (rule Dup_correct, assumption+)
apply (rule Dup_x1_correct, assumption+)
apply (rule Dup_x2_correct, assumption+)
apply (rule Swap_correct, assumption+)
apply (rule IAdd_correct, assumption+)
apply (rule Goto_correct, assumption+)
apply (rule Ifcmpeq_correct, assumption+)
done

section {* Main *}

lemma correct_state_impl_Some_method:
  "G,phi \<turnstile>JVM (None, hp, (stk,loc,C,sig,pc)#frs)\<surd> 
  ==> \<exists>meth. method (G,C) sig = Some(C,meth)"
by (auto simp add: correct_state_def Let_def)


lemma BV_correct_1 [rule_format]:
"!!state. [| wt_jvm_prog G phi; G,phi \<turnstile>JVM state\<surd>|] 
 ==> exec (G,state) = Some state' --> G,phi \<turnstile>JVM state'\<surd>"
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
  "[| xp=None; frs\<noteq>[] |] ==> (\<exists>state'. exec (G,xp,hp,frs) = Some state')"
by (clarsimp simp add: neq_Nil_conv simp del: split_paired_Ex)

lemma L1:
  "[|wt_jvm_prog G phi; G,phi \<turnstile>JVM (xp,hp,frs)\<surd>; xp=None; frs\<noteq>[]|] 
  ==> \<exists>state'. exec(G,xp,hp,frs) = Some state' \<and> G,phi \<turnstile>JVM state'\<surd>"
apply (drule L0)
apply assumption
apply (fast intro: BV_correct_1)
done


theorem BV_correct [rule_format]:
"[| wt_jvm_prog G phi; G \<turnstile> s -jvm-> t |] ==> G,phi \<turnstile>JVM s\<surd> --> G,phi \<turnstile>JVM t\<surd>"
apply (unfold exec_all_def)
apply (erule rtrancl_induct)
 apply simp
apply (auto intro: BV_correct_1)
done


theorem BV_correct_initial:
"[| wt_jvm_prog G phi; 
    G \<turnstile> s0 -jvm-> (None,hp,(stk,loc,C,sig,pc)#frs); G,phi \<turnstile>JVM s0 \<surd>|] 
==> approx_stk G hp stk (fst (the (((phi  C)  sig) ! pc))) \<and> 
    approx_loc G hp loc (snd (the (((phi  C)  sig) ! pc)))"
apply (drule BV_correct)
apply assumption+
apply (simp add: correct_state_def correct_frame_def split_def 
            split: option.splits)
done

end
