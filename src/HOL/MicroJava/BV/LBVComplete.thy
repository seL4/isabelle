(*  Title:      HOL/MicroJava/BV/LBVComplete.thy
    ID:         $Id$
    Author:     Gerwin Klein
    Copyright   2000 Technische Universitaet Muenchen
*)

header {* \isaheader{Completeness of the LBV} *}

theory LBVComplete = LBVSpec + Typing_Framework:

constdefs
  contains_targets :: "['s steptype, 's certificate, 's option list, nat] \<Rightarrow> bool"
  "contains_targets step cert phi pc \<equiv>
  \<forall>(pc',s') \<in> set (step pc (OK (phi!pc))). pc' \<noteq> pc+1 \<and> pc' < length phi \<longrightarrow> cert!pc' = phi!pc'"

  fits :: "['s steptype, 's certificate, 's option list] \<Rightarrow> bool"
  "fits step cert phi \<equiv> \<forall>pc. pc < length phi \<longrightarrow> 
                             contains_targets step cert phi pc \<and>
                             (cert!pc = None \<or> cert!pc = phi!pc)"

  is_target :: "['s steptype, 's option list, nat] \<Rightarrow> bool" 
  "is_target step phi pc' \<equiv>
     \<exists>pc s'. pc' \<noteq> pc+1 \<and> pc < length phi \<and> (pc',s') \<in> set (step pc (OK (phi!pc)))"

  make_cert :: "['s steptype, 's option list] \<Rightarrow> 's certificate"
  "make_cert step phi \<equiv> 
     map (\<lambda>pc. if is_target step phi pc then phi!pc else None) [0..length phi(]"

  
lemmas [simp del] = split_paired_Ex

lemma make_cert_target:
  "\<lbrakk> pc < length phi; is_target step phi pc \<rbrakk> \<Longrightarrow> make_cert step phi ! pc = phi!pc"
  by (simp add: make_cert_def)

lemma make_cert_approx:
  "\<lbrakk> pc < length phi; make_cert step phi ! pc \<noteq> phi!pc \<rbrakk> \<Longrightarrow> 
   make_cert step phi ! pc = None"
  by (auto simp add: make_cert_def)

lemma make_cert_contains_targets:
  "pc < length phi \<Longrightarrow> contains_targets step (make_cert step phi) phi pc"
proof (unfold contains_targets_def, clarify)
  fix pc' s'
  assume "pc < length phi"
         "(pc',s') \<in> set (step pc (OK (phi ! pc)))"
         "pc' \<noteq> pc+1" and
    pc': "pc' < length phi"
  hence "is_target step phi pc'"  by (auto simp add: is_target_def)
  with pc' show "make_cert step phi ! pc' = phi!pc'" 
    by (auto intro: make_cert_target)
qed

theorem fits_make_cert:
  "fits step (make_cert step phi) phi"
  by (auto dest: make_cert_approx simp add: fits_def make_cert_contains_targets)

lemma fitsD: 
  "\<lbrakk> fits step cert phi; (pc',s') \<in> set (step pc (OK (phi ! pc)));
      pc' \<noteq> Suc pc; pc < length phi; pc' < length phi \<rbrakk>
  \<Longrightarrow> cert!pc' = phi!pc'"
  by (auto simp add: fits_def contains_targets_def)

lemma fitsD2:
   "\<lbrakk> fits step cert phi; pc < length phi; cert!pc = Some s \<rbrakk>
  \<Longrightarrow> cert!pc = phi!pc"
  by (auto simp add: fits_def)


lemma merge_mono:
  assumes merge: "merge cert f r pc ss1 x = OK s1"
  assumes less:  "ss2 <=|Err.le (Opt.le r)| ss1"
  shows "\<exists>s2. merge cert f r pc ss2 x = s2 \<and> s2 \<le>|r (OK s1)"
proof-
  from merge
  obtain "\<forall>(pc',s')\<in>set ss1. pc' \<noteq> pc+1 \<longrightarrow> s' \<le>|r (OK (cert!pc'))" and
         "(map snd [(p',t')\<in>ss1 . p' = pc+1] ++|f x) = OK s1"
    sorry
  show ?thesis sorry
qed
  
  
lemma stable_wtl:
  assumes stable: "stable (Err.le (Opt.le r)) step (map OK phi) pc"
  assumes fits:   "fits step cert phi"  
  assumes pc:     "pc < length phi"
  assumes bounded:"bounded step (length phi)"
  shows "wtl_inst cert f r step pc (phi!pc) \<noteq> Err"
proof -
  from pc have [simp]: "map OK phi ! pc = OK (phi!pc)" by simp
  from stable 
  have "\<forall>(q,s')\<in>set (step pc (OK (phi!pc))). s' \<le>|r (map OK phi!q)"
    by (simp add: stable_def)
  
  have "merge cert f r pc (step pc (OK (phi ! pc))) (OK (cert ! Suc pc)) \<noteq> Err"
    sorry
  thus ?thesis by (simp add: wtl_inst_def)  
qed


lemma wtl_inst_mono:
  assumes wtl:  "wtl_inst cert f r step pc s1 = OK s1'"
  assumes fits: "fits step cert phi n"
  assumes pc:   "pc < n" 
  assumes less: "OK s2 \<le>|r (OK s1)"
  shows "\<exists>s2'. wtl_inst cert f r step pc s2 = OK s2' \<and> OK s2' \<le>|r (OK s1')"
apply (simp add: wtl_inst_def)

                           
lemma wtl_inst_mono:
  "\<lbrakk> wtl_inst i G rT s1 cert mxs mpc pc = OK s1'; fits ins cert phi; 
      pc < length ins;  G \<turnstile> s2 <=' s1; i = ins!pc \<rbrakk> \<Longrightarrow>
  \<exists> s2'. wtl_inst (ins!pc) G rT s2 cert mxs mpc pc = OK s2' \<and> (G \<turnstile> s2' <=' s1')"
proof -
  assume pc:   "pc < length ins" "i = ins!pc"
  assume wtl:  "wtl_inst i G rT s1 cert mxs mpc pc = OK s1'"
  assume fits: "fits ins cert phi"
  assume G:    "G \<turnstile> s2 <=' s1"
  
  let "?eff s" = "eff i G s"

  from wtl G
  have app: "app i G mxs rT s2" by (auto simp add: wtl_inst_OK app_mono)
  
  from wtl G
  have eff: "G \<turnstile> ?eff s2 <=' ?eff s1" 
    by (auto intro: eff_mono simp add: wtl_inst_OK)

  { also
    fix pc'
    assume "pc' \<in> set (succs i pc)" "pc' \<noteq> pc+1"
    with wtl 
    have "G \<turnstile> ?eff s1 <=' cert!pc'"
      by (auto simp add: wtl_inst_OK) 
    finally
    have "G\<turnstile> ?eff s2 <=' cert!pc'" .
  } note cert = this
    
  have "\<exists>s2'. wtl_inst i G rT s2 cert mxs mpc pc = OK s2' \<and> G \<turnstile> s2' <=' s1'"
  proof (cases "pc+1 \<in> set (succs i pc)")
    case True
    with wtl
    have s1': "s1' = ?eff s1" by (simp add: wtl_inst_OK)

    have "wtl_inst i G rT s2 cert mxs mpc pc = OK (?eff s2) \<and> G \<turnstile> ?eff s2 <=' s1'" 
      (is "?wtl \<and> ?G")
    proof
      from True s1'
      show ?G by (auto intro: eff)

      from True app wtl
      show ?wtl
        by (clarsimp intro!: cert simp add: wtl_inst_OK)
    qed
    thus ?thesis by blast
  next
    case False
    with wtl
    have "s1' = cert ! Suc pc" by (simp add: wtl_inst_OK)

    with False app wtl
    have "wtl_inst i G rT s2 cert mxs mpc pc = OK s1' \<and> G \<turnstile> s1' <=' s1'"
      by (clarsimp intro!: cert simp add: wtl_inst_OK)

    thus ?thesis by blast
  qed
  
  with pc show ?thesis by simp
qed


lemma wtl_cert_mono:
  "\<lbrakk> wtl_cert i G rT s1 cert mxs mpc pc = OK s1'; fits ins cert phi; 
      pc < length ins; G \<turnstile> s2 <=' s1; i = ins!pc \<rbrakk> \<Longrightarrow>
  \<exists> s2'. wtl_cert (ins!pc) G rT s2 cert mxs mpc pc = OK s2' \<and> (G \<turnstile> s2' <=' s1')"
proof -
  assume wtl:  "wtl_cert i G rT s1 cert mxs mpc pc = OK s1'" and
         fits: "fits ins cert phi" "pc < length ins"
               "G \<turnstile> s2 <=' s1" "i = ins!pc"

  show ?thesis
  proof (cases (open) "cert!pc")
    case None
    with wtl fits
    show ?thesis 
      by - (rule wtl_inst_mono [elim_format], (simp add: wtl_cert_def)+)
  next
    case Some
    with wtl fits

    have G: "G \<turnstile> s2 <=' (Some a)"
      by - (rule sup_state_opt_trans, auto simp add: wtl_cert_def split: if_splits)

    from Some wtl
    have "wtl_inst i G rT (Some a) cert mxs mpc pc = OK s1'" 
      by (simp add: wtl_cert_def split: if_splits)

    with G fits
    have "\<exists> s2'. wtl_inst (ins!pc) G rT (Some a) cert mxs mpc pc = OK s2' \<and> 
                 (G \<turnstile> s2' <=' s1')"
      by - (rule wtl_inst_mono, (simp add: wtl_cert_def)+)
    
    with Some G
    show ?thesis by (simp add: wtl_cert_def)
  qed
qed

 
lemma wt_instr_imp_wtl_inst:
  "\<lbrakk> wt_instr (ins!pc) G rT phi mxs max_pc pc; fits ins cert phi;
      pc < length ins; length ins = max_pc \<rbrakk> \<Longrightarrow> 
  wtl_inst (ins!pc) G rT (phi!pc) cert mxs max_pc pc \<noteq> Err"
 proof -
  assume wt:   "wt_instr (ins!pc) G rT phi mxs max_pc pc" 
  assume fits: "fits ins cert phi"
  assume pc:   "pc < length ins" "length ins = max_pc"

  from wt 
  have app: "app (ins!pc) G mxs rT (phi!pc)" by (simp add: wt_instr_def)

  from wt pc
  have pc': "\<And>pc'. pc' \<in> set (succs (ins!pc) pc) \<Longrightarrow> pc' < length ins"
    by (simp add: wt_instr_def)

  let ?s' = "eff (ins!pc) G (phi!pc)"

  from wt fits pc
  have cert: "\<And>pc'. \<lbrakk>pc' \<in> set (succs (ins!pc) pc); pc' < max_pc; pc' \<noteq> pc+1\<rbrakk> 
    \<Longrightarrow> G \<turnstile> ?s' <=' cert!pc'"
    by (auto dest: fitsD simp add: wt_instr_def)     

  from app pc cert pc'
  show ?thesis
    by (auto simp add: wtl_inst_OK)
qed

lemma wt_less_wtl:
  "\<lbrakk> wt_instr (ins!pc) G rT phi mxs max_pc pc; 
      wtl_inst (ins!pc) G rT (phi!pc) cert mxs max_pc pc = OK s;
      fits ins cert phi; Suc pc < length ins; length ins = max_pc \<rbrakk> \<Longrightarrow> 
  G \<turnstile> s <=' phi ! Suc pc"
proof -
  assume wt:   "wt_instr (ins!pc) G rT phi mxs max_pc pc" 
  assume wtl:  "wtl_inst (ins!pc) G rT (phi!pc) cert mxs max_pc pc = OK s"
  assume fits: "fits ins cert phi"
  assume pc:   "Suc pc < length ins" "length ins = max_pc"

  { assume suc: "Suc pc \<in> set (succs (ins ! pc) pc)"
    with wtl have "s = eff (ins!pc) G (phi!pc)"
      by (simp add: wtl_inst_OK)
    also from suc wt have "G \<turnstile> \<dots> <=' phi!Suc pc"
      by (simp add: wt_instr_def)
    finally have ?thesis .
  }

  moreover
  { assume "Suc pc \<notin> set (succs (ins ! pc) pc)"
    
    with wtl
    have "s = cert!Suc pc" 
      by (simp add: wtl_inst_OK)
    with fits pc
    have ?thesis
      by - (cases "cert!Suc pc", simp, drule fitsD2, assumption+, simp)
  }

  ultimately
  show ?thesis by blast
qed
  

lemma wt_instr_imp_wtl_cert:
  "\<lbrakk> wt_instr (ins!pc) G rT phi mxs max_pc pc; fits ins cert phi;
      pc < length ins; length ins = max_pc \<rbrakk> \<Longrightarrow> 
  wtl_cert (ins!pc) G rT (phi!pc) cert mxs max_pc pc \<noteq> Err"
proof -
  assume "wt_instr (ins!pc) G rT phi mxs max_pc pc" and 
   fits: "fits ins cert phi" and
     pc: "pc < length ins" and
         "length ins = max_pc"
  
  hence wtl: "wtl_inst (ins!pc) G rT (phi!pc) cert mxs max_pc pc \<noteq> Err"
    by (rule wt_instr_imp_wtl_inst)

  hence "cert!pc = None \<Longrightarrow> ?thesis"
    by (simp add: wtl_cert_def)

  moreover
  { fix s
    assume c: "cert!pc = Some s"
    with fits pc
    have "cert!pc = phi!pc"
      by (rule fitsD2)
    from this c wtl
    have ?thesis
      by (clarsimp simp add: wtl_cert_def)
  }

  ultimately
  show ?thesis by blast
qed
  

lemma wt_less_wtl_cert:
  "\<lbrakk> wt_instr (ins!pc) G rT phi mxs max_pc pc; 
      wtl_cert (ins!pc) G rT (phi!pc) cert mxs max_pc pc = OK s;
      fits ins cert phi; Suc pc < length ins; length ins = max_pc \<rbrakk> \<Longrightarrow> 
  G \<turnstile> s <=' phi ! Suc pc"
proof -
  assume wtl: "wtl_cert (ins!pc) G rT (phi!pc) cert mxs max_pc pc = OK s"

  assume wti: "wt_instr (ins!pc) G rT phi mxs max_pc pc"
              "fits ins cert phi" 
              "Suc pc < length ins" "length ins = max_pc"
  
  { assume "cert!pc = None"
    with wtl
    have "wtl_inst (ins!pc) G rT (phi!pc) cert mxs max_pc pc = OK s"
      by (simp add: wtl_cert_def)
    with wti
    have ?thesis
      by - (rule wt_less_wtl)
  }
  moreover
  { fix t
    assume c: "cert!pc = Some t"
    with wti
    have "cert!pc = phi!pc"
      by - (rule fitsD2, simp+)
    with c wtl
    have "wtl_inst (ins!pc) G rT (phi!pc) cert mxs max_pc pc = OK s"
      by (simp add: wtl_cert_def)
    with wti
    have ?thesis
      by - (rule wt_less_wtl)
  }   
    
  ultimately
  show ?thesis by blast
qed

text {*
  \medskip
  Main induction over the instruction list.
*}

theorem wt_imp_wtl_inst_list:
"\<forall> pc. (\<forall>pc'. pc' < length all_ins \<longrightarrow> 
        wt_instr (all_ins ! pc') G rT phi mxs (length all_ins) pc') \<longrightarrow>
       fits all_ins cert phi \<longrightarrow> 
       (\<exists>l. pc = length l \<and> all_ins = l@ins) \<longrightarrow>  
       pc < length all_ins \<longrightarrow>      
       (\<forall> s. (G \<turnstile> s <=' (phi!pc)) \<longrightarrow> 
             wtl_inst_list ins G rT cert mxs (length all_ins) pc s \<noteq> Err)" 
(is "\<forall>pc. ?wt \<longrightarrow> ?fits \<longrightarrow> ?l pc ins \<longrightarrow> ?len pc \<longrightarrow> ?wtl pc ins"  
 is "\<forall>pc. ?C pc ins" is "?P ins") 
proof (induct "?P" "ins")
  case Nil
  show "?P []" by simp
next
  fix i ins'
  assume Cons: "?P ins'"

  show "?P (i#ins')" 
  proof (intro allI impI, elim exE conjE)
    fix pc s l
    assume wt  : "\<forall>pc'. pc' < length all_ins \<longrightarrow> 
                        wt_instr (all_ins ! pc') G rT phi mxs (length all_ins) pc'"
    assume fits: "fits all_ins cert phi"
    assume l   : "pc < length all_ins"
    assume G   : "G \<turnstile> s <=' phi ! pc"
    assume pc  : "all_ins = l@i#ins'" "pc = length l"
    hence  i   : "all_ins ! pc = i"
      by (simp add: nth_append)

    from l wt
    have wti: "wt_instr (all_ins!pc) G rT phi mxs (length all_ins) pc" by blast

    with fits l 
    have c: "wtl_cert (all_ins!pc) G rT (phi!pc) cert mxs (length all_ins) pc \<noteq> Err"
      by - (drule wt_instr_imp_wtl_cert, auto)
    
    from Cons
    have "?C (Suc pc) ins'" by blast
    with wt fits pc
    have IH: "?len (Suc pc) \<longrightarrow> ?wtl (Suc pc) ins'" by auto

    show "wtl_inst_list (i#ins') G rT cert mxs (length all_ins) pc s \<noteq> Err" 
    proof (cases "?len (Suc pc)")
      case False
      with pc
      have "ins' = []" by simp
      with G i c fits l
      show ?thesis by (auto dest: wtl_cert_mono)
    next
      case True
      with IH
      have wtl: "?wtl (Suc pc) ins'" by blast

      from c wti fits l True
      obtain s'' where
        "wtl_cert (all_ins!pc) G rT (phi!pc) cert mxs (length all_ins) pc = OK s''"
        "G \<turnstile> s'' <=' phi ! Suc pc"
        by clarsimp (drule wt_less_wtl_cert, auto)
      moreover
      from calculation fits G l
      obtain s' where
        c': "wtl_cert (all_ins!pc) G rT s cert mxs (length all_ins) pc = OK s'" and
        "G \<turnstile> s' <=' s''"
        by - (drule wtl_cert_mono, auto)
      ultimately
      have G': "G \<turnstile> s' <=' phi ! Suc pc" 
        by - (rule sup_state_opt_trans)

      with wtl
      have "wtl_inst_list ins' G rT cert mxs (length all_ins) (Suc pc) s' \<noteq> Err"
        by auto

      with i c'
      show ?thesis by auto
    qed
  qed
qed
  

lemma fits_imp_wtl_method_complete:
  "\<lbrakk> wt_method G C pTs rT mxs mxl ins phi; fits ins cert phi \<rbrakk> 
  \<Longrightarrow> wtl_method G C pTs rT mxs mxl ins cert"
by (simp add: wt_method_def wtl_method_def)
   (rule wt_imp_wtl_inst_list [rule_format, elim_format], auto simp add: wt_start_def) 


lemma wtl_method_complete:
  "wt_method G C pTs rT mxs mxl ins phi 
  \<Longrightarrow> wtl_method G C pTs rT mxs mxl ins (make_cert ins phi)"
proof -
  assume "wt_method G C pTs rT mxs mxl ins phi" 
  moreover
  have "fits ins (make_cert ins phi) phi"
    by (rule fits_make_cert)
  ultimately
  show ?thesis 
    by (rule fits_imp_wtl_method_complete)
qed


theorem wtl_complete:
  "wt_jvm_prog G Phi \<Longrightarrow> wtl_jvm_prog G (make_Cert G Phi)"
proof -
  assume wt: "wt_jvm_prog G Phi"
   
  { fix C S fs mdecls sig rT code
    assume "(C,S,fs,mdecls) \<in> set G" "(sig,rT,code) \<in> set mdecls"
    moreover
    from wt obtain wf_mb where "wf_prog wf_mb G" 
      by (blast dest: wt_jvm_progD)
    ultimately
    have "method (G,C) sig = Some (C,rT,code)"
      by (simp add: methd)
  } note this [simp]
 
  from wt
  show ?thesis
    apply (clarsimp simp add: wt_jvm_prog_def wtl_jvm_prog_def wf_prog_def wf_cdecl_def)
    apply (drule bspec, assumption)
    apply (clarsimp simp add: wf_mdecl_def)
    apply (drule bspec, assumption)
    apply (clarsimp simp add: make_Cert_def)
    apply (clarsimp dest!: wtl_method_complete)    
    done

qed   
      
lemmas [simp] = split_paired_Ex

end
