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
     map (\<lambda>pc. if is_target step phi pc then phi!pc else None) [0..length phi(] @ [None]"

  
lemmas [simp del] = split_paired_Ex

lemma make_cert_target:
  "\<lbrakk> pc < length phi; is_target step phi pc \<rbrakk> \<Longrightarrow> make_cert step phi ! pc = phi!pc"
  by (simp add: make_cert_def nth_append)

lemma make_cert_approx:
  "\<lbrakk> pc < length phi; make_cert step phi ! pc \<noteq> phi!pc \<rbrakk> \<Longrightarrow> 
   make_cert step phi ! pc = None"
  by (auto simp add: make_cert_def nth_append)

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
  "\<lbrakk> fits step cert phi; (pc',s') \<in> set (step pc (OK (phi!pc)));
      pc' \<noteq> pc+1; pc < length phi; pc' < length phi \<rbrakk>
  \<Longrightarrow> cert!pc' = phi!pc'"
  by (auto simp add: fits_def contains_targets_def)

lemma fitsD2:
   "\<lbrakk> fits step cert phi; pc < length phi; cert!pc = Some s \<rbrakk>
  \<Longrightarrow> cert!pc = phi!pc"
  by (auto simp add: fits_def)


lemma merge_mono:
  assumes merge: "merge cert f r pc ss1 x = OK s1"
  assumes less:  "ss2 <=|Err.le (Opt.le r)| ss1"
  assumes esl:   "err_semilat (A, r, f)"
  assumes x:     "x \<in> err (opt A)"
  assumes ss1:   "\<forall>(pc', s')\<in>set ss1. s' \<in> err (opt A)"
  assumes ss2:   "\<forall>(pc', s')\<in>set ss2. s' \<in> err (opt A)"
  shows "\<exists>s2. merge cert f r pc ss2 x = s2 \<and> s2 \<le>|r (OK s1)"
proof-
  from esl have eosl: "err_semilat (opt A, Opt.le r, Opt.sup f)" 
    by - (drule semilat_opt, simp add: Opt.esl_def)
  hence order: "order (Opt.le r)" ..
  from esl x ss1 have "merge cert f r pc ss1 x =
    (if \<forall>(pc', s')\<in>set ss1. pc' \<noteq> pc + 1 \<longrightarrow> s' \<le>|r (OK (cert!pc'))
    then (map snd [(p', t')\<in>ss1 . p'=pc+1]) ++|f x
    else Err)" 
    by (rule merge_def)
  with merge obtain
    app: "\<forall>(pc',s')\<in>set ss1. pc' \<noteq> pc+1 \<longrightarrow> s' \<le>|r (OK (cert!pc'))" 
         (is "?app ss1") and
    sum: "(map snd [(p',t')\<in>ss1 . p' = pc+1] ++|f x) = OK s1" 
         (is "?map ss1 ++|f x = _" is "?sum ss1 = _")
    by (simp split: split_if_asm)
  from app less
  have "?app ss2" 
    apply clarify 
    apply (drule lesub_step_typeD, assumption) 
    apply clarify
    apply (drule bspec, assumption)
    apply clarify
    apply (drule order_trans [OF order], assumption)
    apply blast
    done
  moreover {
    have "set (?map ss1) \<subseteq> snd`(set ss1)" by auto
    also from ss1 have "snd`(set ss1) \<subseteq> err (opt A)" by auto
    finally have map1: "set (?map ss1) \<subseteq> err (opt A)" . 
    with eosl x have "?sum ss1 \<in> err (opt A)" 
      by (auto intro!: plusplus_closed simp add: Err.sl_def)
    with sum have "OK s1 \<in> err (opt A)" by simp
    moreover    
    have mapD: "\<And>x ss. x \<in> set (?map ss) \<Longrightarrow> \<exists>p. (p,x) \<in> set ss \<and> p=pc+1" by auto
    from eosl x map1 
    have "\<forall>x \<in> set (?map ss1). x \<le>|r (?sum ss1)" 
      by clarify (rule ub1, simp add: Err.sl_def)
    with sum have "\<forall>x \<in> set (?map ss1). x \<le>|r (OK s1)" by simp
    with less have "\<forall>x \<in> set (?map ss2). x \<le>|r (OK s1)"
      apply clarify
      apply (drule mapD)
      apply clarify
      apply (drule lesub_step_typeD, assumption)
      apply clarify
      apply simp
      apply (erule allE, erule impE, assumption)
      apply clarify
      apply simp
      apply (rule order_trans [OF order],assumption+)
      done
    moreover 
    from eosl map1 x have "x \<le>|r (?sum ss1)" 
      by - (rule ub2, simp add: Err.sl_def)
    with sum have "x \<le>|r (OK s1)" by simp
    moreover {
      have "set (?map ss2) \<subseteq> snd`(set ss2)" by auto
      also from ss2 have "snd`(set ss2) \<subseteq> err (opt A)" by auto
      finally have "set (?map ss2) \<subseteq> err (opt A)" . }
    ultimately
    have "?sum ss2 \<le>|r (OK s1)" using eosl x
      by - (rule lub, simp add: Err.sl_def)
    also obtain s2 where sum2: "?sum ss2 = s2" by blast
    finally have "s2 \<le>|r (OK s1)" . 
    with sum2 have "\<exists>s2. ?sum ss2 = s2 \<and> s2 \<le>|r (OK s1)" by blast
  }
  moreover
  from esl x ss2 have 
    "merge cert f r pc ss2 x =
    (if \<forall>(pc', s')\<in>set ss2. pc' \<noteq> pc + 1 \<longrightarrow> s' \<le>|r (OK (cert!pc'))
    then map snd [(p', t')\<in>ss2 . p' = pc + 1] ++|f x
    else Err)" 
    by (rule merge_def)
  ultimately show ?thesis by simp
qed


lemma wtl_inst_mono:
  assumes wtl:  "wtl_inst cert f r step pc s1 = OK s1'"
  assumes less: "OK s2 \<le>|r (OK s1)"
  assumes pc:   "pc < n" 
  assumes s1:   "s1 \<in> opt A"
  assumes s2:   "s2 \<in> opt A"
  assumes esl:  "err_semilat (A,r,f)"
  assumes cert: "cert_ok cert n A"
  assumes mono: "mono (Err.le (Opt.le r)) step n (err (opt A))"
  assumes pres: "pres_type step n (err (opt A))" 
  shows "\<exists>s2'. wtl_inst cert f r step pc s2 = OK s2' \<and> OK s2' \<le>|r (OK s1')"
proof -
  let "?step s1" = "step pc (OK s1)"
  let ?cert = "OK (cert!Suc pc)"
  from wtl 
  have "merge cert f r pc (?step s1) ?cert = OK s1'" by (simp add: wtl_inst_def)
  moreover
  have s2: "OK s2 \<in> err (opt A)" by simp
  with mono have "?step s2 <=|Err.le (Opt.le r)| ?step s1" by - (rule monoD)
  moreover note esl
  moreover
  from pc cert have "?cert \<in> err (opt A)" by (simp add: cert_okD3)
  moreover
  have s1: "OK s1 \<in> err (opt A)" by simp
  with pres pc
  have "\<forall>(pc', s')\<in>set (?step s1). s' \<in> err (opt A)"
    by (blast intro: pres_typeD)  
  moreover
  from pres s2 pc
  have "\<forall>(pc', s')\<in>set (?step s2). s' \<in> err (opt A)" 
    by (blast intro: pres_typeD)  
  ultimately
  obtain s2' where "merge cert f r pc (?step s2) ?cert = s2' \<and> s2' \<le>|r (OK s1')"
    by (blast dest: merge_mono)
  thus ?thesis by (simp add: wtl_inst_def)
qed 

lemma wtl_cert_mono:
  assumes wtl:  "wtl_cert cert f r step pc s1 = OK s1'"
  assumes less: "OK s2 \<le>|r (OK s1)"
  assumes pc:   "pc < n" 
  assumes s1:   "s1 \<in> opt A"
  assumes s2:   "s2 \<in> opt A"
  assumes esl:  "err_semilat (A,r,f)"
  assumes cert: "cert_ok cert n A"
  assumes mono: "mono (Err.le (Opt.le r)) step n (err (opt A))"
  assumes pres: "pres_type step n (err (opt A))" 
  shows "\<exists>s2'. wtl_cert cert f r step pc s2 = OK s2' \<and> OK s2' \<le>|r (OK s1')"
proof (cases "cert!pc")
  case None
  with wtl have "wtl_inst cert f r step pc s1 = OK s1'" 
    by (simp add: wtl_cert_def)
  hence "\<exists>s2'. wtl_inst cert f r step pc s2 = OK s2' \<and> OK s2' \<le>|r (OK s1')"
    by - (rule wtl_inst_mono)
  with None show ?thesis by (simp add: wtl_cert_def)
next
  case (Some s')
  with wtl obtain 
    wti: "wtl_inst cert f r step pc (Some s') = OK s1'" and
    s':  "OK s1 \<le>|r OK (Some s')"
    by (auto simp add: wtl_cert_def split: split_if_asm)
  from esl have order: "order (Opt.le r)" by simp
  hence "order (Err.le (Opt.le r))" by simp
  with less s' have "OK s2 \<le>|r OK (Some s')" by - (drule order_trans)
  with Some wti order show ?thesis by (simp add: wtl_cert_def)
qed


lemma stable_wtl:
  assumes stable:  "stable (Err.le (Opt.le r)) step (map OK phi) pc"
  assumes fits:    "fits step cert phi"  
  assumes pc:      "pc < length phi"
  assumes bounded: "bounded step (length phi)"
  assumes esl:     "err_semilat (A, r, f)"
  assumes cert_ok: "cert_ok cert (length phi) A"
  assumes phi_ok:  "\<forall>pc < length phi. phi!pc \<in> opt A"
  assumes pres:    "pres_type step (length phi) (err (opt A))" 
  shows "wtl_inst cert f r step pc (phi!pc) \<noteq> Err"
proof -
  from esl have order: "order (Opt.le r)" by simp

  let ?step = "step pc (OK (phi!pc))"
  from pc have [simp]: "map OK phi ! pc = OK (phi!pc)" by simp
  from stable 
  have less: "\<forall>(q,s')\<in>set ?step. s' \<le>|r (map OK phi!q)" 
    by (simp add: stable_def)
  
  from cert_ok pc
  have cert_suc: "OK (cert!Suc pc) \<in> err (opt A)" by (auto dest: cert_okD3)
  moreover  
  from phi_ok pc
  have "OK (phi!pc) \<in> err (opt A)" by simp
  with pres pc 
  have stepA: "\<forall>(pc',s') \<in> set ?step. s' \<in> err (opt A)" 
    by (blast dest: pres_typeD)
  ultimately
  have "merge cert f r pc ?step (OK (cert!Suc pc)) =
    (if \<forall>(pc',s')\<in>set ?step. pc'\<noteq>pc+1 \<longrightarrow> s' \<le>|r (OK (cert!pc'))
    then map snd [(p',t')\<in>?step.p'=pc+1] ++|f (OK (cert!Suc pc))
    else Err)" using esl by - (rule merge_def)
  moreover {
    fix pc' s' assume s': "(pc', s') \<in> set ?step" and suc_pc: "pc' \<noteq> pc+1"
    from bounded pc s' have pc': "pc' < length phi" by (rule boundedD)
    hence [simp]: "map OK phi ! pc' = OK (phi!pc')" by simp
    with s' less have "s' \<le>|r OK (phi!pc')" by auto
    also from fits s' suc_pc pc pc' 
    have "cert!pc' = phi!pc'" by (rule fitsD)
    hence "phi!pc' = cert!pc'" ..
    finally have "s' \<le>|r (OK (cert!pc'))" .
  } hence "\<forall>(pc',s')\<in>set ?step. pc'\<noteq>pc+1 \<longrightarrow> s' \<le>|r (OK (cert!pc'))" by auto
  moreover
  from pc have "Suc pc = length phi \<or> Suc pc < length phi" by auto
  hence "(map snd [(p',t')\<in>?step.p'=pc+1] ++|f (OK (cert!Suc pc))) \<noteq> Err" 
         (is "(?map ++|f _) \<noteq> _")
  proof (rule disjE)
    assume pc': "Suc pc = length phi"
    with cert_ok have "cert!Suc pc = None" by (simp add: cert_okD2)
    moreover 
    from pc' bounded pc
    have "\<forall>(p',t')\<in>set ?step. p'\<noteq>pc+1" by clarify (drule boundedD, auto)
    hence "[(p',t')\<in>?step.p'=pc+1] = []" by (blast intro: filter_False) 
    hence "?map = []" by simp
    ultimately show ?thesis by simp
  next
    assume pc': "Suc pc < length phi"
    hence [simp]: "map OK phi ! Suc pc = OK (phi!Suc pc)" by simp
    from esl
    have "semilat (err (opt A), Err.le (Opt.le r), lift2 (Opt.sup f))"
      by (simp add: Err.sl_def)
    moreover
    from pc' phi_ok 
    have "OK (phi!Suc pc) \<in> err (opt A)" by simp
    moreover note cert_suc
    moreover from stepA 
    have "snd`(set ?step) \<subseteq> err (opt A)" by auto
    hence "set ?map \<subseteq> err (opt A)" by auto
    moreover
    have "\<And>s. s \<in> set ?map \<Longrightarrow> \<exists>t. (Suc pc, t) \<in> set ?step" by auto
    with less have "\<forall>s' \<in> set ?map. s' \<le>|r OK (phi!Suc pc)" by auto
    moreover
    from order fits pc' 
    have "OK (cert!Suc pc) \<le>|r OK (phi!Suc pc)"     
      by (cases "cert!Suc pc") (simp, blast dest: fitsD2) 
    ultimately
    have "?map ++|f OK (cert!Suc pc) \<le>|r OK (phi!Suc pc)" by (rule lub)
    thus ?thesis by auto
  qed
  ultimately
  have "merge cert f r pc ?step (OK (cert!Suc pc)) \<noteq> Err" by simp
  thus ?thesis by (simp add: wtl_inst_def)  
qed

lemma stable_cert:
  assumes stable:  "stable (Err.le (Opt.le r)) step (map OK phi) pc"
  assumes fits:    "fits step cert phi"  
  assumes pc:      "pc < length phi"
  assumes bounded: "bounded step (length phi)"
  assumes esl:     "err_semilat (A, r, f)"
  assumes cert_ok: "cert_ok cert (length phi) A"
  assumes phi_ok:  "\<forall>pc < length phi. phi!pc \<in> opt A"
  assumes pres:    "pres_type step (length phi) (err (opt A))" 
  shows "wtl_cert cert f r step pc (phi!pc) \<noteq> Err"
proof -
  have wtl: "wtl_inst cert f r step pc (phi!pc) \<noteq> Err" by (rule stable_wtl)   
  show ?thesis
  proof (cases "cert!pc")
    case None with wtl show ?thesis by (simp add: wtl_cert_def)
  next
    case (Some s)
    with pc fits have "cert!pc = phi!pc" by - (rule fitsD2)
    with Some have "phi!pc = Some s" by simp
    with Some wtl esl show ?thesis by (simp add: wtl_cert_def)
  qed
qed
  

lemma wtl_less:
  assumes stable:  "stable (Err.le (Opt.le r)) step (map OK phi) pc"
  assumes wtl:     "wtl_inst cert f r step pc (phi!pc) = OK s"
  assumes fits:    "fits step cert phi"  
  assumes suc_pc:   "Suc pc < length phi"
  assumes bounded: "bounded step (length phi)"
  assumes esl:     "err_semilat (A, r, f)"
  assumes cert_ok: "cert_ok cert (length phi) A"
  assumes phi_ok:  "\<forall>pc < length phi. phi!pc \<in> opt A"
  assumes pres:    "pres_type step (length phi) (err (opt A))" 
  shows "OK s \<le>|r OK (phi!Suc pc)"
proof -
  from esl have order: "order (Opt.le r)" by simp

  let ?step = "step pc (OK (phi!pc))"
  from suc_pc have [simp]: "map OK phi ! pc = OK (phi!pc)" by simp
  from suc_pc have [simp]: "map OK phi ! Suc pc = OK (phi!Suc pc)" by simp
  from suc_pc have pc: "pc < length phi" by simp

  from stable
  have less: "\<forall>(q,s')\<in>set ?step. s' \<le>|r (map OK phi!q)" 
    by (simp add: stable_def)
  
  from cert_ok pc
  have cert_suc: "OK (cert!Suc pc) \<in> err (opt A)" by (auto dest: cert_okD3)
  moreover  
  from phi_ok pc
  have "OK (phi!pc) \<in> err (opt A)" by simp
  with pres pc 
  have stepA: "\<forall>(pc',s') \<in> set ?step. s' \<in> err (opt A)" 
    by (blast dest: pres_typeD)
  ultimately
  have "merge cert f r pc ?step (OK (cert!Suc pc)) =
    (if \<forall>(pc',s')\<in>set ?step. pc'\<noteq>pc+1 \<longrightarrow> s' \<le>|r (OK (cert!pc'))
    then map snd [(p',t')\<in>?step.p'=pc+1] ++|f (OK (cert!Suc pc))
    else Err)" using esl by - (rule merge_def)
  with wtl have
    "OK s = (map snd [(p',t')\<in>?step.p'=pc+1] ++|f (OK (cert!Suc pc)))" 
    (is "_ = (?map ++|f _)" is "_ = ?sum")
    by (simp add: wtl_inst_def split: split_if_asm)
  also {
    from esl
    have "semilat (err (opt A), Err.le (Opt.le r), lift2 (Opt.sup f))"
      by (simp add: Err.sl_def)
    moreover
    from suc_pc phi_ok 
    have "OK (phi!Suc pc) \<in> err (opt A)" by simp
    moreover note cert_suc
    moreover from stepA 
    have "snd`(set ?step) \<subseteq> err (opt A)" by auto
    hence "set ?map \<subseteq> err (opt A)" by auto
    moreover
    have "\<And>s. s \<in> set ?map \<Longrightarrow> \<exists>t. (Suc pc, t) \<in> set ?step" by auto
    with less have "\<forall>s' \<in> set ?map. s' \<le>|r OK (phi!Suc pc)" by auto
    moreover
    from order fits suc_pc
    have "OK (cert!Suc pc) \<le>|r OK (phi!Suc pc)"     
      by (cases "cert!Suc pc") (simp, blast dest: fitsD2) 
    ultimately
    have "?sum \<le>|r OK (phi!Suc pc)" by (rule lub)
  }
  finally show ?thesis .
qed


lemma cert_less:
  assumes stable:  "stable (Err.le (Opt.le r)) step (map OK phi) pc"
  assumes cert:    "wtl_cert cert f r step pc (phi!pc) = OK s"
  assumes fits:    "fits step cert phi"  
  assumes suc_pc:   "Suc pc < length phi"
  assumes bounded: "bounded step (length phi)"
  assumes esl:     "err_semilat (A, r, f)"
  assumes cert_ok: "cert_ok cert (length phi) A"
  assumes phi_ok:  "\<forall>pc < length phi. phi!pc \<in> opt A"
  assumes pres:    "pres_type step (length phi) (err (opt A))" 
  shows "OK s \<le>|r OK (phi!Suc pc)"
proof (cases "cert!pc")
  case None with cert 
  have "wtl_inst cert f r step pc (phi!pc) = OK s" by (simp add: wtl_cert_def)
  thus ?thesis by - (rule wtl_less)
next
  case (Some s') with cert 
  have "wtl_inst cert f r step pc (Some s') = OK s" 
    by (simp add: wtl_cert_def split: split_if_asm)
  also
  from suc_pc have "pc < length phi" by simp
  with fits Some have "cert!pc = phi!pc" by - (rule fitsD2)
  with Some have "Some s' = phi!pc" by simp
  finally
  have "wtl_inst cert f r step pc (phi!pc) = OK s" .
  thus ?thesis by - (rule wtl_less)
qed


  
lemma wt_step_wtl_lemma:
  assumes wt_step: "wt_step (Err.le (Opt.le r)) Err step (map OK phi)"
  assumes fits:    "fits step cert phi"  
  assumes bounded: "bounded step (length phi)"
  assumes esl:     "err_semilat (A, r, f)"
  assumes cert_ok: "cert_ok cert (length phi) A"
  assumes phi_ok:  "\<forall>pc < length phi. phi!pc \<in> opt A"
  assumes pres:    "pres_type step (length phi) (err (opt A))" 
  assumes mono:    "mono (Err.le (Opt.le r)) step (length phi) (err (opt A))"
  shows "\<And>pc s. pc+length ins = length phi \<Longrightarrow> OK s \<le>|r OK (phi!pc) \<Longrightarrow> s \<in> opt A \<Longrightarrow>
                wtl_inst_list ins cert f r step pc s \<noteq> Err"
  (is "\<And>pc s. _ \<Longrightarrow> _ \<Longrightarrow> _ \<Longrightarrow> ?wtl ins pc s \<noteq> Err")
proof (induct ins)
  fix pc s show "?wtl [] pc s \<noteq> Err" by simp
next
  fix pc s i ins
  assume "\<And>pc s. pc+length ins=length phi \<Longrightarrow> OK s \<le>|r OK (phi!pc) \<Longrightarrow> s \<in> opt A \<Longrightarrow>
                 ?wtl ins pc s \<noteq> Err"
  moreover
  assume pc_l: "pc + length (i#ins) = length phi"
  hence suc_pc_l: "Suc pc + length ins = length phi" by simp
  ultimately
  have IH: 
    "\<And>s. OK s \<le>|r OK (phi!Suc pc) \<Longrightarrow> s \<in> opt A \<Longrightarrow> ?wtl ins (Suc pc) s \<noteq> Err" .

  from pc_l obtain pc: "pc < length phi" by simp
  with wt_step 
  have stable: "stable (Err.le (Opt.le r)) step (map OK phi) pc" 
    by (simp add: wt_step_def)
  moreover
  assume s_phi: "OK s \<le>|r OK (phi!pc)"
  ultimately 
  have "wtl_cert cert f r step pc (phi!pc) \<noteq> Err" by - (rule stable_cert)
  then obtain s'' where s'': "wtl_cert cert f r step pc (phi!pc) = OK s''" by fast
  moreover 
  from phi_ok pc 
  have phi_pc: "phi!pc \<in> opt A" by simp
  moreover 
  assume s: "s \<in> opt A"
  ultimately
  obtain s' where "wtl_cert cert f r step pc s = OK s'"
    by - (drule wtl_cert_mono, assumption+, blast)
  hence "ins = [] \<Longrightarrow> ?wtl (i#ins) pc s \<noteq> Err" by simp
  moreover {
    assume "ins \<noteq> []" 
    with pc_l have suc_pc: "Suc pc < length phi" by (auto simp add: neq_Nil_conv)
    with stable s'' have "OK s'' \<le>|r OK (phi!Suc pc)" by - (rule cert_less)
    moreover
    from s'' s_phi obtain s' where 
      cert: "wtl_cert cert f r step pc s = OK s'" and
      "OK s' \<le>|r OK s''"
      using phi_pc
      by - (drule wtl_cert_mono, assumption+, blast)
    moreover from esl have "order (Err.le (Opt.le r))" by simp
    ultimately have less: "OK s' \<le>|r OK (phi!Suc pc)" by - (rule order_trans)

    from cert_ok suc_pc have "cert!pc \<in> opt A" and "cert!(pc+1) \<in> opt A" 
      by (auto simp add: cert_ok_def)
    with s cert pres have "s' \<in> opt A" by - (rule wtl_cert_pres) 

    with less IH have "?wtl ins (Suc pc) s' \<noteq> Err" by blast
    with cert have "?wtl (i#ins) pc s \<noteq> Err" by simp 
  }
  ultimately show "?wtl (i#ins) pc s \<noteq> Err" by (cases ins) auto 
qed


theorem wtl_complete:
  assumes "wt_step (Err.le (Opt.le r)) Err step (map OK phi)"
  assumes "OK s \<le>|r OK (phi!0)" and "s \<in> opt A"
  defines cert:  "cert \<equiv> make_cert step phi"

  assumes "bounded step (length phi)" and "err_semilat (A, r, f)"
  assumes "pres_type step (length phi) (err (opt A))" 
  assumes "mono (Err.le (Opt.le r)) step (length phi) (err (opt A))"
  assumes "length ins = length phi"
  assumes phi_ok:  "\<forall>pc < length phi. phi!pc \<in> opt A"

  shows "wtl_inst_list ins cert f r step 0 s \<noteq> Err"
proof -
  have "0+length ins = length phi" by simp
  moreover
  have "fits step cert phi" by (unfold cert) (rule fits_make_cert)
  moreover
  from phi_ok have "cert_ok cert (length phi) A"
    by (simp add: cert make_cert_def cert_ok_def nth_append)
  ultimately
  show ?thesis by - (rule wt_step_wtl_lemma)
qed


end
