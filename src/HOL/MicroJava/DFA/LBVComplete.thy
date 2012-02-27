(*  Title:      HOL/MicroJava/DFA/LBVComplete.thy
    Author:     Gerwin Klein
    Copyright   2000 Technische Universitaet Muenchen
*)

header {* \isaheader{Completeness of the LBV} *}

theory LBVComplete
imports LBVSpec Typing_Framework
begin

definition is_target :: "['s step_type, 's list, nat] \<Rightarrow> bool" where 
  "is_target step phi pc' \<longleftrightarrow>
     (\<exists>pc s'. pc' \<noteq> pc+1 \<and> pc < length phi \<and> (pc',s') \<in> set (step pc (phi!pc)))"

definition make_cert :: "['s step_type, 's list, 's] \<Rightarrow> 's certificate" where
  "make_cert step phi B =
     map (\<lambda>pc. if is_target step phi pc then phi!pc else B) [0..<length phi] @ [B]"

lemma [code]:
  "is_target step phi pc' =
    list_ex (\<lambda>pc. pc' \<noteq> pc+1 \<and> List.member (map fst (step pc (phi!pc))) pc') [0..<length phi]"
by (force simp: list_ex_iff member_def is_target_def)


locale lbvc = lbv + 
  fixes phi :: "'a list" ("\<phi>")
  fixes c   :: "'a list" 
  defines cert_def: "c \<equiv> make_cert step \<phi> \<bottom>"

  assumes mono: "mono r step (length \<phi>) A"
  assumes pres: "pres_type step (length \<phi>) A" 
  assumes phi:  "\<forall>pc < length \<phi>. \<phi>!pc \<in> A \<and> \<phi>!pc \<noteq> \<top>"
  assumes bounded: "bounded step (length \<phi>)"

  assumes B_neq_T: "\<bottom> \<noteq> \<top>" 


lemma (in lbvc) cert: "cert_ok c (length \<phi>) \<top> \<bottom> A"
proof (unfold cert_ok_def, intro strip conjI)  
  note [simp] = make_cert_def cert_def nth_append 

  show "c!length \<phi> = \<bottom>" by simp

  fix pc assume pc: "pc < length \<phi>" 
  from pc phi B_A show "c!pc \<in> A" by simp
  from pc phi B_neq_T show "c!pc \<noteq> \<top>" by simp
qed

lemmas [simp del] = split_paired_Ex


lemma (in lbvc) cert_target [intro?]:
  "\<lbrakk> (pc',s') \<in> set (step pc (\<phi>!pc));
      pc' \<noteq> pc+1; pc < length \<phi>; pc' < length \<phi> \<rbrakk>
  \<Longrightarrow> c!pc' = \<phi>!pc'"
  by (auto simp add: cert_def make_cert_def nth_append is_target_def)


lemma (in lbvc) cert_approx [intro?]:
  "\<lbrakk> pc < length \<phi>; c!pc \<noteq> \<bottom> \<rbrakk>
  \<Longrightarrow> c!pc = \<phi>!pc"
  by (auto simp add: cert_def make_cert_def nth_append)


lemma (in lbv) le_top [simp, intro]:
  "x <=_r \<top>"
  by (insert top) simp
  

lemma (in lbv) merge_mono:
  assumes less:  "ss2 <=|r| ss1"
  assumes x:     "x \<in> A"
  assumes ss1:   "snd`set ss1 \<subseteq> A"
  assumes ss2:   "snd`set ss2 \<subseteq> A"
  shows "merge c pc ss2 x <=_r merge c pc ss1 x" (is "?s2 <=_r ?s1")
proof-
  have "?s1 = \<top> \<Longrightarrow> ?thesis" by simp
  moreover {
    assume merge: "?s1 \<noteq> T" 
    from x ss1 have "?s1 =
      (if \<forall>(pc', s')\<in>set ss1. pc' \<noteq> pc + 1 \<longrightarrow> s' <=_r c!pc'
      then (map snd [(p', t') \<leftarrow> ss1 . p'=pc+1]) ++_f x
      else \<top>)" 
      by (rule merge_def)  
    with merge obtain
      app: "\<forall>(pc',s')\<in>set ss1. pc' \<noteq> pc+1 \<longrightarrow> s' <=_r c!pc'" 
           (is "?app ss1") and
      sum: "(map snd [(p',t') \<leftarrow> ss1 . p' = pc+1] ++_f x) = ?s1" 
           (is "?map ss1 ++_f x = _" is "?sum ss1 = _")
      by (simp split: split_if_asm)
    from app less 
    have "?app ss2" by (blast dest: trans_r lesub_step_typeD)
    moreover {
      from ss1 have map1: "set (?map ss1) \<subseteq> A" by auto
      with x have "?sum ss1 \<in> A" by (auto intro!: plusplus_closed semilat)
      with sum have "?s1 \<in> A" by simp
      moreover    
      have mapD: "\<And>x ss. x \<in> set (?map ss) \<Longrightarrow> \<exists>p. (p,x) \<in> set ss \<and> p=pc+1" by auto
      from x map1 
      have "\<forall>x \<in> set (?map ss1). x <=_r ?sum ss1"
        by clarify (rule pp_ub1)
      with sum have "\<forall>x \<in> set (?map ss1). x <=_r ?s1" by simp
      with less have "\<forall>x \<in> set (?map ss2). x <=_r ?s1"
        by (fastforce dest!: mapD lesub_step_typeD intro: trans_r)
      moreover 
      from map1 x have "x <=_r (?sum ss1)" by (rule pp_ub2)
      with sum have "x <=_r ?s1" by simp
      moreover 
      from ss2 have "set (?map ss2) \<subseteq> A" by auto
      ultimately
      have "?sum ss2 <=_r ?s1" using x by - (rule pp_lub)
    }
    moreover
    from x ss2 have 
      "?s2 =
      (if \<forall>(pc', s')\<in>set ss2. pc' \<noteq> pc + 1 \<longrightarrow> s' <=_r c!pc'
      then map snd [(p', t') \<leftarrow> ss2 . p' = pc + 1] ++_f x
      else \<top>)" 
      by (rule merge_def)
    ultimately have ?thesis by simp
  }
  ultimately show ?thesis by (cases "?s1 = \<top>") auto
qed


lemma (in lbvc) wti_mono:
  assumes less: "s2 <=_r s1"
  assumes pc:   "pc < length \<phi>" 
  assumes s1:   "s1 \<in> A"
  assumes s2:   "s2 \<in> A"
  shows "wti c pc s2 <=_r wti c pc s1" (is "?s2' <=_r ?s1'")
proof -
  from mono pc s2 less have "step pc s2 <=|r| step pc s1" by (rule monoD)
  moreover
  from cert B_A pc have "c!Suc pc \<in> A" by (rule cert_okD3)
  moreover 
  from pres s1 pc
  have "snd`set (step pc s1) \<subseteq> A" by (rule pres_typeD2)
  moreover
  from pres s2 pc
  have "snd`set (step pc s2) \<subseteq> A" by (rule pres_typeD2)
  ultimately
  show ?thesis by (simp add: wti merge_mono)
qed 

lemma (in lbvc) wtc_mono:
  assumes less: "s2 <=_r s1"
  assumes pc:   "pc < length \<phi>" 
  assumes s1:   "s1 \<in> A"
  assumes s2:   "s2 \<in> A"
  shows "wtc c pc s2 <=_r wtc c pc s1" (is "?s2' <=_r ?s1'")
proof (cases "c!pc = \<bottom>")
  case True 
  moreover from less pc s1 s2 have "wti c pc s2 <=_r wti c pc s1" by (rule wti_mono)
  ultimately show ?thesis by (simp add: wtc)
next
  case False
  have "?s1' = \<top> \<Longrightarrow> ?thesis" by simp
  moreover {
    assume "?s1' \<noteq> \<top>" 
    with False have c: "s1 <=_r c!pc" by (simp add: wtc split: split_if_asm)
    with less have "s2 <=_r c!pc" ..
    with False c have ?thesis by (simp add: wtc)
  }
  ultimately show ?thesis by (cases "?s1' = \<top>") auto
qed


lemma (in lbv) top_le_conv [simp]:
  "\<top> <=_r x = (x = \<top>)"
  using semilat by (simp add: top) 

lemma (in lbv) neq_top [simp, elim]:
  "\<lbrakk> x <=_r y; y \<noteq> \<top> \<rbrakk> \<Longrightarrow> x \<noteq> \<top>"
  by (cases "x = T") auto


lemma (in lbvc) stable_wti:
  assumes stable:  "stable r step \<phi> pc"
  assumes pc:      "pc < length \<phi>"
  shows "wti c pc (\<phi>!pc) \<noteq> \<top>"
proof -
  let ?step = "step pc (\<phi>!pc)"
  from stable 
  have less: "\<forall>(q,s')\<in>set ?step. s' <=_r \<phi>!q" by (simp add: stable_def)
  
  from cert B_A pc 
  have cert_suc: "c!Suc pc \<in> A" by (rule cert_okD3)
  moreover  
  from phi pc have "\<phi>!pc \<in> A" by simp
  from pres this pc 
  have stepA: "snd`set ?step \<subseteq> A" by (rule pres_typeD2) 
  ultimately
  have "merge c pc ?step (c!Suc pc) =
    (if \<forall>(pc',s')\<in>set ?step. pc'\<noteq>pc+1 \<longrightarrow> s' <=_r c!pc'
    then map snd [(p',t') \<leftarrow> ?step.p'=pc+1] ++_f c!Suc pc
    else \<top>)" unfolding mrg_def by (rule lbv.merge_def [OF lbvc.axioms(1), OF lbvc_axioms])
  moreover {
    fix pc' s' assume s': "(pc', s') \<in> set ?step" and suc_pc: "pc' \<noteq> pc+1"
    with less have "s' <=_r \<phi>!pc'" by auto
    also 
    from bounded pc s' have "pc' < length \<phi>" by (rule boundedD)
    with s' suc_pc pc have "c!pc' = \<phi>!pc'" ..
    hence "\<phi>!pc' = c!pc'" ..
    finally have "s' <=_r c!pc'" .
  } hence "\<forall>(pc',s')\<in>set ?step. pc'\<noteq>pc+1 \<longrightarrow> s' <=_r c!pc'" by auto
  moreover
  from pc have "Suc pc = length \<phi> \<or> Suc pc < length \<phi>" by auto
  hence "map snd [(p',t') \<leftarrow> ?step.p'=pc+1] ++_f c!Suc pc \<noteq> \<top>" 
         (is "?map ++_f _ \<noteq> _")
  proof (rule disjE)
    assume pc': "Suc pc = length \<phi>"
    with cert have "c!Suc pc = \<bottom>" by (simp add: cert_okD2)
    moreover 
    from pc' bounded pc 
    have "\<forall>(p',t')\<in>set ?step. p'\<noteq>pc+1" by clarify (drule boundedD, auto)
    hence "[(p',t') \<leftarrow> ?step.p'=pc+1] = []" by (blast intro: filter_False) 
    hence "?map = []" by simp
    ultimately show ?thesis by (simp add: B_neq_T)  
  next
    assume pc': "Suc pc < length \<phi>"
    from pc' phi have "\<phi>!Suc pc \<in> A" by simp
    moreover note cert_suc
    moreover from stepA 
    have "set ?map \<subseteq> A" by auto
    moreover
    have "\<And>s. s \<in> set ?map \<Longrightarrow> \<exists>t. (Suc pc, t) \<in> set ?step" by auto
    with less have "\<forall>s' \<in> set ?map. s' <=_r \<phi>!Suc pc" by auto
    moreover
    from pc' have "c!Suc pc <=_r \<phi>!Suc pc" 
      by (cases "c!Suc pc = \<bottom>") (auto dest: cert_approx)
    ultimately
    have "?map ++_f c!Suc pc <=_r \<phi>!Suc pc" by (rule pp_lub)
    moreover
    from pc' phi have "\<phi>!Suc pc \<noteq> \<top>" by simp
    ultimately
    show ?thesis by auto
  qed
  ultimately
  have "merge c pc ?step (c!Suc pc) \<noteq> \<top>" by simp
  thus ?thesis by (simp add: wti)  
qed

lemma (in lbvc) wti_less:
  assumes stable:  "stable r step \<phi> pc"
  assumes suc_pc:   "Suc pc < length \<phi>"
  shows "wti c pc (\<phi>!pc) <=_r \<phi>!Suc pc" (is "?wti <=_r _")
proof -
  let ?step = "step pc (\<phi>!pc)"

  from stable 
  have less: "\<forall>(q,s')\<in>set ?step. s' <=_r \<phi>!q" by (simp add: stable_def)
   
  from suc_pc have pc: "pc < length \<phi>" by simp
  with cert B_A have cert_suc: "c!Suc pc \<in> A" by (rule cert_okD3)
  moreover  
  from phi pc have "\<phi>!pc \<in> A" by simp
  with pres pc have stepA: "snd`set ?step \<subseteq> A" by - (rule pres_typeD2)
  moreover
  from stable pc have "?wti \<noteq> \<top>" by (rule stable_wti)
  hence "merge c pc ?step (c!Suc pc) \<noteq> \<top>" by (simp add: wti)
  ultimately
  have "merge c pc ?step (c!Suc pc) =
    map snd [(p',t')\<leftarrow> ?step.p'=pc+1] ++_f c!Suc pc" by (rule merge_not_top_s) 
  hence "?wti = \<dots>" (is "_ = (?map ++_f _)" is "_ = ?sum") by (simp add: wti)
  also {
    from suc_pc phi have "\<phi>!Suc pc \<in> A" by simp
    moreover note cert_suc
    moreover from stepA have "set ?map \<subseteq> A" by auto
    moreover
    have "\<And>s. s \<in> set ?map \<Longrightarrow> \<exists>t. (Suc pc, t) \<in> set ?step" by auto
    with less have "\<forall>s' \<in> set ?map. s' <=_r \<phi>!Suc pc" by auto
    moreover
    from suc_pc have "c!Suc pc <=_r \<phi>!Suc pc"
      by (cases "c!Suc pc = \<bottom>") (auto dest: cert_approx)
    ultimately
    have "?sum <=_r \<phi>!Suc pc" by (rule pp_lub)
  }
  finally show ?thesis .
qed

lemma (in lbvc) stable_wtc:
  assumes stable:  "stable r step phi pc"
  assumes pc:      "pc < length \<phi>"
  shows "wtc c pc (\<phi>!pc) \<noteq> \<top>"
proof -
  from stable pc have wti: "wti c pc (\<phi>!pc) \<noteq> \<top>" by (rule stable_wti)
  show ?thesis
  proof (cases "c!pc = \<bottom>")
    case True with wti show ?thesis by (simp add: wtc)
  next
    case False
    with pc have "c!pc = \<phi>!pc" ..    
    with False wti show ?thesis by (simp add: wtc)
  qed
qed

lemma (in lbvc) wtc_less:
  assumes stable: "stable r step \<phi> pc"
  assumes suc_pc: "Suc pc < length \<phi>"
  shows "wtc c pc (\<phi>!pc) <=_r \<phi>!Suc pc" (is "?wtc <=_r _")
proof (cases "c!pc = \<bottom>")
  case True
  moreover from stable suc_pc have "wti c pc (\<phi>!pc) <=_r \<phi>!Suc pc"
    by (rule wti_less)
  ultimately show ?thesis by (simp add: wtc)
next
  case False
  from suc_pc have pc: "pc < length \<phi>" by simp
  with stable have "?wtc \<noteq> \<top>" by (rule stable_wtc)
  with False have "?wtc = wti c pc (c!pc)" 
    by (unfold wtc) (simp split: split_if_asm)
  also from pc False have "c!pc = \<phi>!pc" .. 
  finally have "?wtc = wti c pc (\<phi>!pc)" .
  also from stable suc_pc have "wti c pc (\<phi>!pc) <=_r \<phi>!Suc pc" by (rule wti_less)
  finally show ?thesis .
qed


lemma (in lbvc) wt_step_wtl_lemma:
  assumes wt_step: "wt_step r \<top> step \<phi>"
  shows "\<And>pc s. pc+length ls = length \<phi> \<Longrightarrow> s <=_r \<phi>!pc \<Longrightarrow> s \<in> A \<Longrightarrow> s\<noteq>\<top> \<Longrightarrow>
                wtl ls c pc s \<noteq> \<top>"
  (is "\<And>pc s. _ \<Longrightarrow> _ \<Longrightarrow> _ \<Longrightarrow> _ \<Longrightarrow> ?wtl ls pc s \<noteq> _")
proof (induct ls)
  fix pc s assume "s\<noteq>\<top>" thus "?wtl [] pc s \<noteq> \<top>" by simp
next
  fix pc s i ls
  assume "\<And>pc s. pc+length ls=length \<phi> \<Longrightarrow> s <=_r \<phi>!pc \<Longrightarrow> s \<in> A \<Longrightarrow> s\<noteq>\<top> \<Longrightarrow> 
                  ?wtl ls pc s \<noteq> \<top>"
  moreover
  assume pc_l: "pc + length (i#ls) = length \<phi>"
  hence suc_pc_l: "Suc pc + length ls = length \<phi>" by simp
  ultimately
  have IH: "\<And>s. s <=_r \<phi>!Suc pc \<Longrightarrow> s \<in> A \<Longrightarrow> s \<noteq> \<top> \<Longrightarrow> ?wtl ls (Suc pc) s \<noteq> \<top>" .

  from pc_l obtain pc: "pc < length \<phi>" by simp
  with wt_step have stable: "stable r step \<phi> pc" by (simp add: wt_step_def)
  from this pc have wt_phi: "wtc c pc (\<phi>!pc) \<noteq> \<top>" by (rule stable_wtc)
  assume s_phi: "s <=_r \<phi>!pc"
  from phi pc have phi_pc: "\<phi>!pc \<in> A" by simp
  assume s: "s \<in> A"
  with s_phi pc phi_pc have wt_s_phi: "wtc c pc s <=_r wtc c pc (\<phi>!pc)" by (rule wtc_mono)
  with wt_phi have wt_s: "wtc c pc s \<noteq> \<top>" by simp
  moreover
  assume s': "s \<noteq> \<top>" 
  ultimately
  have "ls = [] \<Longrightarrow> ?wtl (i#ls) pc s \<noteq> \<top>" by simp
  moreover {
    assume "ls \<noteq> []" 
    with pc_l have suc_pc: "Suc pc < length \<phi>" by (auto simp add: neq_Nil_conv)
    with stable have "wtc c pc (phi!pc) <=_r \<phi>!Suc pc" by (rule wtc_less)
    with wt_s_phi have "wtc c pc s <=_r \<phi>!Suc pc" by (rule trans_r)      
    moreover
    from cert suc_pc have "c!pc \<in> A" "c!(pc+1) \<in> A" 
      by (auto simp add: cert_ok_def)
    from pres this s pc have "wtc c pc s \<in> A" by (rule wtc_pres)
    ultimately
    have "?wtl ls (Suc pc) (wtc c pc s) \<noteq> \<top>" using IH wt_s by blast
    with s' wt_s have "?wtl (i#ls) pc s \<noteq> \<top>" by simp
  }
  ultimately show "?wtl (i#ls) pc s \<noteq> \<top>" by (cases ls) blast+
qed

  
theorem (in lbvc) wtl_complete:
  assumes wt: "wt_step r \<top> step \<phi>"
    and s: "s <=_r \<phi>!0" "s \<in> A" "s \<noteq> \<top>"
    and len: "length ins = length phi"
  shows "wtl ins c 0 s \<noteq> \<top>"
proof -
  from len have "0+length ins = length phi" by simp
  from wt this s show ?thesis by (rule wt_step_wtl_lemma)
qed

end
