(*
    ID:         $Id$
    Author:     Gerwin Klein
    Copyright   1999 Technische Universitaet Muenchen
*)

header {* \isaheader{Correctness of the LBV} *}

theory LBVCorrect = LBVSpec + Typing_Framework:

locale lbvc = lbv +
  fixes s0  :: 'a
  fixes c   :: "'a list"
  fixes ins :: "'b list"
  fixes phi :: "'a list" ("\<phi>")
  defines phi_def:
  "\<phi> \<equiv>  map (\<lambda>pc. if c!pc = \<bottom> then wtl (take pc ins) c 0 s0 else c!pc) 
        [0..length ins(]"


lemma (in lbvc) phi_None [intro?]:
  "\<lbrakk> pc < length ins; c!pc = \<bottom> \<rbrakk> \<Longrightarrow> \<phi> ! pc = wtl (take pc ins) c 0 s0"
  by (simp add: phi_def)

lemma (in lbvc) phi_Some [intro?]:
  "\<lbrakk> pc < length ins; c!pc \<noteq> \<bottom> \<rbrakk> \<Longrightarrow> \<phi> ! pc = c ! pc"
  by (simp add: phi_def)

lemma (in lbvc) phi_len [simp]:
  "length \<phi> = length ins"
  by (simp add: phi_def)


lemma (in lbvc) wtl_suc_pc:
  assumes all: "wtl ins c 0 s0 \<noteq> \<top>" 
  assumes pc:  "pc+1 < length ins"
  shows "wtl (take (pc+1) ins) c 0 s0 <=_r \<phi>!(pc+1)"
proof -
  from all pc
  have "wtc c (pc+1) (wtl (take (pc+1) ins) c 0 s0) \<noteq> T" by (rule wtl_all)
  with pc show ?thesis by (simp add: phi_def wtc split: split_if_asm)
qed


lemma (in lbvc) wtl_stable:
  assumes
    pres:    "pres_type step (length ins) A" and
    s0_in_A: "s0 \<in> A" and
    cert_ok: "cert_ok c (length ins) \<top> \<bottom> A" and
    wtl:     "wtl ins c 0 s0 \<noteq> \<top>" and
    pc:      "pc < length ins" and
    bounded: "bounded step (length ins)"
  shows "stable r step \<phi> pc"
proof (unfold stable_def, clarify)
  fix pc' s' assume step: "(pc',s') \<in> set (step pc (\<phi> ! pc))" 
                      (is "(pc',s') \<in> set (?step pc)")
  
  from step pc bounded have pc': "pc' < length ins"
    by (unfold bounded_def) blast

  have tkpc: "wtl (take pc ins) c 0 s0 \<noteq> \<top>" (is "?s1 \<noteq> _") by (rule wtl_take)
  have s2: "wtl (take (pc+1) ins) c 0 s0 \<noteq> \<top>" (is "?s2 \<noteq> _") by (rule wtl_take)
  
  from wtl pc have cert: "wtc c pc ?s1 \<noteq> \<top>" by (rule wtl_all)

  have c_Some: "\<forall>pc t. pc < length ins \<longrightarrow> c!pc \<noteq> \<bottom> \<longrightarrow> \<phi>!pc = c!pc" 
    by (simp add: phi_def)
  have c_None: "c!pc = \<bottom> \<Longrightarrow> \<phi>!pc = ?s1" ..

  from cert pc c_None c_Some
  have inst: "wtc c pc ?s1  = wti c pc (\<phi>!pc)"
    by (simp add: wtc split: split_if_asm)

  have "?s1 \<in> A" by (rule wtl_pres) 
  with pc c_Some cert_ok c_None
  have "\<phi>!pc \<in> A" by (cases "c!pc = \<bottom>") (auto dest: cert_okD1)
  with pc pres
  have step_in_A: "snd`set (?step pc) \<subseteq> A" by (auto dest: pres_typeD2)

  show "s' <=_r \<phi>!pc'" 
  proof (cases "pc' = pc+1")
    case True
    with pc' cert_ok
    have cert_in_A: "c!(pc+1) \<in> A" by (auto dest: cert_okD1)
    from True pc' have pc1: "pc+1 < length ins" by simp
    with tkpc have "?s2 = wtc c pc ?s1" by - (rule wtl_Suc)
    with inst 
    have merge: "?s2 = merge c pc (?step pc) (c!(pc+1))" by (simp add: wti)
    also    
    from s2 merge have "\<dots> \<noteq> \<top>" (is "?merge \<noteq> _") by simp
    with cert_in_A step_in_A
    have "?merge = (map snd [(p',t')\<in>?step pc. p'=pc+1] ++_f (c!(pc+1)))"
      by (rule merge_not_top_s) 
    finally
    have "s' <=_r ?s2" using step_in_A cert_in_A True step 
      by (auto intro: pp_ub1')
    also 
    from wtl pc1 have "?s2 <=_r \<phi>!(pc+1)" by (rule wtl_suc_pc)
    also note True [symmetric]
    finally show ?thesis by simp    
  next
    case False
    from cert inst
    have "merge c pc (?step pc) (c!(pc+1)) \<noteq> \<top>" by (simp add: wti)
    with step_in_A
    have "\<forall>(pc', s')\<in>set (?step pc). pc'\<noteq>pc+1 \<longrightarrow> s' <=_r c!pc'" 
      by - (rule merge_not_top)
    with step False 
    have ok: "s' <=_r c!pc'" by blast
    moreover
    from ok
    have "c!pc' = \<bottom> \<Longrightarrow> s' = \<bottom>" by simp
    moreover
    from c_Some pc'
    have "c!pc' \<noteq> \<bottom> \<Longrightarrow> \<phi>!pc' = c!pc'" by auto
    ultimately
    show ?thesis by (cases "c!pc' = \<bottom>") auto 
  qed
qed

  
lemma (in lbvc) phi_not_top:
  assumes wtl: "wtl ins c 0 s0 \<noteq> \<top>"
  assumes crt: "cert_ok c (length ins) \<top> \<bottom> A"
  assumes pc: "pc < length ins"
  shows "\<phi>!pc \<noteq> \<top>"
proof (cases "c!pc = \<bottom>")
  case False with pc
  have "\<phi>!pc = c!pc" ..
  also from crt pc have "\<dots> \<noteq> \<top>" by (rule cert_okD4)
  finally show ?thesis .
next
  case True with pc
  have "\<phi>!pc = wtl (take pc ins) c 0 s0" ..
  also from wtl have "\<dots> \<noteq> \<top>" by (rule wtl_take)
  finally show ?thesis .
qed
    

theorem (in lbvc) wtl_sound:
  assumes "wtl ins c 0 s0 \<noteq> \<top>" 
  assumes "bounded step (length ins)"
  assumes "s0 \<in> A" and "cert_ok c (length ins) \<top> \<bottom> A"
  assumes "pres_type step (length ins) A"
  shows "\<exists>ts. wt_step r \<top> step ts"
proof -  
  have "wt_step r \<top> step \<phi>"
  proof (unfold wt_step_def, intro strip conjI)
    fix pc assume "pc < length \<phi>"
    then obtain "pc < length ins" by simp
    show "\<phi>!pc \<noteq> \<top>" by (rule phi_not_top)
    show "stable r step \<phi> pc" by (rule wtl_stable)
  qed    
  thus ?thesis .. 
qed

end