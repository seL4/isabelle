(*  Title:      HOL/MicroJava/BV/JVM.thy
    ID:         $Id$
    Author:     Tobias Nipkow, Gerwin Klein
    Copyright   2000 TUM
*)

header {* \isaheader{The Typing Framework for the JVM}\label{sec:JVM} *}

theory Typing_Framework_JVM = Typing_Framework_err + JVMType + EffectMono + BVSpec:


constdefs
  exec :: "jvm_prog \<Rightarrow> nat \<Rightarrow> ty \<Rightarrow> exception_table \<Rightarrow> instr list \<Rightarrow> state step_type"
  "exec G maxs rT et bs == 
  err_step (size bs) (\<lambda>pc. app (bs!pc) G maxs rT pc et) (\<lambda>pc. eff (bs!pc) G pc et)"

constdefs
  opt_states :: "'c prog \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> (ty list \<times> ty err list) option set"
  "opt_states G maxs maxr \<equiv> opt (\<Union>{list n (types G) |n. n \<le> maxs} \<times> list maxr (err (types G)))"


section {*  Executability of @{term check_bounded} *}
consts
  list_all'_rec :: "('a \<Rightarrow> nat \<Rightarrow> bool) \<Rightarrow> nat \<Rightarrow> 'a list \<Rightarrow> bool"
primrec
  "list_all'_rec P n []     = True"
  "list_all'_rec P n (x#xs) = (P x n \<and> list_all'_rec P (Suc n) xs)"

constdefs
  list_all' :: "('a \<Rightarrow> nat \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> bool"
  "list_all' P xs \<equiv> list_all'_rec P 0 xs"

lemma list_all'_rec:
  "\<And>n. list_all'_rec P n xs = (\<forall>p < size xs. P (xs!p) (p+n))"
  apply (induct xs)
  apply auto
  apply (case_tac p)
  apply auto
  done

lemma list_all' [iff]:
  "list_all' P xs = (\<forall>n < size xs. P (xs!n) n)"
  by (unfold list_all'_def) (simp add: list_all'_rec)

lemma list_all_ball:
  "list_all P xs = (\<forall>x \<in> set xs. P x)"
  by (induct xs) auto

lemma [code]:
  "check_bounded ins et = 
  (list_all' (\<lambda>i pc. list_all (\<lambda>pc'. pc' < length ins) (succs i pc)) ins \<and> 
   list_all (\<lambda>e. fst (snd (snd e)) < length ins) et)"
  by (simp add: list_all_ball check_bounded_def)
  

section {* Connecting JVM and Framework *}

lemma check_bounded_is_bounded:
  "check_bounded ins et \<Longrightarrow> bounded (\<lambda>pc. eff (ins!pc) G pc et) (length ins)"  
  by (unfold bounded_def) (blast dest: check_boundedD)

lemma special_ex_swap_lemma [iff]: 
  "(? X. (? n. X = A n & P n) & Q X) = (? n. Q(A n) & P n)"
  by blast

lemmas [iff del] = not_None_eq

theorem exec_pres_type:
  "wf_prog wf_mb S \<Longrightarrow> 
  pres_type (exec S maxs rT et bs) (size bs) (states S maxs maxr)"
  apply (unfold exec_def JVM_states_unfold)
  apply (rule pres_type_lift)
  apply clarify
  apply (case_tac s)
   apply simp
   apply (drule effNone)
   apply simp  
  apply (simp add: eff_def xcpt_eff_def norm_eff_def)
  apply (case_tac "bs!p")

  apply (clarsimp simp add: not_Err_eq)
  apply (drule listE_nth_in, assumption)
  apply fastsimp

  apply (fastsimp simp add: not_None_eq)

  apply (fastsimp simp add: not_None_eq typeof_empty_is_type)

  apply clarsimp
  apply (erule disjE)
   apply fastsimp
  apply clarsimp
  apply (rule_tac x="1" in exI)
  apply fastsimp

  apply clarsimp
  apply (erule disjE)
   apply (fastsimp dest: field_fields fields_is_type)
  apply (simp add: match_some_entry split: split_if_asm)
  apply (rule_tac x=1 in exI)
  apply fastsimp

  apply clarsimp
  apply (erule disjE)
   apply fastsimp
  apply (simp add: match_some_entry split: split_if_asm)
  apply (rule_tac x=1 in exI)
  apply fastsimp

  apply clarsimp
  apply (erule disjE)
   apply fastsimp
  apply clarsimp
  apply (rule_tac x=1 in exI)
  apply fastsimp

  defer 

  apply fastsimp
  apply fastsimp

  apply clarsimp
  apply (rule_tac x="n'+2" in exI)  
  apply simp

  apply clarsimp
  apply (rule_tac x="Suc (Suc (Suc (length ST)))" in exI)  
  apply simp

  apply clarsimp
  apply (rule_tac x="Suc (Suc (Suc (Suc (length ST))))" in exI)  
  apply simp

  apply fastsimp
  apply fastsimp
  apply fastsimp
  apply fastsimp

  apply clarsimp
  apply (erule disjE)
   apply fastsimp
  apply clarsimp
  apply (rule_tac x=1 in exI)
  apply fastsimp
  
  apply (erule disjE)
   apply (clarsimp simp add: Un_subset_iff)  
   apply (drule method_wf_mdecl, assumption+)
   apply (clarsimp simp add: wf_mdecl_def wf_mhead_def)
   apply fastsimp
  apply clarsimp
  apply (rule_tac x=1 in exI)
  apply fastsimp
  done

lemmas [iff] = not_None_eq

lemma sup_state_opt_unfold:
  "sup_state_opt G \<equiv> Opt.le (Product.le (Listn.le (subtype G)) (Listn.le (Err.le (subtype G))))"
  by (simp add: sup_state_opt_def sup_state_def sup_loc_def sup_ty_opt_def)


lemma app_mono:
  "app_mono (sup_state_opt G) (\<lambda>pc. app (bs!pc) G maxs rT pc et) (length bs) (opt_states G maxs maxr)"
  by (unfold app_mono_def lesub_def) (blast intro: EffectMono.app_mono)
  

lemma list_appendI:
  "\<lbrakk>a \<in> list x A; b \<in> list y A\<rbrakk> \<Longrightarrow> a @ b \<in> list (x+y) A"
  apply (unfold list_def)
  apply (simp (no_asm))
  apply blast
  done

lemma list_map [simp]:
  "(map f xs \<in> list (length xs) A) = (f ` set xs \<subseteq> A)"
  apply (unfold list_def)
  apply simp
  done

lemma [iff]:
  "(OK ` A \<subseteq> err B) = (A \<subseteq> B)"
  apply (unfold err_def)
  apply blast
  done

lemma [intro]:
  "x \<in> A \<Longrightarrow> replicate n x \<in> list n A"
  by (induct n, auto)

lemma lesubstep_type_simple:
  "a <=[Product.le (op =) r] b \<Longrightarrow> a <=|r| b"
  apply (unfold lesubstep_type_def)
  apply clarify
  apply (simp add: set_conv_nth)
  apply clarify
  apply (drule le_listD, assumption)
  apply (clarsimp simp add: lesub_def Product.le_def)
  apply (rule exI)
  apply (rule conjI)
   apply (rule exI)
   apply (rule conjI)
    apply (rule sym)
    apply assumption
   apply assumption
  apply assumption
  done
  

lemma eff_mono:
  "\<lbrakk>p < length bs; s <=_(sup_state_opt G) t; app (bs!p) G maxs rT pc et t\<rbrakk>
  \<Longrightarrow> eff (bs!p) G p et s <=|sup_state_opt G| eff (bs!p) G p et t"
  apply (unfold eff_def)
  apply (rule lesubstep_type_simple)
  apply (rule le_list_appendI)
   apply (simp add: norm_eff_def)
   apply (rule le_listI)
    apply simp
   apply simp
   apply (simp add: lesub_def)
   apply (case_tac s)
    apply simp
   apply (simp del: split_paired_All split_paired_Ex)
   apply (elim exE conjE)
   apply simp
   apply (drule eff'_mono, assumption)
   apply assumption
  apply (simp add: xcpt_eff_def)
  apply (rule le_listI)
    apply simp
  apply simp
  apply (simp add: lesub_def)
  apply (case_tac s)
   apply simp
  apply simp
  apply (case_tac t)
   apply simp
  apply (clarsimp simp add: sup_state_conv)
  done

lemma order_sup_state_opt:
  "wf_prog wf_mb G \<Longrightarrow> order (sup_state_opt G)"
  by (unfold sup_state_opt_unfold) (blast dest: acyclic_subcls1 order_widen)

theorem exec_mono:
  "wf_prog wf_mb G \<Longrightarrow> bounded (exec G maxs rT et bs) (size bs) \<Longrightarrow>
  mono (JVMType.le G maxs maxr) (exec G maxs rT et bs) (size bs) (states G maxs maxr)"  
  apply (unfold exec_def JVM_le_unfold JVM_states_unfold)  
  apply (rule mono_lift)
     apply (fold sup_state_opt_unfold opt_states_def)
     apply (erule order_sup_state_opt)
    apply (rule app_mono)
   apply assumption
  apply clarify
  apply (rule eff_mono)
  apply assumption+
  done

theorem semilat_JVM_slI:
  "wf_prog wf_mb G \<Longrightarrow> semilat (JVMType.sl G maxs maxr)"
  apply (unfold JVMType.sl_def stk_esl_def reg_sl_def)
  apply (rule semilat_opt)
  apply (rule err_semilat_Product_esl)
  apply (rule err_semilat_upto_esl)
  apply (rule err_semilat_JType_esl, assumption+)
  apply (rule err_semilat_eslI)
  apply (rule Listn_sl)
  apply (rule err_semilat_JType_esl, assumption+)
  done

lemma sl_triple_conv:
  "JVMType.sl G maxs maxr == 
  (states G maxs maxr, JVMType.le G maxs maxr, JVMType.sup G maxs maxr)"
  by (simp (no_asm) add: states_def JVMType.le_def JVMType.sup_def)


lemma map_id [rule_format]:
  "(\<forall>n < length xs. f (g (xs!n)) = xs!n) \<longrightarrow> map f (map g xs) = xs"
  by (induct xs, auto)


lemma is_type_pTs:
  "\<lbrakk> wf_prog wf_mb G; (C,S,fs,mdecls) \<in> set G; ((mn,pTs),rT,code) \<in> set mdecls \<rbrakk>
  \<Longrightarrow> set pTs \<subseteq> types G"
proof 
  assume "wf_prog wf_mb G" 
         "(C,S,fs,mdecls) \<in> set G"
         "((mn,pTs),rT,code) \<in> set mdecls"
  hence "wf_mdecl wf_mb G C ((mn,pTs),rT,code)"
    by (unfold wf_prog_def wf_cdecl_def) auto  
  hence "\<forall>t \<in> set pTs. is_type G t" 
    by (unfold wf_mdecl_def wf_mhead_def) auto
  moreover
  fix t assume "t \<in> set pTs"
  ultimately
  have "is_type G t" by blast
  thus "t \<in> types G" ..
qed


lemma jvm_prog_lift:  
  assumes wf: 
  "wf_prog (\<lambda>G C bd. P G C bd) G"

  assumes rule:
  "\<And>wf_mb C mn pTs C rT maxs maxl b et bd.
   wf_prog wf_mb G \<Longrightarrow>
   method (G,C) (mn,pTs) = Some (C,rT,maxs,maxl,b,et) \<Longrightarrow>
   is_class G C \<Longrightarrow>
   set pTs \<subseteq> types G \<Longrightarrow>
   bd = ((mn,pTs),rT,maxs,maxl,b,et) \<Longrightarrow>
   P G C bd \<Longrightarrow>
   Q G C bd"
 
  shows 
  "wf_prog (\<lambda>G C bd. Q G C bd) G"
proof -
  from wf show ?thesis
    apply (unfold wf_prog_def wf_cdecl_def)
    apply clarsimp
    apply (drule bspec, assumption)
    apply (unfold wf_mdecl_def)
    apply clarsimp
    apply (drule bspec, assumption)
    apply clarsimp
    apply (frule methd [OF wf], assumption+)
    apply (frule is_type_pTs [OF wf], assumption+)
    apply clarify
    apply (drule rule [OF wf], assumption+)
    apply (rule refl)
    apply assumption+
    done
qed

end
