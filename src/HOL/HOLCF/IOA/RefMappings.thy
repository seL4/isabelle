(*  Title:      HOL/HOLCF/IOA/RefMappings.thy
    Author:     Olaf Müller
*)

section \<open>Refinement Mappings in HOLCF/IOA\<close>

theory RefMappings
imports Traces
begin

default_sort type

definition move :: "('a, 's) ioa \<Rightarrow> ('a, 's) pairs \<Rightarrow> 's \<Rightarrow> 'a \<Rightarrow> 's \<Rightarrow> bool"
  where "move ioa ex s a t \<longleftrightarrow>
    is_exec_frag ioa (s, ex) \<and> Finite ex \<and>
    laststate (s, ex) = t \<and>
    mk_trace ioa \<cdot> ex = (if a \<in> ext ioa then a \<leadsto> nil else nil)"

definition is_ref_map :: "('s1 \<Rightarrow> 's2) \<Rightarrow> ('a, 's1) ioa \<Rightarrow> ('a, 's2) ioa \<Rightarrow> bool"
  where "is_ref_map f C A \<longleftrightarrow>
   ((\<forall>s \<in> starts_of C. f s \<in> starts_of A) \<and>
     (\<forall>s t a. reachable C s \<and> s \<midarrow>a\<midarrow>C\<rightarrow> t \<longrightarrow> (\<exists>ex. move A ex (f s) a (f t))))"

definition is_weak_ref_map :: "('s1 \<Rightarrow> 's2) \<Rightarrow> ('a, 's1) ioa \<Rightarrow> ('a, 's2) ioa \<Rightarrow> bool"
  where "is_weak_ref_map f C A \<longleftrightarrow>
    ((\<forall>s \<in> starts_of C. f s \<in> starts_of A) \<and>
      (\<forall>s t a. reachable C s \<and> s \<midarrow>a\<midarrow>C\<rightarrow> t \<longrightarrow>
        (if a \<in> ext C then (f s) \<midarrow>a\<midarrow>A\<rightarrow> (f t) else f s = f t)))"


subsection \<open>Transitions and moves\<close>

lemma transition_is_ex: "s \<midarrow>a\<midarrow>A\<rightarrow> t \<Longrightarrow> \<exists>ex. move A ex s a t"
  apply (rule_tac x = " (a, t) \<leadsto> nil" in exI)
  apply (simp add: move_def)
  done

lemma nothing_is_ex: "a \<notin> ext A \<and> s = t \<Longrightarrow> \<exists>ex. move A ex s a t"
  apply (rule_tac x = "nil" in exI)
  apply (simp add: move_def)
  done

lemma ei_transitions_are_ex:
  "s \<midarrow>a\<midarrow>A\<rightarrow> s' \<and> s' \<midarrow>a'\<midarrow>A\<rightarrow> s'' \<and> a' \<notin> ext A \<Longrightarrow> \<exists>ex. move A ex s a s''"
  apply (rule_tac x = " (a,s') \<leadsto> (a',s'') \<leadsto>nil" in exI)
  apply (simp add: move_def)
  done

lemma eii_transitions_are_ex:
  "s1 \<midarrow>a1\<midarrow>A\<rightarrow> s2 \<and> s2 \<midarrow>a2\<midarrow>A\<rightarrow> s3 \<and> s3 \<midarrow>a3\<midarrow>A\<rightarrow> s4 \<and> a2 \<notin> ext A \<and> a3 \<notin> ext A \<Longrightarrow>
    \<exists>ex. move A ex s1 a1 s4"
  apply (rule_tac x = "(a1, s2) \<leadsto> (a2, s3) \<leadsto> (a3, s4) \<leadsto> nil" in exI)
  apply (simp add: move_def)
  done


subsection \<open>\<open>weak_ref_map\<close> and \<open>ref_map\<close>\<close>

lemma weak_ref_map2ref_map: "ext C = ext A \<Longrightarrow> is_weak_ref_map f C A \<Longrightarrow> is_ref_map f C A"
  apply (unfold is_weak_ref_map_def is_ref_map_def)
  apply auto
  apply (case_tac "a \<in> ext A")
  apply (auto intro: transition_is_ex nothing_is_ex)
  done

lemma imp_conj_lemma: "(P \<Longrightarrow> Q \<longrightarrow> R) \<Longrightarrow> P \<and> Q \<longrightarrow> R"
  by blast

declare if_split [split del]
declare if_weak_cong [cong del]

lemma rename_through_pmap:
  "is_weak_ref_map f C A \<Longrightarrow> is_weak_ref_map f (rename C g) (rename A g)"
  apply (simp add: is_weak_ref_map_def)
  apply (rule conjI)
  text \<open>1: start states\<close>
  apply (simp add: rename_def rename_set_def starts_of_def)
  text \<open>1: start states\<close>
  apply (rule allI)+
  apply (rule imp_conj_lemma)
  apply (simp (no_asm) add: rename_def rename_set_def)
  apply (simp add: externals_def asig_inputs_def asig_outputs_def asig_of_def trans_of_def)
  apply safe
  apply (simplesubst if_split)
   apply (rule conjI)
   apply (rule impI)
   apply (erule disjE)
   apply (erule exE)
  apply (erule conjE)
  text \<open>\<open>x\<close> is input\<close>
   apply (drule sym)
   apply (drule sym)
  apply simp
  apply hypsubst+
  apply (frule reachable_rename)
  apply simp
  text \<open>\<open>x\<close> is output\<close>
   apply (erule exE)
  apply (erule conjE)
   apply (drule sym)
   apply (drule sym)
  apply simp
  apply hypsubst+
  apply (frule reachable_rename)
  apply simp
  text \<open>\<open>x\<close> is internal\<close>
  apply (frule reachable_rename)
  apply auto
  done

declare if_split [split]
declare if_weak_cong [cong]

end
