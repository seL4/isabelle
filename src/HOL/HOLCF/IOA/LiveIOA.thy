(*  Title:      HOL/HOLCF/IOA/LiveIOA.thy
    Author:     Olaf Müller
*)

section \<open>Live I/O automata -- specified by temproal formulas\<close>

theory LiveIOA
imports TLS
begin

default_sort type

type_synonym ('a, 's) live_ioa = "('a, 's)ioa \<times> ('a, 's) ioa_temp"

definition validLIOA :: "('a, 's) live_ioa \<Rightarrow> ('a, 's) ioa_temp \<Rightarrow> bool"
  where "validLIOA AL P \<longleftrightarrow> validIOA (fst AL) (snd AL \<^bold>\<longrightarrow> P)"

definition WF :: "('a, 's) ioa \<Rightarrow> 'a set \<Rightarrow> ('a, 's) ioa_temp"
  where "WF A acts = (\<diamond>\<box>\<langle>\<lambda>(s,a,t). Enabled A acts s\<rangle> \<^bold>\<longrightarrow> \<box>\<diamond>\<langle>xt2 (plift (\<lambda>a. a \<in> acts))\<rangle>)"

definition SF :: "('a, 's) ioa \<Rightarrow> 'a set \<Rightarrow> ('a, 's) ioa_temp"
  where "SF A acts = (\<box>\<diamond>\<langle>\<lambda>(s,a,t). Enabled A acts s\<rangle> \<^bold>\<longrightarrow> \<box>\<diamond>\<langle>xt2 (plift (\<lambda>a. a \<in> acts))\<rangle>)"

definition liveexecutions :: "('a, 's) live_ioa \<Rightarrow> ('a, 's) execution set"
  where "liveexecutions AP = {exec. exec \<in> executions (fst AP) \<and> (exec \<TTurnstile> snd AP)}"

definition livetraces :: "('a, 's) live_ioa \<Rightarrow> 'a trace set"
  where "livetraces AP = {mk_trace (fst AP) \<cdot> (snd ex) |ex. ex \<in> liveexecutions AP}"

definition live_implements :: "('a, 's1) live_ioa \<Rightarrow> ('a, 's2) live_ioa \<Rightarrow> bool"
  where "live_implements CL AM \<longleftrightarrow>
    inp (fst CL) = inp (fst AM) \<and> out (fst CL) = out (fst AM) \<and>
      livetraces CL \<subseteq> livetraces AM"

definition is_live_ref_map :: "('s1 \<Rightarrow> 's2) \<Rightarrow> ('a, 's1) live_ioa \<Rightarrow> ('a, 's2) live_ioa \<Rightarrow> bool"
  where "is_live_ref_map f CL AM \<longleftrightarrow>
    is_ref_map f (fst CL ) (fst AM) \<and>
    (\<forall>exec \<in> executions (fst CL). (exec \<TTurnstile> (snd CL)) \<longrightarrow>
      (corresp_ex (fst AM) f exec \<TTurnstile> snd AM))"

lemma live_implements_trans:
  "live_implements (A, LA) (B, LB) \<Longrightarrow> live_implements (B, LB) (C, LC) \<Longrightarrow>
    live_implements (A, LA) (C, LC)"
  by (auto simp: live_implements_def)


subsection \<open>Correctness of live refmap\<close>

lemma live_implements:
  "inp C = inp A \<Longrightarrow> out C = out A \<Longrightarrow> is_live_ref_map f (C, M) (A, L)
    \<Longrightarrow> live_implements (C, M) (A, L)"
  apply (simp add: is_live_ref_map_def live_implements_def livetraces_def liveexecutions_def)
  apply auto
  apply (rule_tac x = "corresp_ex A f ex" in exI)
  apply auto
  text \<open>Traces coincide, Lemma 1\<close>
  apply (pair ex)
  apply (erule lemma_1 [THEN spec, THEN mp])
  apply (simp (no_asm) add: externals_def)
  apply (auto)[1]
  apply (simp add: executions_def reachable.reachable_0)
  text \<open>\<open>corresp_ex\<close> is execution, Lemma 2\<close>
  apply (pair ex)
  apply (simp add: executions_def)
  text \<open>start state\<close>
  apply (rule conjI)
  apply (simp add: is_ref_map_def corresp_ex_def)
  text \<open>\<open>is_execution_fragment\<close>\<close>
  apply (erule lemma_2 [THEN spec, THEN mp])
  apply (simp add: reachable.reachable_0)
  done

end
