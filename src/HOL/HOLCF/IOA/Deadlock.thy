(*  Title:      HOL/HOLCF/IOA/Deadlock.thy
    Author:     Olaf Müller
*)

section \<open>Deadlock freedom of I/O Automata\<close>

theory Deadlock
imports RefCorrectness CompoScheds
begin

text \<open>Input actions may always be added to a schedule.\<close>

lemma scheds_input_enabled:
  "Filter (\<lambda>x. x \<in> act A) \<cdot> sch \<in> schedules A \<Longrightarrow> a \<in> inp A \<Longrightarrow> input_enabled A \<Longrightarrow> Finite sch
    \<Longrightarrow> Filter (\<lambda>x. x \<in> act A) \<cdot> sch @@ a \<leadsto> nil \<in> schedules A"
  apply (simp add: schedules_def has_schedule_def)
  apply auto
  apply (frule inp_is_act)
  apply (simp add: executions_def)
  apply (pair ex)
  apply (rename_tac s ex)
  apply (subgoal_tac "Finite ex")
  prefer 2
  apply (simp add: filter_act_def)
  defer
  apply (rule_tac [2] Map2Finite [THEN iffD1])
  apply (rule_tac [2] t = "Map fst \<cdot> ex" in subst)
  prefer 2
  apply assumption
  apply (erule_tac [2] FiniteFilter)
  text \<open>subgoal 1\<close>
  apply (frule exists_laststate)
  apply (erule allE)
  apply (erule exE)
  text \<open>using input-enabledness\<close>
  apply (simp add: input_enabled_def)
  apply (erule conjE)+
  apply (erule_tac x = "a" in allE)
  apply simp
  apply (erule_tac x = "u" in allE)
  apply (erule exE)
  text \<open>instantiate execution\<close>
  apply (rule_tac x = " (s, ex @@ (a, s2) \<leadsto> nil) " in exI)
  apply (simp add: filter_act_def MapConc)
  apply (erule_tac t = "u" in lemma_2_1)
  apply simp
  apply (rule sym)
  apply assumption
  done

text \<open>
  Deadlock freedom: component B cannot block an out or int action of component
  A in every schedule.

  Needs compositionality on schedule level, input-enabledness, compatibility
  and distributivity of \<open>is_exec_frag\<close> over \<open>@@\<close>.
\<close>

lemma IOA_deadlock_free:
  assumes "a \<in> local A"
    and "Finite sch"
    and "sch \<in> schedules (A \<parallel> B)"
    and "Filter (\<lambda>x. x \<in> act A) \<cdot> (sch @@ a \<leadsto> nil) \<in> schedules A"
    and "compatible A B"
    and "input_enabled B"
  shows "(sch @@ a \<leadsto> nil) \<in> schedules (A \<parallel> B)"
  supply if_split [split del]
  apply (insert assms)
  apply (simp add: compositionality_sch locals_def)
  apply (rule conjI)
  text \<open>\<open>a \<in> act (A \<parallel> B)\<close>\<close>
  prefer 2
  apply (simp add: actions_of_par)
  apply (blast dest: int_is_act out_is_act)

  text \<open>\<open>Filter B (sch @@ [a]) \<in> schedules B\<close>\<close>
  apply (case_tac "a \<in> int A")
  apply (drule intA_is_not_actB)
  apply (assumption) (* \<longrightarrow> a \<notin> act B *)
  apply simp

  text \<open>case \<open>a \<notin> int A\<close>, i.e. \<open>a \<in> out A\<close>\<close>
  apply (case_tac "a \<notin> act B")
  apply simp
  text \<open>case \<open>a \<in> act B\<close>\<close>
  apply simp
  apply (subgoal_tac "a \<in> out A")
  prefer 2
  apply blast
  apply (drule outAactB_is_inpB)
  apply assumption
  apply assumption
  apply (rule scheds_input_enabled)
  apply simp
  apply assumption+
  done

end
