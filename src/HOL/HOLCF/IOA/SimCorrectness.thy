(*  Title:      HOL/HOLCF/IOA/SimCorrectness.thy
    Author:     Olaf Müller
*)

section \<open>Correctness of Simulations in HOLCF/IOA\<close>

theory SimCorrectness
imports Simulations
begin

(*Note: s2 instead of s1 in last argument type!*)
definition corresp_ex_simC ::
    "('a, 's2) ioa \<Rightarrow> ('s1 \<times> 's2) set \<Rightarrow> ('a, 's1) pairs \<rightarrow> ('s2 \<Rightarrow> ('a, 's2) pairs)"
  where "corresp_ex_simC A R =
    (fix \<cdot> (LAM h ex. (\<lambda>s. case ex of
      nil \<Rightarrow> nil
    | x ## xs \<Rightarrow>
        (flift1
          (\<lambda>pr.
            let
              a = fst pr;
              t = snd pr;
              T' = SOME t'. \<exists>ex1. (t, t') \<in> R \<and> move A ex1 s a t'
            in (SOME cex. move A cex s a T') @@ ((h \<cdot> xs) T')) \<cdot> x))))"

definition corresp_ex_sim ::
    "('a, 's2) ioa \<Rightarrow> ('s1 \<times> 's2) set \<Rightarrow> ('a, 's1) execution \<Rightarrow> ('a, 's2) execution"
  where "corresp_ex_sim A R ex \<equiv>
    let S' = SOME s'. (fst ex, s') \<in> R \<and> s' \<in> starts_of A
    in (S', (corresp_ex_simC A R \<cdot> (snd ex)) S')"


subsection \<open>\<open>corresp_ex_sim\<close>\<close>

lemma corresp_ex_simC_unfold:
  "corresp_ex_simC A R =
    (LAM ex. (\<lambda>s. case ex of
      nil \<Rightarrow> nil
    | x ## xs \<Rightarrow>
        (flift1
          (\<lambda>pr.
            let
              a = fst pr;
              t = snd pr;
              T' = SOME t'. \<exists>ex1. (t, t') \<in> R \<and> move A ex1 s a t'
            in (SOME cex. move A cex s a T') @@ ((corresp_ex_simC A R \<cdot> xs) T')) \<cdot> x)))"
  apply (rule trans)
  apply (rule fix_eq2)
  apply (simp only: corresp_ex_simC_def)
  apply (rule beta_cfun)
  apply (simp add: flift1_def)
  done

lemma corresp_ex_simC_UU [simp]: "(corresp_ex_simC A R \<cdot> UU) s = UU"
  apply (subst corresp_ex_simC_unfold)
  apply simp
  done

lemma corresp_ex_simC_nil [simp]: "(corresp_ex_simC A R \<cdot> nil) s = nil"
  apply (subst corresp_ex_simC_unfold)
  apply simp
  done

lemma corresp_ex_simC_cons [simp]:
  "(corresp_ex_simC A R \<cdot> ((a, t) \<leadsto> xs)) s =
    (let T' = SOME t'. \<exists>ex1. (t, t') \<in> R \<and> move A ex1 s a t'
     in (SOME cex. move A cex s a T') @@ ((corresp_ex_simC A R \<cdot> xs) T'))"
  apply (rule trans)
  apply (subst corresp_ex_simC_unfold)
  apply (simp add: Consq_def flift1_def)
  apply simp
  done


subsection \<open>Properties of move\<close>

lemma move_is_move_sim:
   "is_simulation R C A \<Longrightarrow> reachable C s \<Longrightarrow> s \<midarrow>a\<midarrow>C\<rightarrow> t \<Longrightarrow> (s, s') \<in> R \<Longrightarrow>
     let T' = SOME t'. \<exists>ex1. (t, t') \<in> R \<and> move A ex1 s' a t'
     in (t, T') \<in> R \<and> move A (SOME ex2. move A ex2 s' a T') s' a T'"
  supply Let_def [simp del]
  apply (unfold is_simulation_def)
  (* Does not perform conditional rewriting on assumptions automatically as
     usual. Instantiate all variables per hand. Ask Tobias?? *)
  apply (subgoal_tac "\<exists>t' ex. (t, t') \<in> R \<and> move A ex s' a t'")
  prefer 2
  apply simp
  apply (erule conjE)
  apply (erule_tac x = "s" in allE)
  apply (erule_tac x = "s'" in allE)
  apply (erule_tac x = "t" in allE)
  apply (erule_tac x = "a" in allE)
  apply simp
  (* Go on as usual *)
  apply (erule exE)
  apply (drule_tac x = "t'" and P = "\<lambda>t'. \<exists>ex. (t, t') \<in> R \<and> move A ex s' a t'" in someI)
  apply (erule exE)
  apply (erule conjE)
  apply (simp add: Let_def)
  apply (rule_tac x = "ex" in someI)
  apply assumption
  done

lemma move_subprop1_sim:
  "is_simulation R C A \<Longrightarrow> reachable C s \<Longrightarrow> s \<midarrow>a\<midarrow>C\<rightarrow> t \<Longrightarrow> (s, s') \<in> R \<Longrightarrow>
    let T' = SOME t'. \<exists>ex1. (t, t') \<in> R \<and> move A ex1 s' a t'
    in is_exec_frag A (s', SOME x. move A x s' a T')"
  apply (cut_tac move_is_move_sim)
  defer
  apply assumption+
  apply (simp add: move_def)
  done

lemma move_subprop2_sim:
  "is_simulation R C A \<Longrightarrow> reachable C s \<Longrightarrow> s \<midarrow>a\<midarrow>C\<rightarrow> t \<Longrightarrow> (s, s') \<in> R \<Longrightarrow>
    let T' = SOME t'. \<exists>ex1. (t, t') \<in> R \<and> move A ex1 s' a t'
    in Finite (SOME x. move A x s' a T')"
  apply (cut_tac move_is_move_sim)
  defer
  apply assumption+
  apply (simp add: move_def)
  done

lemma move_subprop3_sim:
  "is_simulation R C A \<Longrightarrow> reachable C s \<Longrightarrow> s \<midarrow>a\<midarrow>C\<rightarrow> t \<Longrightarrow> (s, s') \<in> R \<Longrightarrow>
    let T' = SOME t'. \<exists>ex1. (t, t') \<in> R \<and> move A ex1 s' a t'
    in laststate (s', SOME x. move A x s' a T') = T'"
  apply (cut_tac move_is_move_sim)
  defer
  apply assumption+
  apply (simp add: move_def)
  done

lemma move_subprop4_sim:
  "is_simulation R C A \<Longrightarrow> reachable C s \<Longrightarrow> s \<midarrow>a\<midarrow>C\<rightarrow> t \<Longrightarrow> (s, s') \<in> R \<Longrightarrow>
    let T' = SOME t'. \<exists>ex1. (t, t') \<in> R \<and> move A ex1 s' a t'
    in mk_trace A \<cdot> (SOME x. move A x s' a T') = (if a \<in> ext A then a \<leadsto> nil else nil)"
  apply (cut_tac move_is_move_sim)
  defer
  apply assumption+
  apply (simp add: move_def)
  done

lemma move_subprop5_sim:
  "is_simulation R C A \<Longrightarrow> reachable C s \<Longrightarrow> s \<midarrow>a\<midarrow>C\<rightarrow> t \<Longrightarrow> (s, s') \<in> R \<Longrightarrow>
    let T' = SOME t'. \<exists>ex1. (t, t') \<in> R \<and> move A ex1 s' a t'
    in (t, T') \<in> R"
  apply (cut_tac move_is_move_sim)
  defer
  apply assumption+
  apply (simp add: move_def)
  done


subsection \<open>TRACE INCLUSION Part 1: Traces coincide\<close>

subsubsection "Lemmata for <=="

text \<open>Lemma 1: Traces coincide\<close>

lemma traces_coincide_sim [rule_format (no_asm)]:
  "is_simulation R C A \<Longrightarrow> ext C = ext A \<Longrightarrow>
    \<forall>s s'. reachable C s \<and> is_exec_frag C (s, ex) \<and> (s, s') \<in> R \<longrightarrow>
      mk_trace C \<cdot> ex = mk_trace A \<cdot> ((corresp_ex_simC A R \<cdot> ex) s')"
  supply if_split [split del]
  apply (pair_induct ex simp: is_exec_frag_def)
  text \<open>cons case\<close>
  apply auto
  apply (rename_tac ex a t s s')
  apply (simp add: mk_traceConc)
  apply (frule reachable.reachable_n)
  apply assumption
  apply (erule_tac x = "t" in allE)
  apply (erule_tac x = "SOME t'. \<exists>ex1. (t, t') \<in> R \<and> move A ex1 s' a t'" in allE)
  apply (simp add: move_subprop5_sim [unfolded Let_def]
    move_subprop4_sim [unfolded Let_def] split: if_split)
  done

text \<open>Lemma 2: \<open>corresp_ex_sim\<close> is execution\<close>

lemma correspsim_is_execution [rule_format]:
  "is_simulation R C A \<Longrightarrow>
    \<forall>s s'. reachable C s \<and> is_exec_frag C (s, ex) \<and> (s, s') \<in> R
      \<longrightarrow> is_exec_frag A (s', (corresp_ex_simC A R \<cdot> ex) s')"
  apply (pair_induct ex simp: is_exec_frag_def)
  text \<open>main case\<close>
  apply auto
  apply (rename_tac ex a t s s')
  apply (rule_tac t = "SOME t'. \<exists>ex1. (t, t') \<in> R \<and> move A ex1 s' a t'" in lemma_2_1)

  text \<open>Finite\<close>
  apply (erule move_subprop2_sim [unfolded Let_def])
  apply assumption+
  apply (rule conjI)

  text \<open>\<open>is_exec_frag\<close>\<close>
  apply (erule move_subprop1_sim [unfolded Let_def])
  apply assumption+
  apply (rule conjI)

  text \<open>Induction hypothesis\<close>
  text \<open>\<open>reachable_n\<close> looping, therefore apply it manually\<close>
  apply (erule_tac x = "t" in allE)
  apply (erule_tac x = "SOME t'. \<exists>ex1. (t, t') \<in> R \<and> move A ex1 s' a t'" in allE)
  apply simp
  apply (frule reachable.reachable_n)
  apply assumption
  apply (simp add: move_subprop5_sim [unfolded Let_def])
  text \<open>laststate\<close>
  apply (erule move_subprop3_sim [unfolded Let_def, symmetric])
  apply assumption+
  done


subsection \<open>Main Theorem: TRACE - INCLUSION\<close>

text \<open>
  Generate condition \<open>(s, S') \<in> R \<and> S' \<in> starts_of A\<close>, the first being
  interesting for the induction cases concerning the two lemmas
  \<open>correpsim_is_execution\<close> and \<open>traces_coincide_sim\<close>, the second for the start
  state case.
  \<open>S' := SOME s'. (s, s') \<in> R \<and> s' \<in> starts_of A\<close>, where \<open>s \<in> starts_of C\<close>
\<close>

lemma simulation_starts:
  "is_simulation R C A \<Longrightarrow> s\<in>starts_of C \<Longrightarrow>
    let S' = SOME s'. (s, s') \<in> R \<and> s' \<in> starts_of A
    in (s, S') \<in> R \<and> S' \<in> starts_of A"
  apply (simp add: is_simulation_def corresp_ex_sim_def Int_non_empty Image_def)
  apply (erule conjE)+
  apply (erule ballE)
  prefer 2 apply blast
  apply (erule exE)
  apply (rule someI2)
  apply assumption
  apply blast
  done

lemmas sim_starts1 = simulation_starts [unfolded Let_def, THEN conjunct1]
lemmas sim_starts2 = simulation_starts [unfolded Let_def, THEN conjunct2]


lemma trace_inclusion_for_simulations:
  "ext C = ext A \<Longrightarrow> is_simulation R C A \<Longrightarrow> traces C \<subseteq> traces A"
  apply (unfold traces_def)
  apply (simp add: has_trace_def2)
  apply auto

  text \<open>give execution of abstract automata\<close>
  apply (rule_tac x = "corresp_ex_sim A R ex" in bexI)

  text \<open>Traces coincide, Lemma 1\<close>
  apply (pair ex)
  apply (rename_tac s ex)
  apply (simp add: corresp_ex_sim_def)
  apply (rule_tac s = "s" in traces_coincide_sim)
  apply assumption+
  apply (simp add: executions_def reachable.reachable_0 sim_starts1)

  text \<open>\<open>corresp_ex_sim\<close> is execution, Lemma 2\<close>
  apply (pair ex)
  apply (simp add: executions_def)
  apply (rename_tac s ex)

  text \<open>start state\<close>
  apply (rule conjI)
  apply (simp add: sim_starts2 corresp_ex_sim_def)

  text \<open>\<open>is_execution-fragment\<close>\<close>
  apply (simp add: corresp_ex_sim_def)
  apply (rule_tac s = s in correspsim_is_execution)
  apply assumption
  apply (simp add: reachable.reachable_0 sim_starts1)
  done

end
