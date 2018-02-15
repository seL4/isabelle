(*  Title:      HOL/HOLCF/IOA/RefCorrectness.thy
    Author:     Olaf Müller
*)

section \<open>Correctness of Refinement Mappings in HOLCF/IOA\<close>

theory RefCorrectness
imports RefMappings
begin

definition corresp_exC ::
    "('a, 's2) ioa \<Rightarrow> ('s1 \<Rightarrow> 's2) \<Rightarrow> ('a, 's1) pairs \<rightarrow> ('s1 \<Rightarrow> ('a, 's2) pairs)"
  where "corresp_exC A f =
    (fix \<cdot>
      (LAM h ex.
        (\<lambda>s. case ex of
          nil \<Rightarrow> nil
        | x ## xs \<Rightarrow>
            flift1 (\<lambda>pr.
              (SOME cex. move A cex (f s) (fst pr) (f (snd pr))) @@ ((h \<cdot> xs) (snd pr))) \<cdot> x)))"

definition corresp_ex ::
    "('a, 's2) ioa \<Rightarrow> ('s1 \<Rightarrow> 's2) \<Rightarrow> ('a, 's1) execution \<Rightarrow> ('a, 's2) execution"
  where "corresp_ex A f ex = (f (fst ex), (corresp_exC A f \<cdot> (snd ex)) (fst ex))"

definition is_fair_ref_map ::
    "('s1 \<Rightarrow> 's2) \<Rightarrow> ('a, 's1) ioa \<Rightarrow> ('a, 's2) ioa \<Rightarrow> bool"
  where "is_fair_ref_map f C A \<longleftrightarrow>
    is_ref_map f C A \<and> (\<forall>ex \<in> executions C. fair_ex C ex \<longrightarrow> fair_ex A (corresp_ex A f ex))"

text \<open>
  Axioms for fair trace inclusion proof support, not for the correctness proof
  of refinement mappings!

  Note: Everything is superseded by \<^file>\<open>LiveIOA.thy\<close>.
\<close>

axiomatization where
  corresp_laststate:
    "Finite ex \<Longrightarrow> laststate (corresp_ex A f (s, ex)) = f (laststate (s, ex))"

axiomatization where
  corresp_Finite: "Finite (snd (corresp_ex A f (s, ex))) = Finite ex"

axiomatization where
  FromAtoC:
    "fin_often (\<lambda>x. P (snd x)) (snd (corresp_ex A f (s, ex))) \<Longrightarrow>
      fin_often (\<lambda>y. P (f (snd y))) ex"

axiomatization where
  FromCtoA:
    "inf_often (\<lambda>y. P (fst y)) ex \<Longrightarrow>
      inf_often (\<lambda>x. P (fst x)) (snd (corresp_ex A f (s,ex)))"


text \<open>
  Proof by case on \<open>inf W\<close> in ex: If so, ok. If not, only \<open>fin W\<close> in ex, ie.
  there is an index \<open>i\<close> from which on no \<open>W\<close> in ex. But \<open>W\<close> inf enabled, ie at
  least once after \<open>i\<close> \<open>W\<close> is enabled. As \<open>W\<close> does not occur after \<open>i\<close> and \<open>W\<close>
  is \<open>enabling_persistent\<close>, \<open>W\<close> keeps enabled until infinity, ie. indefinitely
\<close>

axiomatization where
  persistent:
    "inf_often (\<lambda>x. Enabled A W (snd x)) ex \<Longrightarrow> en_persistent A W \<Longrightarrow>
      inf_often (\<lambda>x. fst x \<in> W) ex \<or> fin_often (\<lambda>x. \<not> Enabled A W (snd x)) ex"

axiomatization where
  infpostcond:
    "is_exec_frag A (s,ex) \<Longrightarrow> inf_often (\<lambda>x. fst x \<in> W) ex \<Longrightarrow>
      inf_often (\<lambda>x. set_was_enabled A W (snd x)) ex"


subsection \<open>\<open>corresp_ex\<close>\<close>

lemma corresp_exC_unfold:
  "corresp_exC A f =
    (LAM ex.
      (\<lambda>s.
        case ex of
          nil \<Rightarrow> nil
        | x ## xs \<Rightarrow>
            (flift1 (\<lambda>pr.
              (SOME cex. move A cex (f s) (fst pr) (f (snd pr))) @@
              ((corresp_exC A f \<cdot> xs) (snd pr))) \<cdot> x)))"
  apply (rule trans)
  apply (rule fix_eq2)
  apply (simp only: corresp_exC_def)
  apply (rule beta_cfun)
  apply (simp add: flift1_def)
  done

lemma corresp_exC_UU: "(corresp_exC A f \<cdot> UU) s = UU"
  apply (subst corresp_exC_unfold)
  apply simp
  done

lemma corresp_exC_nil: "(corresp_exC A f \<cdot> nil) s = nil"
  apply (subst corresp_exC_unfold)
  apply simp
  done

lemma corresp_exC_cons:
  "(corresp_exC A f \<cdot> (at \<leadsto> xs)) s =
     (SOME cex. move A cex (f s) (fst at) (f (snd at))) @@
     ((corresp_exC A f \<cdot> xs) (snd at))"
  apply (rule trans)
  apply (subst corresp_exC_unfold)
  apply (simp add: Consq_def flift1_def)
  apply simp
  done

declare corresp_exC_UU [simp] corresp_exC_nil [simp] corresp_exC_cons [simp]


subsection \<open>Properties of move\<close>

lemma move_is_move:
  "is_ref_map f C A \<Longrightarrow> reachable C s \<Longrightarrow> (s, a, t) \<in> trans_of C \<Longrightarrow>
    move A (SOME x. move A x (f s) a (f t)) (f s) a (f t)"
  apply (unfold is_ref_map_def)
  apply (subgoal_tac "\<exists>ex. move A ex (f s) a (f t) ")
  prefer 2
  apply simp
  apply (erule exE)
  apply (rule someI)
  apply assumption
  done

lemma move_subprop1:
  "is_ref_map f C A \<Longrightarrow> reachable C s \<Longrightarrow> (s, a, t) \<in> trans_of C \<Longrightarrow>
    is_exec_frag A (f s, SOME x. move A x (f s) a (f t))"
  apply (cut_tac move_is_move)
  defer
  apply assumption+
  apply (simp add: move_def)
  done

lemma move_subprop2:
  "is_ref_map f C A \<Longrightarrow> reachable C s \<Longrightarrow> (s, a, t) \<in> trans_of C \<Longrightarrow>
    Finite ((SOME x. move A x (f s) a (f t)))"
  apply (cut_tac move_is_move)
  defer
  apply assumption+
  apply (simp add: move_def)
  done

lemma move_subprop3:
  "is_ref_map f C A \<Longrightarrow> reachable C s \<Longrightarrow> (s, a, t) \<in> trans_of C \<Longrightarrow>
     laststate (f s, SOME x. move A x (f s) a (f t)) = (f t)"
  apply (cut_tac move_is_move)
  defer
  apply assumption+
  apply (simp add: move_def)
  done

lemma move_subprop4:
  "is_ref_map f C A \<Longrightarrow> reachable C s \<Longrightarrow> (s, a, t) \<in> trans_of C \<Longrightarrow>
    mk_trace A \<cdot> ((SOME x. move A x (f s) a (f t))) =
      (if a \<in> ext A then a \<leadsto> nil else nil)"
  apply (cut_tac move_is_move)
  defer
  apply assumption+
  apply (simp add: move_def)
  done


subsection \<open>TRACE INCLUSION Part 1: Traces coincide\<close>

subsubsection \<open>Lemmata for \<open>\<Longleftarrow>\<close>\<close>

text \<open>Lemma 1.1: Distribution of \<open>mk_trace\<close> and \<open>@@\<close>\<close>

lemma mk_traceConc:
  "mk_trace C \<cdot> (ex1 @@ ex2) = (mk_trace C \<cdot> ex1) @@ (mk_trace C \<cdot> ex2)"
  by (simp add: mk_trace_def filter_act_def MapConc)


text \<open>Lemma 1 : Traces coincide\<close>

lemma lemma_1:
  "is_ref_map f C A \<Longrightarrow> ext C = ext A \<Longrightarrow>
    \<forall>s. reachable C s \<and> is_exec_frag C (s, xs) \<longrightarrow>
      mk_trace C \<cdot> xs = mk_trace A \<cdot> (snd (corresp_ex A f (s, xs)))"
  supply if_split [split del]
  apply (unfold corresp_ex_def)
  apply (pair_induct xs simp: is_exec_frag_def)
  text \<open>cons case\<close>
  apply (auto simp add: mk_traceConc)
  apply (frule reachable.reachable_n)
  apply assumption
  apply (auto simp add: move_subprop4 split: if_split)
  done


subsection \<open>TRACE INCLUSION Part 2: corresp_ex is execution\<close>

subsubsection \<open>Lemmata for \<open>==>\<close>\<close>

text \<open>Lemma 2.1\<close>

lemma lemma_2_1 [rule_format]:
  "Finite xs \<longrightarrow>
    (\<forall>s. is_exec_frag A (s, xs) \<and> is_exec_frag A (t, ys) \<and>
      t = laststate (s, xs) \<longrightarrow> is_exec_frag A (s, xs @@ ys))"
  apply (rule impI)
  apply Seq_Finite_induct
  text \<open>main case\<close>
  apply (auto simp add: split_paired_all)
  done


text \<open>Lemma 2 : \<open>corresp_ex\<close> is execution\<close>

lemma lemma_2:
  "is_ref_map f C A \<Longrightarrow>
    \<forall>s. reachable C s \<and> is_exec_frag C (s, xs) \<longrightarrow>
      is_exec_frag A (corresp_ex A f (s, xs))"
  apply (unfold corresp_ex_def)

  apply simp
  apply (pair_induct xs simp: is_exec_frag_def)

  text \<open>main case\<close>
  apply auto
  apply (rule_tac t = "f x2" in lemma_2_1)

  text \<open>\<open>Finite\<close>\<close>
  apply (erule move_subprop2)
  apply assumption+
  apply (rule conjI)

  text \<open>\<open>is_exec_frag\<close>\<close>
  apply (erule move_subprop1)
  apply assumption+
  apply (rule conjI)

  text \<open>Induction hypothesis\<close>
  text \<open>\<open>reachable_n\<close> looping, therefore apply it manually\<close>
  apply (erule_tac x = "x2" in allE)
  apply simp
  apply (frule reachable.reachable_n)
  apply assumption
  apply simp

  text \<open>\<open>laststate\<close>\<close>
  apply (erule move_subprop3 [symmetric])
  apply assumption+
  done


subsection \<open>Main Theorem: TRACE -- INCLUSION\<close>

theorem trace_inclusion:
  "ext C = ext A \<Longrightarrow> is_ref_map f C A \<Longrightarrow> traces C \<subseteq> traces A"

  apply (unfold traces_def)

  apply (simp add: has_trace_def2)
  apply auto

  text \<open>give execution of abstract automata\<close>
  apply (rule_tac x = "corresp_ex A f ex" in bexI)

  text \<open>Traces coincide, Lemma 1\<close>
  apply (pair ex)
  apply (erule lemma_1 [THEN spec, THEN mp])
  apply assumption+
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


subsection \<open>Corollary:  FAIR TRACE -- INCLUSION\<close>

lemma fininf: "(~inf_often P s) = fin_often P s"
  by (auto simp: fin_often_def)

lemma WF_alt: "is_wfair A W (s, ex) =
  (fin_often (\<lambda>x. \<not> Enabled A W (snd x)) ex \<longrightarrow> inf_often (\<lambda>x. fst x \<in> W) ex)"
  by (auto simp add: is_wfair_def fin_often_def)

lemma WF_persistent:
  "is_wfair A W (s, ex) \<Longrightarrow> inf_often (\<lambda>x. Enabled A W (snd x)) ex \<Longrightarrow>
    en_persistent A W \<Longrightarrow> inf_often (\<lambda>x. fst x \<in> W) ex"
  apply (drule persistent)
  apply assumption
  apply (simp add: WF_alt)
  apply auto
  done

lemma fair_trace_inclusion:
  assumes "is_ref_map f C A"
    and "ext C = ext A"
    and "\<And>ex. ex \<in> executions C \<Longrightarrow> fair_ex C ex \<Longrightarrow>
      fair_ex A (corresp_ex A f ex)"
  shows "fairtraces C \<subseteq> fairtraces A"
  apply (insert assms)
  apply (simp add: fairtraces_def fairexecutions_def)
  apply auto
  apply (rule_tac x = "corresp_ex A f ex" in exI)
  apply auto

  text \<open>Traces coincide, Lemma 1\<close>
  apply (pair ex)
  apply (erule lemma_1 [THEN spec, THEN mp])
  apply assumption+
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

lemma fair_trace_inclusion2:
  "inp C = inp A \<Longrightarrow> out C = out A \<Longrightarrow> is_fair_ref_map f C A \<Longrightarrow>
    fair_implements C A"
  apply (simp add: is_fair_ref_map_def fair_implements_def fairtraces_def fairexecutions_def)
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
