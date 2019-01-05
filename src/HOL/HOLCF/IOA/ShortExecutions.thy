(*  Title:      HOL/HOLCF/IOA/ShortExecutions.thy
    Author:     Olaf Müller
*)

theory ShortExecutions
imports Traces
begin

text \<open>
  Some properties about \<open>Cut ex\<close>, defined as follows:

  For every execution ex there is another shorter execution \<open>Cut ex\<close>
  that has the same trace as ex, but its schedule ends with an external action.
\<close>

definition oraclebuild :: "('a \<Rightarrow> bool) \<Rightarrow> 'a Seq \<rightarrow> 'a Seq \<rightarrow> 'a Seq"
  where "oraclebuild P =
    (fix \<cdot>
      (LAM h s t.
        case t of
          nil \<Rightarrow> nil
        | x ## xs \<Rightarrow>
            (case x of
              UU \<Rightarrow> UU
            | Def y \<Rightarrow>
                (Takewhile (\<lambda>x. \<not> P x) \<cdot> s) @@
                (y \<leadsto> (h \<cdot> (TL \<cdot> (Dropwhile (\<lambda>x. \<not> P x) \<cdot> s)) \<cdot> xs)))))"

definition Cut :: "('a \<Rightarrow> bool) \<Rightarrow> 'a Seq \<Rightarrow> 'a Seq"
  where "Cut P s = oraclebuild P \<cdot> s \<cdot> (Filter P \<cdot> s)"

definition LastActExtsch :: "('a,'s) ioa \<Rightarrow> 'a Seq \<Rightarrow> bool"
  where "LastActExtsch A sch \<longleftrightarrow> Cut (\<lambda>x. x \<in> ext A) sch = sch"

axiomatization where
  Cut_prefixcl_Finite: "Finite s \<Longrightarrow> \<exists>y. s = Cut P s @@ y"

axiomatization where
  LastActExtsmall1: "LastActExtsch A sch \<Longrightarrow> LastActExtsch A (TL \<cdot> (Dropwhile P \<cdot> sch))"

axiomatization where
  LastActExtsmall2: "Finite sch1 \<Longrightarrow> LastActExtsch A (sch1 @@ sch2) \<Longrightarrow> LastActExtsch A sch2"

ML \<open>
fun thin_tac' ctxt j =
  rotate_tac (j - 1) THEN'
  eresolve_tac ctxt [thin_rl] THEN'
  rotate_tac (~ (j - 1))
\<close>


subsection \<open>\<open>oraclebuild\<close> rewrite rules\<close>

lemma oraclebuild_unfold:
  "oraclebuild P =
    (LAM s t.
      case t of
        nil \<Rightarrow> nil
      | x ## xs \<Rightarrow>
          (case x of
            UU \<Rightarrow> UU
          | Def y \<Rightarrow>
            (Takewhile (\<lambda>a. \<not> P a) \<cdot> s) @@
            (y \<leadsto> (oraclebuild P \<cdot> (TL \<cdot> (Dropwhile (\<lambda>a. \<not> P a) \<cdot> s)) \<cdot> xs))))"
  apply (rule trans)
  apply (rule fix_eq2)
  apply (simp only: oraclebuild_def)
  apply (rule beta_cfun)
  apply simp
  done

lemma oraclebuild_UU: "oraclebuild P \<cdot> sch \<cdot> UU = UU"
  apply (subst oraclebuild_unfold)
  apply simp
  done

lemma oraclebuild_nil: "oraclebuild P \<cdot> sch \<cdot> nil = nil"
  apply (subst oraclebuild_unfold)
  apply simp
  done

lemma oraclebuild_cons:
  "oraclebuild P \<cdot> s \<cdot> (x \<leadsto> t) =
    (Takewhile (\<lambda>a. \<not> P a) \<cdot> s) @@
    (x \<leadsto> (oraclebuild P \<cdot> (TL \<cdot> (Dropwhile (\<lambda>a. \<not> P a) \<cdot> s)) \<cdot> t))"
  apply (rule trans)
  apply (subst oraclebuild_unfold)
  apply (simp add: Consq_def)
  apply (simp add: Consq_def)
  done


subsection \<open>Cut rewrite rules\<close>

lemma Cut_nil: "Forall (\<lambda>a. \<not> P a) s \<Longrightarrow> Finite s \<Longrightarrow> Cut P s = nil"
  apply (unfold Cut_def)
  apply (subgoal_tac "Filter P \<cdot> s = nil")
  apply (simp add: oraclebuild_nil)
  apply (rule ForallQFilterPnil)
  apply assumption+
  done

lemma Cut_UU: "Forall (\<lambda>a. \<not> P a) s \<Longrightarrow> \<not> Finite s \<Longrightarrow> Cut P s = UU"
  apply (unfold Cut_def)
  apply (subgoal_tac "Filter P \<cdot> s = UU")
  apply (simp add: oraclebuild_UU)
  apply (rule ForallQFilterPUU)
  apply assumption+
  done

lemma Cut_Cons:
  "P t \<Longrightarrow> Forall (\<lambda>x. \<not> P x) ss \<Longrightarrow> Finite ss \<Longrightarrow>
    Cut P (ss @@ (t \<leadsto> rs)) = ss @@ (t \<leadsto> Cut P rs)"
  apply (unfold Cut_def)
  apply (simp add: ForallQFilterPnil oraclebuild_cons TakewhileConc DropwhileConc)
  done


subsection \<open>Cut lemmas for main theorem\<close>

lemma FilterCut: "Filter P \<cdot> s = Filter P \<cdot> (Cut P s)"
  apply (rule_tac A1 = "\<lambda>x. True" and Q1 = "\<lambda>x. \<not> P x" and x1 = "s" in take_lemma_induct [THEN mp])
  prefer 3
  apply fast
  apply (case_tac "Finite s")
  apply (simp add: Cut_nil ForallQFilterPnil)
  apply (simp add: Cut_UU ForallQFilterPUU)
  text \<open>main case\<close>
  apply (simp add: Cut_Cons ForallQFilterPnil)
  done

lemma Cut_idemp: "Cut P (Cut P s) = (Cut P s)"
  apply (rule_tac A1 = "\<lambda>x. True" and Q1 = "\<lambda>x. \<not> P x" and x1 = "s" in
    take_lemma_less_induct [THEN mp])
  prefer 3
  apply fast
  apply (case_tac "Finite s")
  apply (simp add: Cut_nil ForallQFilterPnil)
  apply (simp add: Cut_UU ForallQFilterPUU)
  text \<open>main case\<close>
  apply (simp add: Cut_Cons ForallQFilterPnil)
  apply (rule take_reduction)
  apply auto
  done

lemma MapCut: "Map f\<cdot>(Cut (P \<circ> f) s) = Cut P (Map f\<cdot>s)"
  apply (rule_tac A1 = "\<lambda>x. True" and Q1 = "\<lambda>x. \<not> P (f x) " and x1 = "s" in
    take_lemma_less_induct [THEN mp])
  prefer 3
  apply fast
  apply (case_tac "Finite s")
  apply (simp add: Cut_nil)
  apply (rule Cut_nil [symmetric])
  apply (simp add: ForallMap o_def)
  apply (simp add: Map2Finite)
  text \<open>case \<open>\<not> Finite s\<close>\<close>
  apply (simp add: Cut_UU)
  apply (rule Cut_UU)
  apply (simp add: ForallMap o_def)
  apply (simp add: Map2Finite)
  text \<open>main case\<close>
  apply (simp add: Cut_Cons MapConc ForallMap FiniteMap1 o_def)
  apply (rule take_reduction)
  apply auto
  done

lemma Cut_prefixcl_nFinite [rule_format]: "\<not> Finite s \<longrightarrow> Cut P s \<sqsubseteq> s"
  apply (intro strip)
  apply (rule take_lemma_less [THEN iffD1])
  apply (intro strip)
  apply (rule mp)
  prefer 2
  apply assumption
  apply (tactic "thin_tac' \<^context> 1 1")
  apply (rule_tac x = "s" in spec)
  apply (rule nat_less_induct)
  apply (intro strip)
  apply (rename_tac na n s)
  apply (case_tac "Forall (\<lambda>x. \<not> P x) s")
  apply (rule take_lemma_less [THEN iffD2, THEN spec])
  apply (simp add: Cut_UU)
  text \<open>main case\<close>
  apply (drule divide_Seq3)
  apply (erule exE)+
  apply (erule conjE)+
  apply hypsubst
  apply (simp add: Cut_Cons)
  apply (rule take_reduction_less)
  text \<open>auto makes also reasoning about Finiteness of parts of \<open>s\<close>!\<close>
  apply auto
  done

lemma execThruCut: "is_exec_frag A (s, ex) \<Longrightarrow> is_exec_frag A (s, Cut P ex)"
  apply (case_tac "Finite ex")
  apply (cut_tac s = "ex" and P = "P" in Cut_prefixcl_Finite)
  apply assumption
  apply (erule exE)
  apply (rule exec_prefix2closed)
  apply (erule_tac s = "ex" and t = "Cut P ex @@ y" in subst)
  apply assumption
  apply (erule exec_prefixclosed)
  apply (erule Cut_prefixcl_nFinite)
  done


subsection \<open>Main Cut Theorem\<close>

lemma exists_LastActExtsch:
  "sch \<in> schedules A \<Longrightarrow> tr = Filter (\<lambda>a. a \<in> ext A) \<cdot> sch \<Longrightarrow>
    \<exists>sch. sch \<in> schedules A \<and> tr = Filter (\<lambda>a. a \<in> ext A) \<cdot> sch \<and> LastActExtsch A sch"
  apply (unfold schedules_def has_schedule_def [abs_def])
  apply auto
  apply (rule_tac x = "filter_act \<cdot> (Cut (\<lambda>a. fst a \<in> ext A) (snd ex))" in exI)
  apply (simp add: executions_def)
  apply (pair ex)
  apply auto
  apply (rule_tac x = "(x1, Cut (\<lambda>a. fst a \<in> ext A) x2)" in exI)
  apply simp

  text \<open>Subgoal 1: Lemma:  propagation of execution through \<open>Cut\<close>\<close>
  apply (simp add: execThruCut)

  text \<open>Subgoal 2:  Lemma:  \<open>Filter P s = Filter P (Cut P s)\<close>\<close>
  apply (simp add: filter_act_def)
  apply (subgoal_tac "Map fst \<cdot> (Cut (\<lambda>a. fst a \<in> ext A) x2) = Cut (\<lambda>a. a \<in> ext A) (Map fst \<cdot> x2)")
  apply (rule_tac [2] MapCut [unfolded o_def])
  apply (simp add: FilterCut [symmetric])

  text \<open>Subgoal 3: Lemma: \<open>Cut\<close> idempotent\<close>
  apply (simp add: LastActExtsch_def filter_act_def)
  apply (subgoal_tac "Map fst \<cdot> (Cut (\<lambda>a. fst a \<in> ext A) x2) = Cut (\<lambda>a. a \<in> ext A) (Map fst \<cdot> x2)")
  apply (rule_tac [2] MapCut [unfolded o_def])
  apply (simp add: Cut_idemp)
  done


subsection \<open>Further Cut lemmas\<close>

lemma LastActExtimplnil: "LastActExtsch A sch \<Longrightarrow> Filter (\<lambda>x. x \<in> ext A) \<cdot> sch = nil \<Longrightarrow> sch = nil"
  apply (unfold LastActExtsch_def)
  apply (drule FilternPnilForallP)
  apply (erule conjE)
  apply (drule Cut_nil)
  apply assumption
  apply simp
  done

lemma LastActExtimplUU: "LastActExtsch A sch \<Longrightarrow> Filter (\<lambda>x. x \<in> ext A) \<cdot> sch = UU \<Longrightarrow> sch = UU"
  apply (unfold LastActExtsch_def)
  apply (drule FilternPUUForallP)
  apply (erule conjE)
  apply (drule Cut_UU)
  apply assumption
  apply simp
  done

end
