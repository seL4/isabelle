(*  Title:      HOL/HOLCF/IOA/Traces.thy
    Author:     Olaf Müller
*)

section \<open>Executions and Traces of I/O automata in HOLCF\<close>

theory Traces
imports Sequence Automata
begin

default_sort type

type_synonym ('a, 's) pairs = "('a \<times> 's) Seq"
type_synonym ('a, 's) execution = "'s \<times> ('a, 's) pairs"
type_synonym 'a trace = "'a Seq"
type_synonym ('a, 's) execution_module = "('a, 's) execution set \<times> 'a signature"
type_synonym 'a schedule_module = "'a trace set \<times> 'a signature"
type_synonym 'a trace_module = "'a trace set \<times> 'a signature"


subsection \<open>Executions\<close>

definition is_exec_fragC :: "('a, 's) ioa \<Rightarrow> ('a, 's) pairs \<rightarrow> 's \<Rightarrow> tr"
  where "is_exec_fragC A =
    (fix \<cdot>
      (LAM h ex.
        (\<lambda>s.
          case ex of
            nil \<Rightarrow> TT
          | x ## xs \<Rightarrow> flift1 (\<lambda>p. Def ((s, p) \<in> trans_of A) andalso (h \<cdot> xs) (snd p)) \<cdot> x)))"

definition is_exec_frag :: "('a, 's) ioa \<Rightarrow> ('a, 's) execution \<Rightarrow> bool"
  where "is_exec_frag A ex \<longleftrightarrow> (is_exec_fragC A \<cdot> (snd ex)) (fst ex) \<noteq> FF"

definition executions :: "('a, 's) ioa \<Rightarrow> ('a, 's) execution set"
  where "executions ioa = {e. fst e \<in> starts_of ioa \<and> is_exec_frag ioa e}"


subsection \<open>Schedules\<close>

definition filter_act :: "('a, 's) pairs \<rightarrow> 'a trace"
  where "filter_act = Map fst"

definition has_schedule :: "('a, 's) ioa \<Rightarrow> 'a trace \<Rightarrow> bool"
  where "has_schedule ioa sch \<longleftrightarrow> (\<exists>ex \<in> executions ioa. sch = filter_act \<cdot> (snd ex))"

definition schedules :: "('a, 's) ioa \<Rightarrow> 'a trace set"
  where "schedules ioa = {sch. has_schedule ioa sch}"


subsection \<open>Traces\<close>

definition has_trace :: "('a, 's) ioa \<Rightarrow> 'a trace \<Rightarrow> bool"
  where "has_trace ioa tr \<longleftrightarrow> (\<exists>sch \<in> schedules ioa. tr = Filter (\<lambda>a. a \<in> ext ioa) \<cdot> sch)"

definition traces :: "('a, 's) ioa \<Rightarrow> 'a trace set"
  where "traces ioa \<equiv> {tr. has_trace ioa tr}"

definition mk_trace :: "('a, 's) ioa \<Rightarrow> ('a, 's) pairs \<rightarrow> 'a trace"
  where "mk_trace ioa = (LAM tr. Filter (\<lambda>a. a \<in> ext ioa) \<cdot> (filter_act \<cdot> tr))"


subsection \<open>Fair Traces\<close>

definition laststate :: "('a, 's) execution \<Rightarrow> 's"
  where "laststate ex =
    (case Last \<cdot> (snd ex) of
      UU \<Rightarrow> fst ex
    | Def at \<Rightarrow> snd at)"

text \<open>A predicate holds infinitely (finitely) often in a sequence.\<close>
definition inf_often :: "('a \<Rightarrow> bool) \<Rightarrow> 'a Seq \<Rightarrow> bool"
  where "inf_often P s \<longleftrightarrow> Infinite (Filter P \<cdot> s)"

text \<open>Filtering \<open>P\<close> yields a finite or partial sequence.\<close>
definition fin_often :: "('a \<Rightarrow> bool) \<Rightarrow> 'a Seq \<Rightarrow> bool"
  where "fin_often P s \<longleftrightarrow> \<not> inf_often P s"


subsection \<open>Fairness of executions\<close>

text \<open>
  Note that partial execs cannot be \<open>wfair\<close> as the inf_often predicate in the
  else branch prohibits it. However they can be \<open>sfair\<close> in the case when all
  \<open>W\<close> are only finitely often enabled: Is this the right model?

  See \<^file>\<open>LiveIOA.thy\<close> for solution conforming with the literature and
  superseding this one.
\<close>

definition is_wfair :: "('a, 's) ioa \<Rightarrow> 'a set \<Rightarrow> ('a, 's) execution \<Rightarrow> bool"
  where "is_wfair A W ex \<longleftrightarrow>
    (inf_often (\<lambda>x. fst x \<in> W) (snd ex) \<or>
      inf_often (\<lambda>x. \<not> Enabled A W (snd x)) (snd ex))"

definition wfair_ex :: "('a, 's) ioa \<Rightarrow> ('a, 's) execution \<Rightarrow> bool"
  where "wfair_ex A ex \<longleftrightarrow>
    (\<forall>W \<in> wfair_of A.
      if Finite (snd ex)
      then \<not> Enabled A W (laststate ex)
      else is_wfair A W ex)"

definition is_sfair :: "('a, 's) ioa \<Rightarrow> 'a set \<Rightarrow> ('a, 's) execution \<Rightarrow> bool"
  where "is_sfair A W ex \<longleftrightarrow>
    (inf_often (\<lambda>x. fst x \<in> W) (snd ex) \<or>
      fin_often (\<lambda>x. Enabled A W (snd x)) (snd ex))"

definition sfair_ex :: "('a, 's)ioa \<Rightarrow> ('a, 's) execution \<Rightarrow> bool"
  where "sfair_ex A ex \<longleftrightarrow>
    (\<forall>W \<in> sfair_of A.
      if Finite (snd ex)
      then \<not> Enabled A W (laststate ex)
      else is_sfair A W ex)"

definition fair_ex :: "('a, 's) ioa \<Rightarrow> ('a, 's) execution \<Rightarrow> bool"
  where "fair_ex A ex \<longleftrightarrow> wfair_ex A ex \<and> sfair_ex A ex"


text \<open>Fair behavior sets.\<close>

definition fairexecutions :: "('a, 's) ioa \<Rightarrow> ('a, 's) execution set"
  where "fairexecutions A = {ex. ex \<in> executions A \<and> fair_ex A ex}"

definition fairtraces :: "('a, 's) ioa \<Rightarrow> 'a trace set"
  where "fairtraces A = {mk_trace A \<cdot> (snd ex) | ex. ex \<in> fairexecutions A}"


subsection \<open>Implementation\<close>

subsubsection \<open>Notions of implementation\<close>

definition ioa_implements :: "('a, 's1) ioa \<Rightarrow> ('a, 's2) ioa \<Rightarrow> bool"  (infixr \<open>=<|\<close> 12)
  where "(ioa1 =<| ioa2) \<longleftrightarrow>
    (inputs (asig_of ioa1) = inputs (asig_of ioa2) \<and>
     outputs (asig_of ioa1) = outputs (asig_of ioa2)) \<and>
    traces ioa1 \<subseteq> traces ioa2"

definition fair_implements :: "('a, 's1) ioa \<Rightarrow> ('a, 's2) ioa \<Rightarrow> bool"
  where "fair_implements C A \<longleftrightarrow>
    inp C = inp A \<and> out C = out A \<and> fairtraces C \<subseteq> fairtraces A"

lemma implements_trans: "A =<| B \<Longrightarrow> B =<| C \<Longrightarrow> A =<| C"
  by (auto simp add: ioa_implements_def)


subsection \<open>Modules\<close>

subsubsection \<open>Execution, schedule and trace modules\<close>

definition Execs :: "('a, 's) ioa \<Rightarrow> ('a, 's) execution_module"
  where "Execs A = (executions A, asig_of A)"

definition Scheds :: "('a, 's) ioa \<Rightarrow> 'a schedule_module"
  where "Scheds A = (schedules A, asig_of A)"

definition Traces :: "('a, 's) ioa \<Rightarrow> 'a trace_module"
  where "Traces A = (traces A, asig_of A)"

lemmas [simp del] = HOL.ex_simps HOL.all_simps split_paired_Ex
declare Let_def [simp]
setup \<open>map_theory_claset (fn ctxt => ctxt delSWrapper "split_all_tac")\<close>

lemmas exec_rws = executions_def is_exec_frag_def


subsection \<open>Recursive equations of operators\<close>

subsubsection \<open>\<open>filter_act\<close>\<close>

lemma filter_act_UU: "filter_act \<cdot> UU = UU"
  by (simp add: filter_act_def)

lemma filter_act_nil: "filter_act \<cdot> nil = nil"
  by (simp add: filter_act_def)

lemma filter_act_cons: "filter_act \<cdot> (x \<leadsto> xs) = fst x \<leadsto> filter_act \<cdot> xs"
  by (simp add: filter_act_def)

declare filter_act_UU [simp] filter_act_nil [simp] filter_act_cons [simp]


subsubsection \<open>\<open>mk_trace\<close>\<close>

lemma mk_trace_UU: "mk_trace A \<cdot> UU = UU"
  by (simp add: mk_trace_def)

lemma mk_trace_nil: "mk_trace A \<cdot> nil = nil"
  by (simp add: mk_trace_def)

lemma mk_trace_cons:
  "mk_trace A \<cdot> (at \<leadsto> xs) =
    (if fst at \<in> ext A
     then fst at \<leadsto> mk_trace A \<cdot> xs
     else mk_trace A \<cdot> xs)"
  by (simp add: mk_trace_def)

declare mk_trace_UU [simp] mk_trace_nil [simp] mk_trace_cons [simp]


subsubsection \<open>\<open>is_exec_fragC\<close>\<close>

lemma is_exec_fragC_unfold:
  "is_exec_fragC A =
    (LAM ex.
      (\<lambda>s.
        case ex of
          nil \<Rightarrow> TT
        | x ## xs \<Rightarrow>
            (flift1 (\<lambda>p. Def ((s, p) \<in> trans_of A) andalso (is_exec_fragC A\<cdot>xs) (snd p)) \<cdot> x)))"
  apply (rule trans)
  apply (rule fix_eq4)
  apply (rule is_exec_fragC_def)
  apply (rule beta_cfun)
  apply (simp add: flift1_def)
  done

lemma is_exec_fragC_UU: "(is_exec_fragC A \<cdot> UU) s = UU"
  apply (subst is_exec_fragC_unfold)
  apply simp
  done

lemma is_exec_fragC_nil: "(is_exec_fragC A \<cdot> nil) s = TT"
  apply (subst is_exec_fragC_unfold)
  apply simp
  done

lemma is_exec_fragC_cons:
  "(is_exec_fragC A \<cdot> (pr \<leadsto> xs)) s =
    (Def ((s, pr) \<in> trans_of A) andalso (is_exec_fragC A \<cdot> xs) (snd pr))"
  apply (rule trans)
  apply (subst is_exec_fragC_unfold)
  apply (simp add: Consq_def flift1_def)
  apply simp
  done

declare is_exec_fragC_UU [simp] is_exec_fragC_nil [simp] is_exec_fragC_cons [simp]


subsubsection \<open>\<open>is_exec_frag\<close>\<close>

lemma is_exec_frag_UU: "is_exec_frag A (s, UU)"
  by (simp add: is_exec_frag_def)

lemma is_exec_frag_nil: "is_exec_frag A (s, nil)"
  by (simp add: is_exec_frag_def)

lemma is_exec_frag_cons:
  "is_exec_frag A (s, (a, t) \<leadsto> ex) \<longleftrightarrow> (s, a, t) \<in> trans_of A \<and> is_exec_frag A (t, ex)"
  by (simp add: is_exec_frag_def)

declare is_exec_frag_UU [simp] is_exec_frag_nil [simp] is_exec_frag_cons [simp]


subsubsection \<open>\<open>laststate\<close>\<close>

lemma laststate_UU: "laststate (s, UU) = s"
  by (simp add: laststate_def)

lemma laststate_nil: "laststate (s, nil) = s"
  by (simp add: laststate_def)

lemma laststate_cons: "Finite ex \<Longrightarrow> laststate (s, at \<leadsto> ex) = laststate (snd at, ex)"
  apply (simp add: laststate_def)
  apply (cases "ex = nil")
  apply simp
  apply simp
  apply (drule Finite_Last1 [THEN mp])
  apply assumption
  apply defined
  done

declare laststate_UU [simp] laststate_nil [simp] laststate_cons [simp]

lemma exists_laststate: "Finite ex \<Longrightarrow> \<forall>s. \<exists>u. laststate (s, ex) = u"
  by Seq_Finite_induct


subsection \<open>\<open>has_trace\<close> \<open>mk_trace\<close>\<close>

(*alternative definition of has_trace tailored for the refinement proof, as it does not
  take the detour of schedules*)
lemma has_trace_def2: "has_trace A b \<longleftrightarrow> (\<exists>ex \<in> executions A. b = mk_trace A \<cdot> (snd ex))"
  apply (unfold executions_def mk_trace_def has_trace_def schedules_def has_schedule_def [abs_def])
  apply auto
  done


subsection \<open>Signatures and executions, schedules\<close>

text \<open>
  All executions of \<open>A\<close> have only actions of \<open>A\<close>. This is only true because of
  the predicate \<open>state_trans\<close> (part of the predicate \<open>IOA\<close>): We have no
  dependent types. For executions of parallel automata this assumption is not
  needed, as in \<open>par_def\<close> this condition is included once more. (See Lemmas
  1.1.1c in CompoExecs for example.)
\<close>

lemma execfrag_in_sig:
  "is_trans_of A \<Longrightarrow> \<forall>s. is_exec_frag A (s, xs) \<longrightarrow> Forall (\<lambda>a. a \<in> act A) (filter_act \<cdot> xs)"
  apply (pair_induct xs simp: is_exec_frag_def Forall_def sforall_def)
  text \<open>main case\<close>
  apply (auto simp add: is_trans_of_def)
  done

lemma exec_in_sig:
  "is_trans_of A \<Longrightarrow> x \<in> executions A \<Longrightarrow> Forall (\<lambda>a. a \<in> act A) (filter_act \<cdot> (snd x))"
  apply (simp add: executions_def)
  apply (pair x)
  apply (rule execfrag_in_sig [THEN spec, THEN mp])
  apply auto
  done

lemma scheds_in_sig: "is_trans_of A \<Longrightarrow> x \<in> schedules A \<Longrightarrow> Forall (\<lambda>a. a \<in> act A) x"
  apply (unfold schedules_def has_schedule_def [abs_def])
  apply (fast intro!: exec_in_sig)
  done


subsection \<open>Executions are prefix closed\<close>

(*only admissible in y, not if done in x!*)
lemma execfrag_prefixclosed: "\<forall>x s. is_exec_frag A (s, x) \<and> y \<sqsubseteq> x \<longrightarrow> is_exec_frag A (s, y)"
  apply (pair_induct y simp: is_exec_frag_def)
  apply (intro strip)
  apply (Seq_case_simp x)
  apply (pair a)
  apply auto
  done

lemmas exec_prefixclosed =
  conjI [THEN execfrag_prefixclosed [THEN spec, THEN spec, THEN mp]]

(*second prefix notion for Finite x*)
lemma exec_prefix2closed [rule_format]:
  "\<forall>y s. is_exec_frag A (s, x @@ y) \<longrightarrow> is_exec_frag A (s, x)"
  apply (pair_induct x simp: is_exec_frag_def)
  apply (intro strip)
  apply (Seq_case_simp s)
  apply (pair a)
  apply auto
  done

end
