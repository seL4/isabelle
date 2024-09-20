(*  Title:      HOL/HOLCF/IOA/Automata.thy
    Author:     Olaf Müller, Konrad Slind, Tobias Nipkow
*)

section \<open>The I/O automata of Lynch and Tuttle in HOLCF\<close>

theory Automata
imports Asig
begin

default_sort type

type_synonym ('a, 's) transition = "'s \<times> 'a \<times> 's"
type_synonym ('a, 's) ioa =
  "'a signature \<times> 's set \<times> ('a, 's)transition set \<times> 'a set set \<times> 'a set set"


subsection \<open>IO automata\<close>

definition asig_of :: "('a, 's) ioa \<Rightarrow> 'a signature"
  where "asig_of = fst"

definition starts_of :: "('a, 's) ioa \<Rightarrow> 's set"
  where "starts_of = fst \<circ> snd"

definition trans_of :: "('a, 's) ioa \<Rightarrow> ('a, 's) transition set"
  where "trans_of = fst \<circ> snd \<circ> snd"

abbreviation trans_of_syn  (\<open>_ \<midarrow>_\<midarrow>_\<rightarrow> _\<close> [81, 81, 81, 81] 100)
  where "s \<midarrow>a\<midarrow>A\<rightarrow> t \<equiv> (s, a, t) \<in> trans_of A"

definition wfair_of :: "('a, 's) ioa \<Rightarrow> 'a set set"
  where "wfair_of = fst \<circ> snd \<circ> snd \<circ> snd"

definition sfair_of :: "('a, 's) ioa \<Rightarrow> 'a set set"
  where "sfair_of = snd \<circ> snd \<circ> snd \<circ> snd"

definition is_asig_of :: "('a, 's) ioa \<Rightarrow> bool"
  where "is_asig_of A = is_asig (asig_of A)"

definition is_starts_of :: "('a, 's) ioa \<Rightarrow> bool"
  where "is_starts_of A \<longleftrightarrow> starts_of A \<noteq> {}"

definition is_trans_of :: "('a, 's) ioa \<Rightarrow> bool"
  where "is_trans_of A \<longleftrightarrow>
    (\<forall>triple. triple \<in> trans_of A \<longrightarrow> fst (snd triple) \<in> actions (asig_of A))"

definition input_enabled :: "('a, 's) ioa \<Rightarrow> bool"
  where "input_enabled A \<longleftrightarrow>
    (\<forall>a. a \<in> inputs (asig_of A) \<longrightarrow> (\<forall>s1. \<exists>s2. (s1, a, s2) \<in> trans_of A))"

definition IOA :: "('a, 's) ioa \<Rightarrow> bool"
  where "IOA A \<longleftrightarrow>
    is_asig_of A \<and>
    is_starts_of A \<and>
    is_trans_of A \<and>
    input_enabled A"

abbreviation "act A \<equiv> actions (asig_of A)"
abbreviation "ext A \<equiv> externals (asig_of A)"
abbreviation int where "int A \<equiv> internals (asig_of A)"
abbreviation "inp A \<equiv> inputs (asig_of A)"
abbreviation "out A \<equiv> outputs (asig_of A)"
abbreviation "local A \<equiv> locals (asig_of A)"


text \<open>invariants\<close>

inductive reachable :: "('a, 's) ioa \<Rightarrow> 's \<Rightarrow> bool" for C :: "('a, 's) ioa"
where
  reachable_0:  "s \<in> starts_of C \<Longrightarrow> reachable C s"
| reachable_n:  "reachable C s \<Longrightarrow> (s, a, t) \<in> trans_of C \<Longrightarrow> reachable C t"

definition invariant :: "[('a, 's) ioa, 's \<Rightarrow> bool] \<Rightarrow> bool"
  where "invariant A P \<longleftrightarrow> (\<forall>s. reachable A s \<longrightarrow> P s)"


subsection \<open>Parallel composition\<close>

subsubsection \<open>Binary composition of action signatures and automata\<close>

definition compatible :: "('a, 's) ioa \<Rightarrow> ('a, 't) ioa \<Rightarrow> bool"
  where "compatible A B \<longleftrightarrow>
    out A \<inter> out B = {} \<and>
    int A \<inter> act B = {} \<and>
    int B \<inter> act A = {}"

definition asig_comp :: "'a signature \<Rightarrow> 'a signature \<Rightarrow> 'a signature"
  where "asig_comp a1 a2 =
     (((inputs a1 \<union> inputs a2) - (outputs a1 \<union> outputs a2),
       (outputs a1 \<union> outputs a2),
       (internals a1 \<union> internals a2)))"

definition par :: "('a, 's) ioa \<Rightarrow> ('a, 't) ioa \<Rightarrow> ('a, 's * 't) ioa"  (infixr \<open>\<parallel>\<close> 10)
  where "(A \<parallel> B) =
    (asig_comp (asig_of A) (asig_of B),
     {pr. fst pr \<in> starts_of A \<and> snd pr \<in> starts_of B},
     {tr.
        let
          s = fst tr;
          a = fst (snd tr);
          t = snd (snd tr)
        in
          (a \<in> act A \<or> a \<in> act B) \<and>
          (if a \<in> act A then (fst s, a, fst t) \<in> trans_of A
           else fst t = fst s) \<and>
          (if a \<in> act B then (snd s, a, snd t) \<in> trans_of B
           else snd t = snd s)},
      wfair_of A \<union> wfair_of B,
      sfair_of A \<union> sfair_of B)"


subsection \<open>Hiding\<close>

subsubsection \<open>Hiding and restricting\<close>

definition restrict_asig :: "'a signature \<Rightarrow> 'a set \<Rightarrow> 'a signature"
  where "restrict_asig asig actns =
    (inputs asig \<inter> actns,
     outputs asig \<inter> actns,
     internals asig \<union> (externals asig - actns))"

text \<open>
  Notice that for \<open>wfair_of\<close> and \<open>sfair_of\<close> nothing has to be changed, as
  changes from the outputs to the internals does not touch the locals as a
  whole, which is of importance for fairness only.
\<close>
definition restrict :: "('a, 's) ioa \<Rightarrow> 'a set \<Rightarrow> ('a, 's) ioa"
  where "restrict A actns =
    (restrict_asig (asig_of A) actns,
     starts_of A,
     trans_of A,
     wfair_of A,
     sfair_of A)"

definition hide_asig :: "'a signature \<Rightarrow> 'a set \<Rightarrow> 'a signature"
  where "hide_asig asig actns =
    (inputs asig - actns,
     outputs asig - actns,
     internals asig \<union> actns)"

definition hide :: "('a, 's) ioa \<Rightarrow> 'a set \<Rightarrow> ('a, 's) ioa"
  where "hide A actns =
    (hide_asig (asig_of A) actns,
     starts_of A,
     trans_of A,
     wfair_of A,
     sfair_of A)"


subsection \<open>Renaming\<close>

definition rename_set :: "'a set \<Rightarrow> ('c \<Rightarrow> 'a option) \<Rightarrow> 'c set"
  where "rename_set A ren = {b. \<exists>x. Some x = ren b \<and> x \<in> A}"

definition rename :: "('a, 'b) ioa \<Rightarrow> ('c \<Rightarrow> 'a option) \<Rightarrow> ('c, 'b) ioa"
  where "rename ioa ren =
    ((rename_set (inp ioa) ren,
      rename_set (out ioa) ren,
      rename_set (int ioa) ren),
     starts_of ioa,
     {tr.
        let
          s = fst tr;
          a = fst (snd tr);
          t = snd (snd tr)
        in \<exists>x. Some x = ren a \<and> s \<midarrow>x\<midarrow>ioa\<rightarrow> t},
     {rename_set s ren | s. s \<in> wfair_of ioa},
     {rename_set s ren | s. s \<in> sfair_of ioa})"


subsection \<open>Fairness\<close>

subsubsection \<open>Enabledness of actions and action sets\<close>

definition enabled :: "('a, 's) ioa \<Rightarrow> 'a \<Rightarrow> 's \<Rightarrow> bool"
  where "enabled A a s \<longleftrightarrow> (\<exists>t. s \<midarrow>a\<midarrow>A\<rightarrow> t)"

definition Enabled :: "('a, 's) ioa \<Rightarrow> 'a set \<Rightarrow> 's \<Rightarrow> bool"
  where "Enabled A W s \<longleftrightarrow> (\<exists>w \<in> W. enabled A w s)"


text \<open>Action set keeps enabled until probably disabled by itself.\<close>

definition en_persistent :: "('a, 's) ioa \<Rightarrow> 'a set \<Rightarrow> bool"
  where "en_persistent A W \<longleftrightarrow>
    (\<forall>s a t. Enabled A W s \<and> a \<notin> W \<and> s \<midarrow>a\<midarrow>A\<rightarrow> t \<longrightarrow> Enabled A W t)"


text \<open>Post conditions for actions and action sets.\<close>

definition was_enabled :: "('a, 's) ioa \<Rightarrow> 'a \<Rightarrow> 's \<Rightarrow> bool"
  where "was_enabled A a t \<longleftrightarrow> (\<exists>s. s \<midarrow>a\<midarrow>A\<rightarrow> t)"

definition set_was_enabled :: "('a, 's) ioa \<Rightarrow> 'a set \<Rightarrow> 's \<Rightarrow> bool"
  where "set_was_enabled A W t \<longleftrightarrow> (\<exists>w \<in> W. was_enabled A w t)"


text \<open>Constraints for fair IOA.\<close>

definition fairIOA :: "('a, 's) ioa \<Rightarrow> bool"
  where "fairIOA A \<longleftrightarrow> (\<forall>S \<in> wfair_of A. S \<subseteq> local A) \<and> (\<forall>S \<in> sfair_of A. S \<subseteq> local A)"

definition input_resistant :: "('a, 's) ioa \<Rightarrow> bool"
  where "input_resistant A \<longleftrightarrow>
    (\<forall>W \<in> sfair_of A. \<forall>s a t.
      reachable A s \<and> reachable A t \<and> a \<in> inp A \<and>
      Enabled A W s \<and> s \<midarrow>a\<midarrow>A\<rightarrow> t \<longrightarrow> Enabled A W t)"


declare split_paired_Ex [simp del]

lemmas ioa_projections = asig_of_def starts_of_def trans_of_def wfair_of_def sfair_of_def


subsection "\<open>asig_of\<close>, \<open>starts_of\<close>, \<open>trans_of\<close>"

lemma ioa_triple_proj:
  "asig_of (x, y, z, w, s) = x \<and>
   starts_of (x, y, z, w, s) = y \<and>
   trans_of (x, y, z, w, s) = z \<and>
   wfair_of (x, y, z, w, s) = w \<and>
   sfair_of (x, y, z, w, s) = s"
  by (simp add: ioa_projections)

lemma trans_in_actions: "is_trans_of A \<Longrightarrow> s1 \<midarrow>a\<midarrow>A\<rightarrow> s2 \<Longrightarrow> a \<in> act A"
  by (auto simp add: is_trans_of_def actions_def is_asig_def)

lemma starts_of_par: "starts_of (A \<parallel> B) = {p. fst p \<in> starts_of A \<and> snd p \<in> starts_of B}"
  by (simp add: par_def ioa_projections)

lemma trans_of_par:
  "trans_of(A \<parallel> B) =
    {tr.
      let
        s = fst tr;
        a = fst (snd tr);
        t = snd (snd tr)
      in
        (a \<in> act A \<or> a \<in> act B) \<and>
        (if a \<in> act A then (fst s, a, fst t) \<in> trans_of A
         else fst t = fst s) \<and>
        (if a \<in> act B then (snd s, a, snd t) \<in> trans_of B
         else snd t = snd s)}"
  by (simp add: par_def ioa_projections)


subsection \<open>\<open>actions\<close> and \<open>par\<close>\<close>

lemma actions_asig_comp: "actions (asig_comp a b) = actions a \<union> actions b"
  by (auto simp add: actions_def asig_comp_def asig_projections)

lemma asig_of_par: "asig_of(A \<parallel> B) = asig_comp (asig_of A) (asig_of B)"
  by (simp add: par_def ioa_projections)

lemma externals_of_par: "ext (A1 \<parallel> A2) = ext A1 \<union> ext A2"
  by (auto simp add: externals_def asig_of_par asig_comp_def
    asig_inputs_def asig_outputs_def Un_def set_diff_eq)

lemma actions_of_par: "act (A1 \<parallel> A2) = act A1 \<union> act A2"
  by (auto simp add: actions_def asig_of_par asig_comp_def
    asig_inputs_def asig_outputs_def asig_internals_def Un_def set_diff_eq)

lemma inputs_of_par: "inp (A1 \<parallel> A2) = (inp A1 \<union> inp A2) - (out A1 \<union> out A2)"
  by (simp add: actions_def asig_of_par asig_comp_def
    asig_inputs_def asig_outputs_def Un_def set_diff_eq)

lemma outputs_of_par: "out (A1 \<parallel> A2) = out A1 \<union> out A2"
  by (simp add: actions_def asig_of_par asig_comp_def
    asig_outputs_def Un_def set_diff_eq)

lemma internals_of_par: "int (A1 \<parallel> A2) = int A1 \<union> int A2"
  by (simp add: actions_def asig_of_par asig_comp_def
    asig_inputs_def asig_outputs_def asig_internals_def Un_def set_diff_eq)


subsection \<open>Actions and compatibility\<close>

lemma compat_commute: "compatible A B = compatible B A"
  by (auto simp add: compatible_def Int_commute)

lemma ext1_is_not_int2: "compatible A1 A2 \<Longrightarrow> a \<in> ext A1 \<Longrightarrow> a \<notin> int A2"
  by (auto simp add: externals_def actions_def compatible_def)

(*just commuting the previous one: better commute compatible*)
lemma ext2_is_not_int1: "compatible A2 A1 \<Longrightarrow> a \<in> ext A1 \<Longrightarrow> a \<notin> int A2"
  by (auto simp add: externals_def actions_def compatible_def)

lemmas ext1_ext2_is_not_act2 = ext1_is_not_int2 [THEN int_and_ext_is_act]
lemmas ext1_ext2_is_not_act1 = ext2_is_not_int1 [THEN int_and_ext_is_act]

lemma intA_is_not_extB: "compatible A B \<Longrightarrow> x \<in> int A \<Longrightarrow> x \<notin> ext B"
  by (auto simp add: externals_def actions_def compatible_def)

lemma intA_is_not_actB: "compatible A B \<Longrightarrow> a \<in> int A \<Longrightarrow> a \<notin> act B"
  by (auto simp add: externals_def actions_def compatible_def is_asig_def asig_of_def)

(*the only one that needs disjointness of outputs and of internals and _all_ acts*)
lemma outAactB_is_inpB: "compatible A B \<Longrightarrow> a \<in> out A \<Longrightarrow> a \<in> act B \<Longrightarrow> a \<in> inp B"
  by (auto simp add: asig_outputs_def asig_internals_def actions_def asig_inputs_def
      compatible_def is_asig_def asig_of_def)

(*needed for propagation of input_enabledness from A, B to A \<parallel> B*)
lemma inpAAactB_is_inpBoroutB:
  "compatible A B \<Longrightarrow> a \<in> inp A \<Longrightarrow> a \<in> act B \<Longrightarrow> a \<in> inp B \<or> a \<in> out B"
  by (auto simp add: asig_outputs_def asig_internals_def actions_def asig_inputs_def
      compatible_def is_asig_def asig_of_def)


subsection \<open>Input enabledness and par\<close>

(*ugly case distinctions. Heart of proof:
    1. inpAAactB_is_inpBoroutB ie. internals are really hidden.
    2. inputs_of_par: outputs are no longer inputs of par. This is important here.*)
lemma input_enabled_par:
  "compatible A B \<Longrightarrow> input_enabled A \<Longrightarrow> input_enabled B \<Longrightarrow> input_enabled (A \<parallel> B)"
  apply (unfold input_enabled_def)
  apply (simp add: Let_def inputs_of_par trans_of_par)
  apply (tactic "safe_tac (Context.raw_transfer \<^theory> \<^theory_context>\<open>Fun\<close>)")
  apply (simp add: inp_is_act)
  prefer 2
  apply (simp add: inp_is_act)
  text \<open>\<open>a \<in> inp A\<close>\<close>
  apply (case_tac "a \<in> act B")
  text \<open>\<open>a \<in> inp B\<close>\<close>
  apply (erule_tac x = "a" in allE)
  apply simp
  apply (drule inpAAactB_is_inpBoroutB)
  apply assumption
  apply assumption
  apply (erule_tac x = "a" in allE)
  apply simp
  apply (erule_tac x = "aa" in allE)
  apply (erule_tac x = "b" in allE)
  apply (erule exE)
  apply (erule exE)
  apply (rule_tac x = "(s2, s2a)" in exI)
  apply (simp add: inp_is_act)
  text \<open>\<open>a \<notin> act B\<close>\<close>
  apply (simp add: inp_is_act)
  apply (erule_tac x = "a" in allE)
  apply simp
  apply (erule_tac x = "aa" in allE)
  apply (erule exE)
  apply (rule_tac x = " (s2,b) " in exI)
  apply simp

  text \<open>\<open>a \<in> inp B\<close>\<close>
  apply (case_tac "a \<in> act A")
  text \<open>\<open>a \<in> act A\<close>\<close>
  apply (erule_tac x = "a" in allE)
  apply (erule_tac x = "a" in allE)
  apply (simp add: inp_is_act)
  apply (frule_tac A1 = "A" in compat_commute [THEN iffD1])
  apply (drule inpAAactB_is_inpBoroutB)
  back
  apply assumption
  apply assumption
  apply simp
  apply (erule_tac x = "aa" in allE)
  apply (erule_tac x = "b" in allE)
  apply (erule exE)
  apply (erule exE)
  apply (rule_tac x = "(s2, s2a)" in exI)
  apply (simp add: inp_is_act)
  text \<open>\<open>a \<notin> act B\<close>\<close>
  apply (simp add: inp_is_act)
  apply (erule_tac x = "a" in allE)
  apply (erule_tac x = "a" in allE)
  apply simp
  apply (erule_tac x = "b" in allE)
  apply (erule exE)
  apply (rule_tac x = "(aa, s2)" in exI)
  apply simp
  done


subsection \<open>Invariants\<close>

lemma invariantI:
  assumes "\<And>s. s \<in> starts_of A \<Longrightarrow> P s"
    and "\<And>s t a. reachable A s \<Longrightarrow> P s \<Longrightarrow> (s, a, t) \<in> trans_of A \<longrightarrow> P t"
  shows "invariant A P"
  using assms
  apply (unfold invariant_def)
  apply (rule allI)
  apply (rule impI)
  apply (rule_tac x = "s" in reachable.induct)
  apply assumption
  apply blast
  apply blast
  done

lemma invariantI1:
  assumes "\<And>s. s \<in> starts_of A \<Longrightarrow> P s"
    and "\<And>s t a. reachable A s \<Longrightarrow> P s \<longrightarrow> (s, a, t) \<in> trans_of A \<longrightarrow> P t"
  shows "invariant A P"
  using assms by (blast intro: invariantI)

lemma invariantE: "invariant A P \<Longrightarrow> reachable A s \<Longrightarrow> P s"
  unfolding invariant_def by blast


subsection \<open>\<open>restrict\<close>\<close>

lemmas reachable_0 = reachable.reachable_0
  and reachable_n = reachable.reachable_n

lemma cancel_restrict_a:
  "starts_of (restrict ioa acts) = starts_of ioa \<and>
   trans_of (restrict ioa acts) = trans_of ioa"
  by (simp add: restrict_def ioa_projections)

lemma cancel_restrict_b: "reachable (restrict ioa acts) s = reachable ioa s"
  apply (rule iffI)
  apply (erule reachable.induct)
  apply (simp add: cancel_restrict_a reachable_0)
  apply (erule reachable_n)
  apply (simp add: cancel_restrict_a)
  text \<open>\<open>\<longleftarrow>\<close>\<close>
  apply (erule reachable.induct)
  apply (rule reachable_0)
  apply (simp add: cancel_restrict_a)
  apply (erule reachable_n)
  apply (simp add: cancel_restrict_a)
  done

lemma acts_restrict: "act (restrict A acts) = act A"
  by (auto simp add: actions_def asig_internals_def
    asig_outputs_def asig_inputs_def externals_def asig_of_def restrict_def restrict_asig_def)

lemma cancel_restrict:
  "starts_of (restrict ioa acts) = starts_of ioa \<and>
   trans_of (restrict ioa acts) = trans_of ioa \<and>
   reachable (restrict ioa acts) s = reachable ioa s \<and>
   act (restrict A acts) = act A"
  by (simp add: cancel_restrict_a cancel_restrict_b acts_restrict)


subsection \<open>\<open>rename\<close>\<close>

lemma trans_rename: "s \<midarrow>a\<midarrow>(rename C f)\<rightarrow> t \<Longrightarrow> (\<exists>x. Some x = f a \<and> s \<midarrow>x\<midarrow>C\<rightarrow> t)"
  by (simp add: Let_def rename_def trans_of_def)

lemma reachable_rename: "reachable (rename C g) s \<Longrightarrow> reachable C s"
  apply (erule reachable.induct)
  apply (rule reachable_0)
  apply (simp add: rename_def ioa_projections)
  apply (drule trans_rename)
  apply (erule exE)
  apply (erule conjE)
  apply (erule reachable_n)
  apply assumption
  done


subsection \<open>\<open>trans_of (A \<parallel> B)\<close>\<close>

lemma trans_A_proj:
  "(s, a, t) \<in> trans_of (A \<parallel> B) \<Longrightarrow> a \<in> act A \<Longrightarrow> (fst s, a, fst t) \<in> trans_of A"
  by (simp add: Let_def par_def trans_of_def)

lemma trans_B_proj:
  "(s, a, t) \<in> trans_of (A \<parallel> B) \<Longrightarrow> a \<in> act B \<Longrightarrow> (snd s, a, snd t) \<in> trans_of B"
  by (simp add: Let_def par_def trans_of_def)

lemma trans_A_proj2: "(s, a, t) \<in> trans_of (A \<parallel> B) \<Longrightarrow> a \<notin> act A \<Longrightarrow> fst s = fst t"
  by (simp add: Let_def par_def trans_of_def)

lemma trans_B_proj2: "(s, a, t) \<in> trans_of (A \<parallel> B) \<Longrightarrow> a \<notin> act B \<Longrightarrow> snd s = snd t"
  by (simp add: Let_def par_def trans_of_def)

lemma trans_AB_proj: "(s, a, t) \<in> trans_of (A \<parallel> B) \<Longrightarrow> a \<in> act A \<or> a \<in> act B"
  by (simp add: Let_def par_def trans_of_def)

lemma trans_AB:
  "a \<in> act A \<Longrightarrow> a \<in> act B \<Longrightarrow>
  (fst s, a, fst t) \<in> trans_of A \<Longrightarrow>
  (snd s, a, snd t) \<in> trans_of B \<Longrightarrow>
  (s, a, t) \<in> trans_of (A \<parallel> B)"
  by (simp add: Let_def par_def trans_of_def)

lemma trans_A_notB:
  "a \<in> act A \<Longrightarrow> a \<notin> act B \<Longrightarrow>
  (fst s, a, fst t) \<in> trans_of A \<Longrightarrow>
  snd s = snd t \<Longrightarrow>
  (s, a, t) \<in> trans_of (A \<parallel> B)"
  by (simp add: Let_def par_def trans_of_def)

lemma trans_notA_B:
  "a \<notin> act A \<Longrightarrow> a \<in> act B \<Longrightarrow>
  (snd s, a, snd t) \<in> trans_of B \<Longrightarrow>
  fst s = fst t \<Longrightarrow>
  (s, a, t) \<in> trans_of (A \<parallel> B)"
  by (simp add: Let_def par_def trans_of_def)

lemmas trans_of_defs1 = trans_AB trans_A_notB trans_notA_B
  and trans_of_defs2 = trans_A_proj trans_B_proj trans_A_proj2 trans_B_proj2 trans_AB_proj


lemma trans_of_par4:
  "(s, a, t) \<in> trans_of (A \<parallel> B \<parallel> C \<parallel> D) \<longleftrightarrow>
    ((a \<in> actions (asig_of A) \<or> a \<in> actions (asig_of B) \<or> a \<in> actions (asig_of C) \<or>
      a \<in> actions (asig_of D)) \<and>
     (if a \<in> actions (asig_of A)
      then (fst s, a, fst t) \<in> trans_of A
      else fst t = fst s) \<and>
     (if a \<in> actions (asig_of B)
      then (fst (snd s), a, fst (snd t)) \<in> trans_of B
      else fst (snd t) = fst (snd s)) \<and>
     (if a \<in> actions (asig_of C)
      then (fst (snd (snd s)), a, fst (snd (snd t))) \<in> trans_of C
      else fst (snd (snd t)) = fst (snd (snd s))) \<and>
     (if a \<in> actions (asig_of D)
      then (snd (snd (snd s)), a, snd (snd (snd t))) \<in> trans_of D
      else snd (snd (snd t)) = snd (snd (snd s))))"
  by (simp add: par_def actions_asig_comp prod_eq_iff Let_def ioa_projections)


subsection \<open>Proof obligation generator for IOA requirements\<close>

(*without assumptions on A and B because is_trans_of is also incorporated in par_def*)
lemma is_trans_of_par: "is_trans_of (A \<parallel> B)"
  by (simp add: is_trans_of_def Let_def actions_of_par trans_of_par)

lemma is_trans_of_restrict: "is_trans_of A \<Longrightarrow> is_trans_of (restrict A acts)"
  by (simp add: is_trans_of_def cancel_restrict acts_restrict)

lemma is_trans_of_rename: "is_trans_of A \<Longrightarrow> is_trans_of (rename A f)"
  apply (unfold is_trans_of_def restrict_def restrict_asig_def)
  apply (simp add: Let_def actions_def trans_of_def asig_internals_def
    asig_outputs_def asig_inputs_def externals_def asig_of_def rename_def rename_set_def)
  apply blast
  done

lemma is_asig_of_par: "is_asig_of A \<Longrightarrow> is_asig_of B \<Longrightarrow> compatible A B \<Longrightarrow> is_asig_of (A \<parallel> B)"
  apply (simp add: is_asig_of_def asig_of_par asig_comp_def compatible_def
    asig_internals_def asig_outputs_def asig_inputs_def actions_def is_asig_def)
  apply (simp add: asig_of_def)
  apply auto
  done

lemma is_asig_of_restrict: "is_asig_of A \<Longrightarrow> is_asig_of (restrict A f)"
  apply (unfold is_asig_of_def is_asig_def asig_of_def restrict_def restrict_asig_def
    asig_internals_def asig_outputs_def asig_inputs_def externals_def o_def)
  apply simp
  apply auto
  done

lemma is_asig_of_rename: "is_asig_of A \<Longrightarrow> is_asig_of (rename A f)"
  apply (simp add: is_asig_of_def rename_def rename_set_def asig_internals_def
    asig_outputs_def asig_inputs_def actions_def is_asig_def asig_of_def)
  apply auto
  apply (drule_tac [!] s = "Some _" in sym)
  apply auto
  done

lemmas [simp] = is_asig_of_par is_asig_of_restrict
  is_asig_of_rename is_trans_of_par is_trans_of_restrict is_trans_of_rename


lemma compatible_par: "compatible A B \<Longrightarrow> compatible A C \<Longrightarrow> compatible A (B \<parallel> C)"
  by (auto simp add: compatible_def internals_of_par outputs_of_par actions_of_par)

(*better derive by previous one and compat_commute*)
lemma compatible_par2: "compatible A C \<Longrightarrow> compatible B C \<Longrightarrow> compatible (A \<parallel> B) C"
  by (auto simp add: compatible_def internals_of_par outputs_of_par actions_of_par)

lemma compatible_restrict:
  "compatible A B \<Longrightarrow> (ext B - S) \<inter> ext A = {} \<Longrightarrow> compatible A (restrict B S)"
  by (auto simp add: compatible_def ioa_triple_proj asig_triple_proj externals_def
    restrict_def restrict_asig_def actions_def)

declare split_paired_Ex [simp]

end
