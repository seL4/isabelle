(*  Title:      HOL/Analysis/Measurable.thy
    Author:     Johannes Hölzl <hoelzl@in.tum.de>
*)
section \<open>Measurability Prover\<close>
theory Measurable
  imports
    Sigma_Algebra
    "HOL-Library.Order_Continuity"
begin


lemma (in algebra) sets_Collect_finite_All:
  assumes "\<And>i. i \<in> S \<Longrightarrow> {x\<in>\<Omega>. P i x} \<in> M" "finite S"
  shows "{x\<in>\<Omega>. \<forall>i\<in>S. P i x} \<in> M"
proof -
  have "{x\<in>\<Omega>. \<forall>i\<in>S. P i x} = (if S = {} then \<Omega> else \<Inter>i\<in>S. {x\<in>\<Omega>. P i x})"
    by auto
  with assms show ?thesis by (auto intro!: sets_Collect_finite_All')
qed

abbreviation "pred M P \<equiv> P \<in> measurable M (count_space (UNIV::bool set))"

lemma pred_def: "pred M P \<longleftrightarrow> {x\<in>space M. P x} \<in> sets M"
proof
  assume "pred M P"
  then have "P -` {True} \<inter> space M \<in> sets M"
    by (auto simp: measurable_count_space_eq2)
  also have "P -` {True} \<inter> space M = {x\<in>space M. P x}" by auto
  finally show "{x\<in>space M. P x} \<in> sets M" .
next
  assume P: "{x\<in>space M. P x} \<in> sets M"
  moreover
  { fix X
    have "X \<in> Pow (UNIV :: bool set)" by simp
    then have "P -` X \<inter> space M = {x\<in>space M. ((X = {True} \<longrightarrow> P x) \<and> (X = {False} \<longrightarrow> \<not> P x) \<and> X \<noteq> {})}"
      unfolding UNIV_bool Pow_insert Pow_empty by auto
    then have "P -` X \<inter> space M \<in> sets M"
      by (auto intro!: sets.sets_Collect_neg sets.sets_Collect_imp sets.sets_Collect_conj sets.sets_Collect_const P) }
  then show "pred M P"
    by (auto simp: measurable_def)
qed

lemma pred_sets1: "{x\<in>space M. P x} \<in> sets M \<Longrightarrow> f \<in> measurable N M \<Longrightarrow> pred N (\<lambda>x. P (f x))"
  by (rule measurable_compose[where f=f and N=M]) (auto simp: pred_def)

lemma pred_sets2: "A \<in> sets N \<Longrightarrow> f \<in> measurable M N \<Longrightarrow> pred M (\<lambda>x. f x \<in> A)"
  by (rule measurable_compose[where f=f and N=N]) (auto simp: pred_def Int_def[symmetric])

ML_file \<open>measurable.ML\<close>

attribute_setup measurable = \<open>
  Scan.lift (
    (Args.add >> K true || Args.del >> K false || Scan.succeed true) --
    Scan.optional (Args.parens (
      Scan.optional (Args.$$$ "raw" >> K true) false --
      Scan.optional (Args.$$$ "generic" >> K Measurable.Generic) Measurable.Concrete))
    (false, Measurable.Concrete) >>
    Measurable.measurable_thm_attr)
\<close> "declaration of measurability theorems"

attribute_setup measurable_dest = Measurable.dest_thm_attr
  "add dest rule to measurability prover"

attribute_setup measurable_cong = Measurable.cong_thm_attr
  "add congurence rules to measurability prover"

method_setup\<^marker>\<open>tag important\<close> measurable = \<open> Scan.lift (Scan.succeed (METHOD o Measurable.measurable_tac)) \<close>
  "measurability prover"

simproc_setup\<^marker>\<open>tag important\<close> measurable ("A \<in> sets M" | "f \<in> measurable M N") =
  \<open>K Measurable.proc\<close>

setup \<open>
  Global_Theory.add_thms_dynamic (\<^binding>\<open>measurable\<close>, Measurable.get_all)
\<close>

declare
  pred_sets1[measurable_dest]
  pred_sets2[measurable_dest]
  sets.sets_into_space[measurable_dest]

declare
  sets.top[measurable]
  sets.empty_sets[measurable (raw)]
  sets.Un[measurable (raw)]
  sets.Diff[measurable (raw)]

declare
  measurable_count_space[measurable (raw)]
  measurable_ident[measurable (raw)]
  measurable_id[measurable (raw)]
  measurable_const[measurable (raw)]
  measurable_If[measurable (raw)]
  measurable_comp[measurable (raw)]
  measurable_sets[measurable (raw)]

declare measurable_cong_sets[measurable_cong]
declare sets_restrict_space_cong[measurable_cong]
declare sets_restrict_UNIV[measurable_cong]

lemma predE[measurable (raw)]:
  "pred M P \<Longrightarrow> {x\<in>space M. P x} \<in> sets M"
  unfolding pred_def .

lemma pred_intros_imp'[measurable (raw)]:
  "(K \<Longrightarrow> pred M (\<lambda>x. P x)) \<Longrightarrow> pred M (\<lambda>x. K \<longrightarrow> P x)"
  by (cases K) auto

lemma pred_intros_conj1'[measurable (raw)]:
  "(K \<Longrightarrow> pred M (\<lambda>x. P x)) \<Longrightarrow> pred M (\<lambda>x. K \<and> P x)"
  by (cases K) auto

lemma pred_intros_conj2'[measurable (raw)]:
  "(K \<Longrightarrow> pred M (\<lambda>x. P x)) \<Longrightarrow> pred M (\<lambda>x. P x \<and> K)"
  by (cases K) auto

lemma pred_intros_disj1'[measurable (raw)]:
  "(\<not> K \<Longrightarrow> pred M (\<lambda>x. P x)) \<Longrightarrow> pred M (\<lambda>x. K \<or> P x)"
  by (cases K) auto

lemma pred_intros_disj2'[measurable (raw)]:
  "(\<not> K \<Longrightarrow> pred M (\<lambda>x. P x)) \<Longrightarrow> pred M (\<lambda>x. P x \<or> K)"
  by (cases K) auto

lemma pred_intros_logic[measurable (raw)]:
  "pred M (\<lambda>x. x \<in> space M)"
  "pred M (\<lambda>x. P x) \<Longrightarrow> pred M (\<lambda>x. \<not> P x)"
  "pred M (\<lambda>x. Q x) \<Longrightarrow> pred M (\<lambda>x. P x) \<Longrightarrow> pred M (\<lambda>x. Q x \<and> P x)"
  "pred M (\<lambda>x. Q x) \<Longrightarrow> pred M (\<lambda>x. P x) \<Longrightarrow> pred M (\<lambda>x. Q x \<longrightarrow> P x)"
  "pred M (\<lambda>x. Q x) \<Longrightarrow> pred M (\<lambda>x. P x) \<Longrightarrow> pred M (\<lambda>x. Q x \<or> P x)"
  "pred M (\<lambda>x. Q x) \<Longrightarrow> pred M (\<lambda>x. P x) \<Longrightarrow> pred M (\<lambda>x. Q x = P x)"
  "pred M (\<lambda>x. f x \<in> UNIV)"
  "pred M (\<lambda>x. f x \<in> {})"
  "pred M (\<lambda>x. P' (f x) x) \<Longrightarrow> pred M (\<lambda>x. f x \<in> {y. P' y x})"
  "pred M (\<lambda>x. f x \<in> (B x)) \<Longrightarrow> pred M (\<lambda>x. f x \<in> - (B x))"
  "pred M (\<lambda>x. f x \<in> (A x)) \<Longrightarrow> pred M (\<lambda>x. f x \<in> (B x)) \<Longrightarrow> pred M (\<lambda>x. f x \<in> (A x) - (B x))"
  "pred M (\<lambda>x. f x \<in> (A x)) \<Longrightarrow> pred M (\<lambda>x. f x \<in> (B x)) \<Longrightarrow> pred M (\<lambda>x. f x \<in> (A x) \<inter> (B x))"
  "pred M (\<lambda>x. f x \<in> (A x)) \<Longrightarrow> pred M (\<lambda>x. f x \<in> (B x)) \<Longrightarrow> pred M (\<lambda>x. f x \<in> (A x) \<union> (B x))"
  "pred M (\<lambda>x. g x (f x) \<in> (X x)) \<Longrightarrow> pred M (\<lambda>x. f x \<in> (g x) -` (X x))"
  by (auto simp: iff_conv_conj_imp pred_def)

lemma pred_intros_countable[measurable (raw)]:
  fixes P :: "'a \<Rightarrow> 'i :: countable \<Rightarrow> bool"
  shows
    "(\<And>i. pred M (\<lambda>x. P x i)) \<Longrightarrow> pred M (\<lambda>x. \<forall>i. P x i)"
    "(\<And>i. pred M (\<lambda>x. P x i)) \<Longrightarrow> pred M (\<lambda>x. \<exists>i. P x i)"
  by (auto intro!: sets.sets_Collect_countable_All sets.sets_Collect_countable_Ex simp: pred_def)

lemma pred_intros_countable_bounded[measurable (raw)]:
  fixes X :: "'i :: countable set"
  shows
    "(\<And>i. i \<in> X \<Longrightarrow> pred M (\<lambda>x. x \<in> N x i)) \<Longrightarrow> pred M (\<lambda>x. x \<in> (\<Inter>i\<in>X. N x i))"
    "(\<And>i. i \<in> X \<Longrightarrow> pred M (\<lambda>x. x \<in> N x i)) \<Longrightarrow> pred M (\<lambda>x. x \<in> (\<Union>i\<in>X. N x i))"
    "(\<And>i. i \<in> X \<Longrightarrow> pred M (\<lambda>x. P x i)) \<Longrightarrow> pred M (\<lambda>x. \<forall>i\<in>X. P x i)"
    "(\<And>i. i \<in> X \<Longrightarrow> pred M (\<lambda>x. P x i)) \<Longrightarrow> pred M (\<lambda>x. \<exists>i\<in>X. P x i)"
  by simp_all (auto simp: Bex_def Ball_def)

lemma pred_intros_finite[measurable (raw)]:
  "finite I \<Longrightarrow> (\<And>i. i \<in> I \<Longrightarrow> pred M (\<lambda>x. x \<in> N x i)) \<Longrightarrow> pred M (\<lambda>x. x \<in> (\<Inter>i\<in>I. N x i))"
  "finite I \<Longrightarrow> (\<And>i. i \<in> I \<Longrightarrow> pred M (\<lambda>x. x \<in> N x i)) \<Longrightarrow> pred M (\<lambda>x. x \<in> (\<Union>i\<in>I. N x i))"
  "finite I \<Longrightarrow> (\<And>i. i \<in> I \<Longrightarrow> pred M (\<lambda>x. P x i)) \<Longrightarrow> pred M (\<lambda>x. \<forall>i\<in>I. P x i)"
  "finite I \<Longrightarrow> (\<And>i. i \<in> I \<Longrightarrow> pred M (\<lambda>x. P x i)) \<Longrightarrow> pred M (\<lambda>x. \<exists>i\<in>I. P x i)"
  by (auto intro!: sets.sets_Collect_finite_Ex sets.sets_Collect_finite_All simp: iff_conv_conj_imp pred_def)

lemma countable_Un_Int[measurable (raw)]:
  "(\<And>i :: 'i :: countable. i \<in> I \<Longrightarrow> N i \<in> sets M) \<Longrightarrow> (\<Union>i\<in>I. N i) \<in> sets M"
  "I \<noteq> {} \<Longrightarrow> (\<And>i :: 'i :: countable. i \<in> I \<Longrightarrow> N i \<in> sets M) \<Longrightarrow> (\<Inter>i\<in>I. N i) \<in> sets M"
  by auto

declare
  finite_UN[measurable (raw)]
  finite_INT[measurable (raw)]

lemma sets_Int_pred[measurable (raw)]:
  assumes space: "A \<inter> B \<subseteq> space M" and [measurable]: "pred M (\<lambda>x. x \<in> A)" "pred M (\<lambda>x. x \<in> B)"
  shows "A \<inter> B \<in> sets M"
proof -
  have "{x\<in>space M. x \<in> A \<inter> B} \<in> sets M" by auto
  also have "{x\<in>space M. x \<in> A \<inter> B} = A \<inter> B"
    using space by auto
  finally show ?thesis .
qed

lemma [measurable (raw generic)]:
  assumes f: "f \<in> measurable M N" and c: "c \<in> space N \<Longrightarrow> {c} \<in> sets N"
  shows pred_eq_const1: "pred M (\<lambda>x. f x = c)"
    and pred_eq_const2: "pred M (\<lambda>x. c = f x)"
proof -
  show "pred M (\<lambda>x. f x = c)"
  proof cases
    assume "c \<in> space N"
    with measurable_sets[OF f c] show ?thesis
      by (auto simp: Int_def conj_commute pred_def)
  next
    assume "c \<notin> space N"
    with f[THEN measurable_space] have "{x \<in> space M. f x = c} = {}" by auto
    then show ?thesis by (auto simp: pred_def cong: conj_cong)
  qed
  then show "pred M (\<lambda>x. c = f x)"
    by (simp add: eq_commute)
qed

lemma pred_count_space_const1[measurable (raw)]:
  "f \<in> measurable M (count_space UNIV) \<Longrightarrow> Measurable.pred M (\<lambda>x. f x = c)"
  by (intro pred_eq_const1[where N="count_space UNIV"]) (auto )

lemma pred_count_space_const2[measurable (raw)]:
  "f \<in> measurable M (count_space UNIV) \<Longrightarrow> Measurable.pred M (\<lambda>x. c = f x)"
  by (intro pred_eq_const2[where N="count_space UNIV"]) (auto )

lemma pred_le_const[measurable (raw generic)]:
  assumes f: "f \<in> measurable M N" and c: "{.. c} \<in> sets N" shows "pred M (\<lambda>x. f x \<le> c)"
  using measurable_sets[OF f c]
  by (auto simp: Int_def conj_commute eq_commute pred_def)

lemma pred_const_le[measurable (raw generic)]:
  assumes f: "f \<in> measurable M N" and c: "{c ..} \<in> sets N" shows "pred M (\<lambda>x. c \<le> f x)"
  using measurable_sets[OF f c]
  by (auto simp: Int_def conj_commute eq_commute pred_def)

lemma pred_less_const[measurable (raw generic)]:
  assumes f: "f \<in> measurable M N" and c: "{..< c} \<in> sets N" shows "pred M (\<lambda>x. f x < c)"
  using measurable_sets[OF f c]
  by (auto simp: Int_def conj_commute eq_commute pred_def)

lemma pred_const_less[measurable (raw generic)]:
  assumes f: "f \<in> measurable M N" and c: "{c <..} \<in> sets N" shows "pred M (\<lambda>x. c < f x)"
  using measurable_sets[OF f c]
  by (auto simp: Int_def conj_commute eq_commute pred_def)

declare
  sets.Int[measurable (raw)]

lemma pred_in_If[measurable (raw)]:
  "(P \<Longrightarrow> pred M (\<lambda>x. x \<in> A x)) \<Longrightarrow> (\<not> P \<Longrightarrow> pred M (\<lambda>x. x \<in> B x)) \<Longrightarrow>
    pred M (\<lambda>x. x \<in> (if P then A x else B x))"
  by auto

lemma sets_range[measurable_dest]:
  "A ` I \<subseteq> sets M \<Longrightarrow> i \<in> I \<Longrightarrow> A i \<in> sets M"
  by auto

lemma pred_sets_range[measurable_dest]:
  "A ` I \<subseteq> sets N \<Longrightarrow> i \<in> I \<Longrightarrow> f \<in> measurable M N \<Longrightarrow> pred M (\<lambda>x. f x \<in> A i)"
  using pred_sets2[OF sets_range] by auto

lemma sets_All[measurable_dest]:
  "\<forall>i. A i \<in> sets (M i) \<Longrightarrow> A i \<in> sets (M i)"
  by auto

lemma pred_sets_All[measurable_dest]:
  "\<forall>i. A i \<in> sets (N i) \<Longrightarrow> f \<in> measurable M (N i) \<Longrightarrow> pred M (\<lambda>x. f x \<in> A i)"
  using pred_sets2[OF sets_All, of A N f] by auto

lemma sets_Ball[measurable_dest]:
  "\<forall>i\<in>I. A i \<in> sets (M i) \<Longrightarrow> i\<in>I \<Longrightarrow> A i \<in> sets (M i)"
  by auto

lemma pred_sets_Ball[measurable_dest]:
  "\<forall>i\<in>I. A i \<in> sets (N i) \<Longrightarrow> i\<in>I \<Longrightarrow> f \<in> measurable M (N i) \<Longrightarrow> pred M (\<lambda>x. f x \<in> A i)"
  using pred_sets2[OF sets_Ball, of _ _ _ f] by auto

lemma measurable_finite[measurable (raw)]:
  fixes S :: "'a \<Rightarrow> nat set"
  assumes [measurable]: "\<And>i. {x\<in>space M. i \<in> S x} \<in> sets M"
  shows "pred M (\<lambda>x. finite (S x))"
  unfolding finite_nat_set_iff_bounded by (simp add: Ball_def)

lemma measurable_Least[measurable]:
  assumes [measurable]: "(\<And>i::nat. (\<lambda>x. P i x) \<in> measurable M (count_space UNIV))"
  shows "(\<lambda>x. LEAST i. P i x) \<in> measurable M (count_space UNIV)"
  unfolding measurable_def by (safe intro!: sets_Least) simp_all

lemma measurable_Max_nat[measurable (raw)]:
  fixes P :: "nat \<Rightarrow> 'a \<Rightarrow> bool"
  assumes [measurable]: "\<And>i. Measurable.pred M (P i)"
  shows "(\<lambda>x. Max {i. P i x}) \<in> measurable M (count_space UNIV)"
  unfolding measurable_count_space_eq2_countable
proof safe
  fix n
  have 1: "Max {i. P i x} = the None" if "\<forall>i. \<exists>n\<ge>i. P n x" for x
    by (simp add: Max.infinite infinite_nat_iff_unbounded_le that)
  have 2: "finite {i. P i x}" if "\<forall>n\<ge>j. \<not> P n x" for j x
    by (metis bounded_nat_set_is_finite leI mem_Collect_eq that)
  have 3: "P (Max {i. P i x}) x" "i \<le> Max {i. P i x}" if "P i x" "\<forall>n\<ge>j. \<not> P n x" for x i j
      using that 2 Max_in[of "{i. P i x}"] by auto 
  have "(\<lambda>x. Max {i. P i x}) -` {n} \<inter> space M = {x\<in>space M. Max {i. P i x} = n}"
    by auto
  also have "\<dots> =
    {x\<in>space M. if (\<forall>i. \<exists>n\<ge>i. P n x) then the None = n else
      if (\<exists>i. P i x) then P n x \<and> (\<forall>i>n. \<not> P i x)
      else Max {} = n}"
    by (intro arg_cong[where f=Collect] ext conj_cong)
       (auto simp add: 1 2 3 not_le[symmetric] intro!: Max_eqI)
  also have "\<dots> \<in> sets M"
    by measurable
  finally show "(\<lambda>x. Max {i. P i x}) -` {n} \<inter> space M \<in> sets M" .
qed simp

lemma measurable_Min_nat[measurable (raw)]:
  fixes P :: "nat \<Rightarrow> 'a \<Rightarrow> bool"
  assumes [measurable]: "\<And>i. Measurable.pred M (P i)"
  shows "(\<lambda>x. Min {i. P i x}) \<in> measurable M (count_space UNIV)"
  unfolding measurable_count_space_eq2_countable
proof safe
  fix n
  have 1: "Min {i. P i x} = the None" if "\<forall>i. \<exists>n\<ge>i. P n x" for x
    by (simp add: Min.infinite infinite_nat_iff_unbounded_le that)
  have 2: "finite {i. P i x}" if "\<forall>n\<ge>j. \<not> P n x" for j x
    by (metis bounded_nat_set_is_finite leI mem_Collect_eq that)
  have 3: "P (Min {i. P i x}) x" "i \<ge> Min {i. P i x}" if "P i x" "\<forall>n\<ge>j. \<not> P n x" for x i j
      using that 2 Min_in[of "{i. P i x}"] by auto 

  have "(\<lambda>x. Min {i. P i x}) -` {n} \<inter> space M = {x\<in>space M. Min {i. P i x} = n}"
    by auto
  also have "\<dots> =
    {x\<in>space M. if (\<forall>i. \<exists>n\<ge>i. P n x) then the None = n else
      if (\<exists>i. P i x) then P n x \<and> (\<forall>i<n. \<not> P i x)
      else Min {} = n}"
    by (intro arg_cong[where f=Collect] ext conj_cong)
       (auto simp add: 1 2 3 not_le[symmetric] intro!: Min_eqI)
  also have "\<dots> \<in> sets M"
    by measurable
  finally show "(\<lambda>x. Min {i. P i x}) -` {n} \<inter> space M \<in> sets M" .
qed simp

lemma measurable_count_space_insert[measurable (raw)]:
  "s \<in> S \<Longrightarrow> A \<in> sets (count_space S) \<Longrightarrow> insert s A \<in> sets (count_space S)"
  by simp

lemma sets_UNIV [measurable (raw)]: "A \<in> sets (count_space UNIV)"
  by simp

lemma measurable_card[measurable]:
  fixes S :: "'a \<Rightarrow> nat set"
  assumes [measurable]: "\<And>i. {x\<in>space M. i \<in> S x} \<in> sets M"
  shows "(\<lambda>x. card (S x)) \<in> measurable M (count_space UNIV)"
  unfolding measurable_count_space_eq2_countable
proof safe
  fix n show "(\<lambda>x. card (S x)) -` {n} \<inter> space M \<in> sets M"
  proof (cases n)
    case 0
    then have "(\<lambda>x. card (S x)) -` {n} \<inter> space M = {x\<in>space M. infinite (S x) \<or> (\<forall>i. i \<notin> S x)}"
      by auto
    also have "\<dots> \<in> sets M"
      by measurable
    finally show ?thesis .
  next
    case (Suc i)
    then have "(\<lambda>x. card (S x)) -` {n} \<inter> space M =
               (\<Union>F\<in>{A\<in>{A. finite A}. card A = n}. {x\<in>space M. (\<forall>i. i \<in> S x \<longleftrightarrow> i \<in> F)})"
      unfolding set_eq_iff[symmetric] Collect_bex_eq[symmetric] by (auto intro: card_ge_0_finite)
    also have "\<dots> \<in> sets M"
      by (intro sets.countable_UN' countable_Collect countable_Collect_finite) auto
    finally show ?thesis .
  qed
qed rule

lemma measurable_pred_countable[measurable (raw)]:
  assumes "countable X"
  shows
    "(\<And>i. i \<in> X \<Longrightarrow> Measurable.pred M (\<lambda>x. P x i)) \<Longrightarrow> Measurable.pred M (\<lambda>x. \<forall>i\<in>X. P x i)"
    "(\<And>i. i \<in> X \<Longrightarrow> Measurable.pred M (\<lambda>x. P x i)) \<Longrightarrow> Measurable.pred M (\<lambda>x. \<exists>i\<in>X. P x i)"
  unfolding pred_def
  by (auto intro!: sets.sets_Collect_countable_All' sets.sets_Collect_countable_Ex' assms)

subsection\<^marker>\<open>tag unimportant\<close> \<open>Measurability for (co)inductive predicates\<close>

lemma measurable_bot[measurable]: "bot \<in> measurable M (count_space UNIV)"
  by (simp add: bot_fun_def)

lemma measurable_top[measurable]: "top \<in> measurable M (count_space UNIV)"
  by (simp add: top_fun_def)

lemma measurable_SUP[measurable]:
  fixes F :: "'i \<Rightarrow> 'a \<Rightarrow> 'b::{complete_lattice, countable}"
  assumes [simp]: "countable I"
  assumes [measurable]: "\<And>i. i \<in> I \<Longrightarrow> F i \<in> measurable M (count_space UNIV)"
  shows "(\<lambda>x. SUP i\<in>I. F i x) \<in> measurable M (count_space UNIV)"
  unfolding measurable_count_space_eq2_countable
proof (safe intro!: UNIV_I)
  fix a
  have "(\<lambda>x. SUP i\<in>I. F i x) -` {a} \<inter> space M =
        {x\<in>space M. (\<forall>i\<in>I. F i x \<le> a) \<and> (\<forall>b. (\<forall>i\<in>I. F i x \<le> b) \<longrightarrow> a \<le> b)}"
    unfolding SUP_le_iff[symmetric] by auto
  also have "\<dots> \<in> sets M"
    by measurable
  finally show "(\<lambda>x. SUP i\<in>I. F i x) -` {a} \<inter> space M \<in> sets M" .
qed

lemma measurable_INF[measurable]:
  fixes F :: "'i \<Rightarrow> 'a \<Rightarrow> 'b::{complete_lattice, countable}"
  assumes [simp]: "countable I"
  assumes [measurable]: "\<And>i. i \<in> I \<Longrightarrow> F i \<in> measurable M (count_space UNIV)"
  shows "(\<lambda>x. INF i\<in>I. F i x) \<in> measurable M (count_space UNIV)"
  unfolding measurable_count_space_eq2_countable
proof (safe intro!: UNIV_I)
  fix a
  have "(\<lambda>x. INF i\<in>I. F i x) -` {a} \<inter> space M =
        {x\<in>space M. (\<forall>i\<in>I. a \<le> F i x) \<and> (\<forall>b. (\<forall>i\<in>I. b \<le> F i x) \<longrightarrow> b \<le> a)}"
    unfolding le_INF_iff[symmetric] by auto
  also have "\<dots> \<in> sets M"
    by measurable
  finally show "(\<lambda>x. INF i\<in>I. F i x) -` {a} \<inter> space M \<in> sets M" .
qed

lemma measurable_lfp_coinduct[consumes 1, case_names continuity step]:
  fixes F :: "('a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'b::{complete_lattice, countable})"
  assumes "P M"
  assumes F: "sup_continuous F"
  assumes *: "\<And>M A. P M \<Longrightarrow> (\<And>N. P N \<Longrightarrow> A \<in> measurable N (count_space UNIV)) \<Longrightarrow> F A \<in> measurable M (count_space UNIV)"
  shows "lfp F \<in> measurable M (count_space UNIV)"
proof -
  have "((F ^^ i) bot) \<in> measurable M (count_space UNIV)" for i
    using \<open>P M\<close> by (induct i arbitrary: M) (auto intro!: *) 
  then have "(\<lambda>x. SUP i. (F ^^ i) bot x) \<in> measurable M (count_space UNIV)"
    by measurable
  also have "(\<lambda>x. SUP i. (F ^^ i) bot x) = lfp F"
    by (subst sup_continuous_lfp) (auto intro: F simp: image_comp)
  finally show ?thesis .
qed

lemma measurable_lfp:
  fixes F :: "('a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'b::{complete_lattice, countable})"
  assumes F: "sup_continuous F"
  assumes *: "\<And>A. A \<in> measurable M (count_space UNIV) \<Longrightarrow> F A \<in> measurable M (count_space UNIV)"
  shows "lfp F \<in> measurable M (count_space UNIV)"
  by (coinduction rule: measurable_lfp_coinduct[OF _ F]) (blast intro: *)

lemma measurable_gfp_coinduct[consumes 1, case_names continuity step]:
  fixes F :: "('a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'b::{complete_lattice, countable})"
  assumes "P M"
  assumes F: "inf_continuous F"
  assumes *: "\<And>M A. P M \<Longrightarrow> (\<And>N. P N \<Longrightarrow> A \<in> measurable N (count_space UNIV)) \<Longrightarrow> F A \<in> measurable M (count_space UNIV)"
  shows "gfp F \<in> measurable M (count_space UNIV)"
proof -
  have "((F ^^ i) top) \<in> measurable M (count_space UNIV)" for i
    using \<open>P M\<close> by (induct i arbitrary: M) (auto intro!: *) 
  then have "(\<lambda>x. INF i. (F ^^ i) top x) \<in> measurable M (count_space UNIV)"
    by measurable
  also have "(\<lambda>x. INF i. (F ^^ i) top x) = gfp F"
    by (subst inf_continuous_gfp) (auto intro: F simp: image_comp)
  finally show ?thesis .
qed

lemma measurable_gfp:
  fixes F :: "('a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'b::{complete_lattice, countable})"
  assumes F: "inf_continuous F"
  assumes *: "\<And>A. A \<in> measurable M (count_space UNIV) \<Longrightarrow> F A \<in> measurable M (count_space UNIV)"
  shows "gfp F \<in> measurable M (count_space UNIV)"
  by (coinduction rule: measurable_gfp_coinduct[OF _ F]) (blast intro: *)

lemma measurable_lfp2_coinduct[consumes 1, case_names continuity step]:
  fixes F :: "('a \<Rightarrow> 'c \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'c \<Rightarrow> 'b::{complete_lattice, countable})"
  assumes "P M s"
  assumes F: "sup_continuous F"
  assumes *: "\<And>M A s. P M s \<Longrightarrow> (\<And>N t. P N t \<Longrightarrow> A t \<in> measurable N (count_space UNIV)) \<Longrightarrow> F A s \<in> measurable M (count_space UNIV)"
  shows "lfp F s \<in> measurable M (count_space UNIV)"
proof -
  have "(\<lambda>x. (F ^^ i) bot s x) \<in> measurable M (count_space UNIV)" for i
    using \<open>P M s\<close> by (induct i arbitrary: M s) (auto intro!: *) 
  then have "(\<lambda>x. SUP i. (F ^^ i) bot s x) \<in> measurable M (count_space UNIV)"
    by measurable
  also have "(\<lambda>x. SUP i. (F ^^ i) bot s x) = lfp F s"
    by (subst sup_continuous_lfp) (auto simp: F simp: image_comp)
  finally show ?thesis .
qed

lemma measurable_gfp2_coinduct[consumes 1, case_names continuity step]:
  fixes F :: "('a \<Rightarrow> 'c \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'c \<Rightarrow> 'b::{complete_lattice, countable})"
  assumes "P M s"
  assumes F: "inf_continuous F"
  assumes *: "\<And>M A s. P M s \<Longrightarrow> (\<And>N t. P N t \<Longrightarrow> A t \<in> measurable N (count_space UNIV)) \<Longrightarrow> F A s \<in> measurable M (count_space UNIV)"
  shows "gfp F s \<in> measurable M (count_space UNIV)"
proof -
  have "(\<lambda>x. (F ^^ i) top s x) \<in> measurable M (count_space UNIV)" for i
    using \<open>P M s\<close> by (induct i arbitrary: M s) (auto intro!: *) 
  then have "(\<lambda>x. INF i. (F ^^ i) top s x) \<in> measurable M (count_space UNIV)"
    by measurable
  also have "(\<lambda>x. INF i. (F ^^ i) top s x) = gfp F s"
    by (subst inf_continuous_gfp) (auto simp: F simp: image_comp)
  finally show ?thesis .
qed

lemma measurable_enat_coinduct:
  fixes f :: "'a \<Rightarrow> enat"
  assumes "R f"
  assumes *: "\<And>f. R f \<Longrightarrow> \<exists>g h i P. R g \<and> f = (\<lambda>x. if P x then h x else eSuc (g (i x))) \<and>
    Measurable.pred M P \<and>
    i \<in> measurable M M \<and>
    h \<in> measurable M (count_space UNIV)"
  shows "f \<in> measurable M (count_space UNIV)"
proof (simp add: measurable_count_space_eq2_countable, rule )
  fix a :: enat
  have "f -` {a} \<inter> space M = {x\<in>space M. f x = a}"
    by auto
  have "Measurable.pred M (\<lambda>x. f x = enat i)" for i
    using \<open>R f\<close>
  proof (induction i arbitrary: f)
    case 0
    from *[OF this] obtain g h i P
      where f: "f = (\<lambda>x. if P x then h x else eSuc (g (i x)))" and
        [measurable]: "Measurable.pred M P" "i \<in> measurable M M" "h \<in> measurable M (count_space UNIV)"
      by auto
    have "Measurable.pred M (\<lambda>x. P x \<and> h x = 0)"
      by measurable
    also have "(\<lambda>x. P x \<and> h x = 0) = (\<lambda>x. f x = enat 0)"
      by (auto simp: f zero_enat_def[symmetric])
    finally show ?case .
  next
    case (Suc n)
    from *[OF Suc.prems] obtain g h i P
      where f: "f = (\<lambda>x. if P x then h x else eSuc (g (i x)))" and "R g" and
        M[measurable]: "Measurable.pred M P" "i \<in> measurable M M" "h \<in> measurable M (count_space UNIV)"
      by auto
    have "(\<lambda>x. f x = enat (Suc n)) =
        (\<lambda>x. (P x \<longrightarrow> h x = enat (Suc n)) \<and> (\<not> P x \<longrightarrow> g (i x) = enat n))"
      by (auto simp: f zero_enat_def[symmetric] eSuc_enat[symmetric])
    also have "Measurable.pred M \<dots>"
      by (intro pred_intros_logic measurable_compose[OF M(2)] Suc \<open>R g\<close>) measurable
    finally show ?case .
  qed
  then have fin: "f -` {enat i} \<inter> space M \<in> sets M" for i
    by (simp add: pred_def Int_def conj_commute) 
  show "f -` {a} \<inter> space M \<in> sets M"
  proof (cases a)
    case infinity
    then have "f -` {a} \<inter> space M = space M - (\<Union>n. f -` {enat n} \<inter> space M)"
      by auto
    also have "\<dots> \<in> sets M"
      by (intro sets.Diff sets.top sets.Un sets.countable_UN) (auto intro!: fin)
    finally show ?thesis .
  qed (simp add: fin)
qed

lemma measurable_THE:
  fixes P :: "'a \<Rightarrow> 'b \<Rightarrow> bool"
  assumes [measurable]: "\<And>i. Measurable.pred M (P i)"
  assumes I[simp]: "countable I" "\<And>i x. x \<in> space M \<Longrightarrow> P i x \<Longrightarrow> i \<in> I"
  assumes unique: "\<And>x i j. x \<in> space M \<Longrightarrow> P i x \<Longrightarrow> P j x \<Longrightarrow> i = j"
  shows "(\<lambda>x. THE i. P i x) \<in> measurable M (count_space UNIV)"
  unfolding measurable_def
proof safe
  fix X
  define f where "f x = (THE i. P i x)" for x
  define undef where "undef = (THE i::'a. False)"
  have f_eq: "f x = i" if "x \<in> space M" "P i x" for i x
    unfolding f_def using unique that by auto
  have "f x = undef" if "x \<in> space M" "\<forall>i\<in>I. \<not> P i x" for x
    using that I f_def undef_def by moura
  then have "f -` X \<inter> space M = 
             (\<Union>i\<in>I \<inter> X. {x\<in>space M. P i x}) \<union> (if undef \<in> X then space M - (\<Union>i\<in>I. {x\<in>space M. P i x}) else {})"
    by (auto dest: f_eq)
  also have "\<dots> \<in> sets M"
    by (auto intro!: sets.Diff sets.countable_UN')
  finally show "f -` X \<inter> space M \<in> sets M" .
qed simp

lemma measurable_Ex1[measurable (raw)]:
  assumes [simp]: "countable I" and [measurable]: "\<And>i. i \<in> I \<Longrightarrow> Measurable.pred M (P i)"
  shows "Measurable.pred M (\<lambda>x. \<exists>!i\<in>I. P i x)"
  unfolding bex1_def by measurable

lemma measurable_Sup_nat[measurable (raw)]:
  fixes F :: "'a \<Rightarrow> nat set"
  assumes [measurable]: "\<And>i. Measurable.pred M (\<lambda>x. i \<in> F x)"
  shows "(\<lambda>x. Sup (F x)) \<in> M \<rightarrow>\<^sub>M count_space UNIV"
proof (clarsimp simp add: measurable_count_space_eq2_countable)
  fix a
  have F_empty_iff: "F x = {} \<longleftrightarrow> (\<forall>i. i \<notin> F x)" for x
    by auto
  have "Measurable.pred M (\<lambda>x. if finite (F x) then if F x = {} then a = 0
    else a \<in> F x \<and> (\<forall>j. j \<in> F x \<longrightarrow> j \<le> a) else a = the None)"
    unfolding finite_nat_set_iff_bounded Ball_def F_empty_iff by measurable
  moreover have "(\<lambda>x. Sup (F x)) -` {a} \<inter> space M =
    {x\<in>space M. if finite (F x) then if F x = {} then a = 0
      else a \<in> F x \<and> (\<forall>j. j \<in> F x \<longrightarrow> j \<le> a) else a = the None}"
    by (intro set_eqI)
       (auto simp: Sup_nat_def Max.infinite intro!: Max_in Max_eqI)
  ultimately show "(\<lambda>x. Sup (F x)) -` {a} \<inter> space M \<in> sets M"
    by auto
qed

lemma measurable_if_split[measurable (raw)]:
  "(c \<Longrightarrow> Measurable.pred M f) \<Longrightarrow> (\<not> c \<Longrightarrow> Measurable.pred M g) \<Longrightarrow>
   Measurable.pred M (if c then f else g)"
  by simp

lemma pred_restrict_space:
  assumes "S \<in> sets M"
  shows "Measurable.pred (restrict_space M S) P \<longleftrightarrow> Measurable.pred M (\<lambda>x. x \<in> S \<and> P x)"
  unfolding pred_def sets_Collect_restrict_space_iff[OF assms] ..

lemma measurable_predpow[measurable]:
  assumes "Measurable.pred M T"
  assumes "\<And>Q. Measurable.pred M Q \<Longrightarrow> Measurable.pred M (R Q)"
  shows "Measurable.pred M ((R ^^ n) T)"
  by (induct n) (auto intro: assms)

lemma measurable_compose_countable_restrict:
  assumes P: "countable {i. P i}"
    and f: "f \<in> M \<rightarrow>\<^sub>M count_space UNIV"
    and Q: "\<And>i. P i \<Longrightarrow> pred M (Q i)"
  shows "pred M (\<lambda>x. P (f x) \<and> Q (f x) x)"
proof -
  have P_f: "{x \<in> space M. P (f x)} \<in> sets M"
    unfolding pred_def[symmetric] by (rule measurable_compose[OF f]) simp
  have "pred (restrict_space M {x\<in>space M. P (f x)}) (\<lambda>x. Q (f x) x)"
  proof (rule measurable_compose_countable'[OF _ _ P])
    show "f \<in> restrict_space M {x\<in>space M. P (f x)} \<rightarrow>\<^sub>M count_space {i. P i}"
      by (rule measurable_count_space_extend[OF subset_UNIV])
         (auto simp: space_restrict_space intro!: measurable_restrict_space1 f)
  qed (auto intro!: measurable_restrict_space1 Q)
  then show ?thesis
    unfolding pred_restrict_space[OF P_f] by (simp cong: measurable_cong)
qed

lemma measurable_limsup [measurable (raw)]:
  assumes [measurable]: "\<And>n. A n \<in> sets M"
  shows "limsup A \<in> sets M"
by (subst limsup_INF_SUP, auto)

lemma measurable_liminf [measurable (raw)]:
  assumes [measurable]: "\<And>n. A n \<in> sets M"
  shows "liminf A \<in> sets M"
by (subst liminf_SUP_INF, auto)

lemma measurable_case_enat[measurable (raw)]:
  assumes f: "f \<in> M \<rightarrow>\<^sub>M count_space UNIV" and g: "\<And>i. g i \<in> M \<rightarrow>\<^sub>M N" and h: "h \<in> M \<rightarrow>\<^sub>M N"
  shows "(\<lambda>x. case f x of enat i \<Rightarrow> g i x | \<infinity> \<Rightarrow> h x) \<in> M \<rightarrow>\<^sub>M N"
  apply (rule measurable_compose_countable[OF _ f])
  subgoal for i
    by (cases i) (auto intro: g h)
  done

hide_const (open) pred

end

