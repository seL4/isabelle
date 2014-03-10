(*  Title:      HOL/Probability/Measurable.thy
    Author:     Johannes Hölzl <hoelzl@in.tum.de>
*)
theory Measurable
  imports
    Sigma_Algebra
    "~~/src/HOL/Library/Order_Continuity"
begin

hide_const (open) Order_Continuity.continuous

subsection {* Measurability prover *}

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

ML_file "measurable.ML"

attribute_setup measurable = {*
  Scan.lift (Scan.optional (Args.parens (Scan.optional (Args.$$$ "raw" >> K true) false --
    Scan.optional (Args.$$$ "generic" >> K Measurable.Generic) Measurable.Concrete))
    (false, Measurable.Concrete) >> (Thm.declaration_attribute o Measurable.add_thm))
*} "declaration of measurability theorems"

attribute_setup measurable_dest = {*
  Scan.lift (Scan.succeed (Thm.declaration_attribute Measurable.add_dest))
*} "add dest rule for measurability prover"

attribute_setup measurable_app = {*
  Scan.lift (Scan.succeed (Thm.declaration_attribute Measurable.add_app))
*} "add application rule for measurability prover"

method_setup measurable = {*
  Scan.lift (Scan.succeed (fn ctxt => METHOD (fn facts => Measurable.measurable_tac ctxt facts)))
*} "measurability prover"

simproc_setup measurable ("A \<in> sets M" | "f \<in> measurable M N") = {* K Measurable.simproc *}

declare
  measurable_compose_rev[measurable_dest]
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
  measurable_ident_sets[measurable (raw)]
  measurable_const[measurable (raw)]
  measurable_If[measurable (raw)]
  measurable_comp[measurable (raw)]
  measurable_sets[measurable (raw)]

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
  by (auto simp: Bex_def Ball_def)

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
  assumes [measurable]: "(\<And>i::nat. (\<lambda>x. P i x) \<in> measurable M (count_space UNIV))"q
  shows "(\<lambda>x. LEAST i. P i x) \<in> measurable M (count_space UNIV)"
  unfolding measurable_def by (safe intro!: sets_Least) simp_all

lemma measurable_count_space_insert[measurable (raw)]:
  "s \<in> S \<Longrightarrow> A \<in> sets (count_space S) \<Longrightarrow> insert s A \<in> sets (count_space S)"
  by simp

subsection {* Measurability for (co)inductive predicates *}

lemma measurable_lfp:
  assumes "P = lfp F"
  assumes "Order_Continuity.continuous F"
  assumes *: "\<And>A. pred M A \<Longrightarrow> pred M (F A)"
  shows "pred M P"
proof -
  { fix i have "Measurable.pred M (\<lambda>x. (F ^^ i) (\<lambda>x. False) x)"
      by (induct i) (auto intro!: *) }
  then have "Measurable.pred M (\<lambda>x. \<exists>i. (F ^^ i) (\<lambda>x. False) x)"
    by measurable
  also have "(\<lambda>x. \<exists>i. (F ^^ i) (\<lambda>x. False) x) = (SUP i. (F ^^ i) bot)"
    by (auto simp add: bot_fun_def)
  also have "\<dots> = P"
    unfolding `P = lfp F` by (rule continuous_lfp[symmetric]) fact
  finally show ?thesis .
qed

lemma measurable_gfp:
  assumes "P = gfp F"
  assumes "Order_Continuity.down_continuous F"
  assumes *: "\<And>A. pred M A \<Longrightarrow> pred M (F A)"
  shows "pred M P"
proof -
  { fix i have "Measurable.pred M (\<lambda>x. (F ^^ i) (\<lambda>x. True) x)"
      by (induct i) (auto intro!: *) }
  then have "Measurable.pred M (\<lambda>x. \<forall>i. (F ^^ i) (\<lambda>x. True) x)"
    by measurable
  also have "(\<lambda>x. \<forall>i. (F ^^ i) (\<lambda>x. True) x) = (INF i. (F ^^ i) top)"
    by (auto simp add: top_fun_def)
  also have "\<dots> = P"
    unfolding `P = gfp F` by (rule down_continuous_gfp[symmetric]) fact
  finally show ?thesis .
qed

hide_const (open) pred

end
