(*  Title:      HOL/Inductive.thy
    Author:     Markus Wenzel, TU Muenchen
*)

section \<open>Knaster-Tarski Fixpoint Theorem and inductive definitions\<close>

theory Inductive
  imports Complete_Lattices Ctr_Sugar
  keywords
    "inductive" "coinductive" "inductive_cases" "inductive_simps" :: thy_defn and
    "monos" and
    "print_inductives" :: diag and
    "old_rep_datatype" :: thy_goal and
    "primrec" :: thy_defn
begin

subsection \<open>Least fixed points\<close>

context complete_lattice
begin

definition lfp :: "('a \<Rightarrow> 'a) \<Rightarrow> 'a"
  where "lfp f = Inf {u. f u \<le> u}"

lemma lfp_lowerbound: "f A \<le> A \<Longrightarrow> lfp f \<le> A"
  unfolding lfp_def by (rule Inf_lower) simp

lemma lfp_greatest: "(\<And>u. f u \<le> u \<Longrightarrow> A \<le> u) \<Longrightarrow> A \<le> lfp f"
  unfolding lfp_def by (rule Inf_greatest) simp

end

lemma lfp_fixpoint:
  assumes "mono f"
  shows "f (lfp f) = lfp f"
  unfolding lfp_def
proof (rule order_antisym)
  let ?H = "{u. f u \<le> u}"
  let ?a = "\<Sqinter>?H"
  show "f ?a \<le> ?a"
  proof (rule Inf_greatest)
    fix x
    assume "x \<in> ?H"
    then have "?a \<le> x" by (rule Inf_lower)
    with \<open>mono f\<close> have "f ?a \<le> f x" ..
    also from \<open>x \<in> ?H\<close> have "f x \<le> x" ..
    finally show "f ?a \<le> x" .
  qed
  show "?a \<le> f ?a"
  proof (rule Inf_lower)
    from \<open>mono f\<close> and \<open>f ?a \<le> ?a\<close> have "f (f ?a) \<le> f ?a" ..
    then show "f ?a \<in> ?H" ..
  qed
qed

lemma lfp_unfold: "mono f \<Longrightarrow> lfp f = f (lfp f)"
  by (rule lfp_fixpoint [symmetric])

lemma lfp_const: "lfp (\<lambda>x. t) = t"
  by (rule lfp_unfold) (simp add: mono_def)

lemma lfp_eqI: "mono F \<Longrightarrow> F x = x \<Longrightarrow> (\<And>z. F z = z \<Longrightarrow> x \<le> z) \<Longrightarrow> lfp F = x"
  by (rule antisym) (simp_all add: lfp_lowerbound lfp_unfold[symmetric])


subsection \<open>General induction rules for least fixed points\<close>

lemma lfp_ordinal_induct [case_names mono step union]:
  fixes f :: "'a::complete_lattice \<Rightarrow> 'a"
  assumes mono: "mono f"
    and P_f: "\<And>S. P S \<Longrightarrow> S \<le> lfp f \<Longrightarrow> P (f S)"
    and P_Union: "\<And>M. \<forall>S\<in>M. P S \<Longrightarrow> P (Sup M)"
  shows "P (lfp f)"
proof -
  let ?M = "{S. S \<le> lfp f \<and> P S}"
  from P_Union have "P (Sup ?M)" by simp
  also have "Sup ?M = lfp f"
  proof (rule antisym)
    show "Sup ?M \<le> lfp f"
      by (blast intro: Sup_least)
    then have "f (Sup ?M) \<le> f (lfp f)"
      by (rule mono [THEN monoD])
    then have "f (Sup ?M) \<le> lfp f"
      using mono [THEN lfp_unfold] by simp
    then have "f (Sup ?M) \<in> ?M"
      using P_Union by simp (intro P_f Sup_least, auto)
    then have "f (Sup ?M) \<le> Sup ?M"
      by (rule Sup_upper)
    then show "lfp f \<le> Sup ?M"
      by (rule lfp_lowerbound)
  qed
  finally show ?thesis .
qed

theorem lfp_induct:
  assumes mono: "mono f"
    and ind: "f (inf (lfp f) P) \<le> P"
  shows "lfp f \<le> P"
proof (induct rule: lfp_ordinal_induct)
  case mono
  show ?case by fact
next
  case (step S)
  then show ?case
    by (intro order_trans[OF _ ind] monoD[OF mono]) auto
next
  case (union M)
  then show ?case
    by (auto intro: Sup_least)
qed

lemma lfp_induct_set:
  assumes lfp: "a \<in> lfp f"
    and mono: "mono f"
    and hyp: "\<And>x. x \<in> f (lfp f \<inter> {x. P x}) \<Longrightarrow> P x"
  shows "P a"
  by (rule lfp_induct [THEN subsetD, THEN CollectD, OF mono _ lfp]) (auto intro: hyp)

lemma lfp_ordinal_induct_set:
  assumes mono: "mono f"
    and P_f: "\<And>S. P S \<Longrightarrow> P (f S)"
    and P_Union: "\<And>M. \<forall>S\<in>M. P S \<Longrightarrow> P (\<Union>M)"
  shows "P (lfp f)"
  using assms by (rule lfp_ordinal_induct)


text \<open>Definition forms of \<open>lfp_unfold\<close> and \<open>lfp_induct\<close>, to control unfolding.\<close>

lemma def_lfp_unfold: "h \<equiv> lfp f \<Longrightarrow> mono f \<Longrightarrow> h = f h"
  by (auto intro!: lfp_unfold)

lemma def_lfp_induct: "A \<equiv> lfp f \<Longrightarrow> mono f \<Longrightarrow> f (inf A P) \<le> P \<Longrightarrow> A \<le> P"
  by (blast intro: lfp_induct)

lemma def_lfp_induct_set:
  "A \<equiv> lfp f \<Longrightarrow> mono f \<Longrightarrow> a \<in> A \<Longrightarrow> (\<And>x. x \<in> f (A \<inter> {x. P x}) \<Longrightarrow> P x) \<Longrightarrow> P a"
  by (blast intro: lfp_induct_set)

text \<open>Monotonicity of \<open>lfp\<close>!\<close>
lemma lfp_mono: "(\<And>Z. f Z \<le> g Z) \<Longrightarrow> lfp f \<le> lfp g"
  by (rule lfp_lowerbound [THEN lfp_greatest]) (blast intro: order_trans)


subsection \<open>Greatest fixed points\<close>

context complete_lattice
begin

definition gfp :: "('a \<Rightarrow> 'a) \<Rightarrow> 'a"
  where "gfp f = Sup {u. u \<le> f u}"

lemma gfp_upperbound: "X \<le> f X \<Longrightarrow> X \<le> gfp f"
  by (auto simp add: gfp_def intro: Sup_upper)

lemma gfp_least: "(\<And>u. u \<le> f u \<Longrightarrow> u \<le> X) \<Longrightarrow> gfp f \<le> X"
  by (auto simp add: gfp_def intro: Sup_least)

end

lemma lfp_le_gfp: "mono f \<Longrightarrow> lfp f \<le> gfp f"
  by (rule gfp_upperbound) (simp add: lfp_fixpoint)

lemma gfp_fixpoint:
  assumes "mono f"
  shows "f (gfp f) = gfp f"
  unfolding gfp_def
proof (rule order_antisym)
  let ?H = "{u. u \<le> f u}"
  let ?a = "\<Squnion>?H"
  show "?a \<le> f ?a"
  proof (rule Sup_least)
    fix x
    assume "x \<in> ?H"
    then have "x \<le> f x" ..
    also from \<open>x \<in> ?H\<close> have "x \<le> ?a" by (rule Sup_upper)
    with \<open>mono f\<close> have "f x \<le> f ?a" ..
    finally show "x \<le> f ?a" .
  qed
  show "f ?a \<le> ?a"
  proof (rule Sup_upper)
    from \<open>mono f\<close> and \<open>?a \<le> f ?a\<close> have "f ?a \<le> f (f ?a)" ..
    then show "f ?a \<in> ?H" ..
  qed
qed

lemma gfp_unfold: "mono f \<Longrightarrow> gfp f = f (gfp f)"
  by (rule gfp_fixpoint [symmetric])

lemma gfp_const: "gfp (\<lambda>x. t) = t"
  by (rule gfp_unfold) (simp add: mono_def)

lemma gfp_eqI: "mono F \<Longrightarrow> F x = x \<Longrightarrow> (\<And>z. F z = z \<Longrightarrow> z \<le> x) \<Longrightarrow> gfp F = x"
  by (rule antisym) (simp_all add: gfp_upperbound gfp_unfold[symmetric])


subsection \<open>Coinduction rules for greatest fixed points\<close>

text \<open>Weak version.\<close>
lemma weak_coinduct: "a \<in> X \<Longrightarrow> X \<subseteq> f X \<Longrightarrow> a \<in> gfp f"
  by (rule gfp_upperbound [THEN subsetD]) auto

lemma weak_coinduct_image: "a \<in> X \<Longrightarrow> g`X \<subseteq> f (g`X) \<Longrightarrow> g a \<in> gfp f"
  apply (erule gfp_upperbound [THEN subsetD])
  apply (erule imageI)
  done

lemma coinduct_lemma: "X \<le> f (sup X (gfp f)) \<Longrightarrow> mono f \<Longrightarrow> sup X (gfp f) \<le> f (sup X (gfp f))"
  apply (frule gfp_unfold [THEN eq_refl])
  apply (drule mono_sup)
  apply (rule le_supI)
   apply assumption
  apply (rule order_trans)
   apply (rule order_trans)
    apply assumption
   apply (rule sup_ge2)
  apply assumption
  done

text \<open>Strong version, thanks to Coen and Frost.\<close>
lemma coinduct_set: "mono f \<Longrightarrow> a \<in> X \<Longrightarrow> X \<subseteq> f (X \<union> gfp f) \<Longrightarrow> a \<in> gfp f"
  by (rule weak_coinduct[rotated], rule coinduct_lemma) blast+

lemma gfp_fun_UnI2: "mono f \<Longrightarrow> a \<in> gfp f \<Longrightarrow> a \<in> f (X \<union> gfp f)"
  by (blast dest: gfp_fixpoint mono_Un)

lemma gfp_ordinal_induct[case_names mono step union]:
  fixes f :: "'a::complete_lattice \<Rightarrow> 'a"
  assumes mono: "mono f"
    and P_f: "\<And>S. P S \<Longrightarrow> gfp f \<le> S \<Longrightarrow> P (f S)"
    and P_Union: "\<And>M. \<forall>S\<in>M. P S \<Longrightarrow> P (Inf M)"
  shows "P (gfp f)"
proof -
  let ?M = "{S. gfp f \<le> S \<and> P S}"
  from P_Union have "P (Inf ?M)" by simp
  also have "Inf ?M = gfp f"
  proof (rule antisym)
    show "gfp f \<le> Inf ?M"
      by (blast intro: Inf_greatest)
    then have "f (gfp f) \<le> f (Inf ?M)"
      by (rule mono [THEN monoD])
    then have "gfp f \<le> f (Inf ?M)"
      using mono [THEN gfp_unfold] by simp
    then have "f (Inf ?M) \<in> ?M"
      using P_Union by simp (intro P_f Inf_greatest, auto)
    then have "Inf ?M \<le> f (Inf ?M)"
      by (rule Inf_lower)
    then show "Inf ?M \<le> gfp f"
      by (rule gfp_upperbound)
  qed
  finally show ?thesis .
qed

lemma coinduct:
  assumes mono: "mono f"
    and ind: "X \<le> f (sup X (gfp f))"
  shows "X \<le> gfp f"
proof (induct rule: gfp_ordinal_induct)
  case mono
  then show ?case by fact
next
  case (step S)
  then show ?case
    by (intro order_trans[OF ind _] monoD[OF mono]) auto
next
  case (union M)
  then show ?case
    by (auto intro: mono Inf_greatest)
qed


subsection \<open>Even Stronger Coinduction Rule, by Martin Coen\<close>

text \<open>Weakens the condition \<^term>\<open>X \<subseteq> f X\<close> to one expressed using both
  \<^term>\<open>lfp\<close> and \<^term>\<open>gfp\<close>\<close>
lemma coinduct3_mono_lemma: "mono f \<Longrightarrow> mono (\<lambda>x. f x \<union> X \<union> B)"
  by (iprover intro: subset_refl monoI Un_mono monoD)

lemma coinduct3_lemma:
  "X \<subseteq> f (lfp (\<lambda>x. f x \<union> X \<union> gfp f)) \<Longrightarrow> mono f \<Longrightarrow>
    lfp (\<lambda>x. f x \<union> X \<union> gfp f) \<subseteq> f (lfp (\<lambda>x. f x \<union> X \<union> gfp f))"
  apply (rule subset_trans)
   apply (erule coinduct3_mono_lemma [THEN lfp_unfold [THEN eq_refl]])
  apply (rule Un_least [THEN Un_least])
    apply (rule subset_refl, assumption)
  apply (rule gfp_unfold [THEN equalityD1, THEN subset_trans], assumption)
  apply (rule monoD, assumption)
  apply (subst coinduct3_mono_lemma [THEN lfp_unfold], auto)
  done

lemma coinduct3: "mono f \<Longrightarrow> a \<in> X \<Longrightarrow> X \<subseteq> f (lfp (\<lambda>x. f x \<union> X \<union> gfp f)) \<Longrightarrow> a \<in> gfp f"
  apply (rule coinduct3_lemma [THEN [2] weak_coinduct])
    apply (rule coinduct3_mono_lemma [THEN lfp_unfold, THEN ssubst])
     apply simp_all
  done

text  \<open>Definition forms of \<open>gfp_unfold\<close> and \<open>coinduct\<close>, to control unfolding.\<close>

lemma def_gfp_unfold: "A \<equiv> gfp f \<Longrightarrow> mono f \<Longrightarrow> A = f A"
  by (auto intro!: gfp_unfold)

lemma def_coinduct: "A \<equiv> gfp f \<Longrightarrow> mono f \<Longrightarrow> X \<le> f (sup X A) \<Longrightarrow> X \<le> A"
  by (iprover intro!: coinduct)

lemma def_coinduct_set: "A \<equiv> gfp f \<Longrightarrow> mono f \<Longrightarrow> a \<in> X \<Longrightarrow> X \<subseteq> f (X \<union> A) \<Longrightarrow> a \<in> A"
  by (auto intro!: coinduct_set)

lemma def_Collect_coinduct:
  "A \<equiv> gfp (\<lambda>w. Collect (P w)) \<Longrightarrow> mono (\<lambda>w. Collect (P w)) \<Longrightarrow> a \<in> X \<Longrightarrow>
    (\<And>z. z \<in> X \<Longrightarrow> P (X \<union> A) z) \<Longrightarrow> a \<in> A"
  by (erule def_coinduct_set) auto

lemma def_coinduct3: "A \<equiv> gfp f \<Longrightarrow> mono f \<Longrightarrow> a \<in> X \<Longrightarrow> X \<subseteq> f (lfp (\<lambda>x. f x \<union> X \<union> A)) \<Longrightarrow> a \<in> A"
  by (auto intro!: coinduct3)

text \<open>Monotonicity of \<^term>\<open>gfp\<close>!\<close>
lemma gfp_mono: "(\<And>Z. f Z \<le> g Z) \<Longrightarrow> gfp f \<le> gfp g"
  by (rule gfp_upperbound [THEN gfp_least]) (blast intro: order_trans)


subsection \<open>Rules for fixed point calculus\<close>

lemma lfp_rolling:
  assumes "mono g" "mono f"
  shows "g (lfp (\<lambda>x. f (g x))) = lfp (\<lambda>x. g (f x))"
proof (rule antisym)
  have *: "mono (\<lambda>x. f (g x))"
    using assms by (auto simp: mono_def)
  show "lfp (\<lambda>x. g (f x)) \<le> g (lfp (\<lambda>x. f (g x)))"
    by (rule lfp_lowerbound) (simp add: lfp_unfold[OF *, symmetric])
  show "g (lfp (\<lambda>x. f (g x))) \<le> lfp (\<lambda>x. g (f x))"
  proof (rule lfp_greatest)
    fix u
    assume u: "g (f u) \<le> u"
    then have "g (lfp (\<lambda>x. f (g x))) \<le> g (f u)"
      by (intro assms[THEN monoD] lfp_lowerbound)
    with u show "g (lfp (\<lambda>x. f (g x))) \<le> u"
      by auto
  qed
qed

lemma lfp_lfp:
  assumes f: "\<And>x y w z. x \<le> y \<Longrightarrow> w \<le> z \<Longrightarrow> f x w \<le> f y z"
  shows "lfp (\<lambda>x. lfp (f x)) = lfp (\<lambda>x. f x x)"
proof (rule antisym)
  have *: "mono (\<lambda>x. f x x)"
    by (blast intro: monoI f)
  show "lfp (\<lambda>x. lfp (f x)) \<le> lfp (\<lambda>x. f x x)"
    by (intro lfp_lowerbound) (simp add: lfp_unfold[OF *, symmetric])
  show "lfp (\<lambda>x. lfp (f x)) \<ge> lfp (\<lambda>x. f x x)" (is "?F \<ge> _")
  proof (intro lfp_lowerbound)
    have *: "?F = lfp (f ?F)"
      by (rule lfp_unfold) (blast intro: monoI lfp_mono f)
    also have "\<dots> = f ?F (lfp (f ?F))"
      by (rule lfp_unfold) (blast intro: monoI lfp_mono f)
    finally show "f ?F ?F \<le> ?F"
      by (simp add: *[symmetric])
  qed
qed

lemma gfp_rolling:
  assumes "mono g" "mono f"
  shows "g (gfp (\<lambda>x. f (g x))) = gfp (\<lambda>x. g (f x))"
proof (rule antisym)
  have *: "mono (\<lambda>x. f (g x))"
    using assms by (auto simp: mono_def)
  show "g (gfp (\<lambda>x. f (g x))) \<le> gfp (\<lambda>x. g (f x))"
    by (rule gfp_upperbound) (simp add: gfp_unfold[OF *, symmetric])
  show "gfp (\<lambda>x. g (f x)) \<le> g (gfp (\<lambda>x. f (g x)))"
  proof (rule gfp_least)
    fix u
    assume u: "u \<le> g (f u)"
    then have "g (f u) \<le> g (gfp (\<lambda>x. f (g x)))"
      by (intro assms[THEN monoD] gfp_upperbound)
    with u show "u \<le> g (gfp (\<lambda>x. f (g x)))"
      by auto
  qed
qed

lemma gfp_gfp:
  assumes f: "\<And>x y w z. x \<le> y \<Longrightarrow> w \<le> z \<Longrightarrow> f x w \<le> f y z"
  shows "gfp (\<lambda>x. gfp (f x)) = gfp (\<lambda>x. f x x)"
proof (rule antisym)
  have *: "mono (\<lambda>x. f x x)"
    by (blast intro: monoI f)
  show "gfp (\<lambda>x. f x x) \<le> gfp (\<lambda>x. gfp (f x))"
    by (intro gfp_upperbound) (simp add: gfp_unfold[OF *, symmetric])
  show "gfp (\<lambda>x. gfp (f x)) \<le> gfp (\<lambda>x. f x x)" (is "?F \<le> _")
  proof (intro gfp_upperbound)
    have *: "?F = gfp (f ?F)"
      by (rule gfp_unfold) (blast intro: monoI gfp_mono f)
    also have "\<dots> = f ?F (gfp (f ?F))"
      by (rule gfp_unfold) (blast intro: monoI gfp_mono f)
    finally show "?F \<le> f ?F ?F"
      by (simp add: *[symmetric])
  qed
qed


subsection \<open>Inductive predicates and sets\<close>

text \<open>Package setup.\<close>

lemmas basic_monos =
  subset_refl imp_refl disj_mono conj_mono ex_mono all_mono if_bool_eq_conj
  Collect_mono in_mono vimage_mono

lemma le_rel_bool_arg_iff: "X \<le> Y \<longleftrightarrow> X False \<le> Y False \<and> X True \<le> Y True"
  unfolding le_fun_def le_bool_def using bool_induct by auto

lemma imp_conj_iff: "((P \<longrightarrow> Q) \<and> P) = (P \<and> Q)"
  by blast

lemma meta_fun_cong: "P \<equiv> Q \<Longrightarrow> P a \<equiv> Q a"
  by auto

ML_file \<open>Tools/inductive.ML\<close>

lemmas [mono] =
  imp_refl disj_mono conj_mono ex_mono all_mono if_bool_eq_conj
  imp_mono not_mono
  Ball_def Bex_def
  induct_rulify_fallback


subsection \<open>The Schroeder-Bernstein Theorem\<close>

text \<open>
  See also:
  \<^item> \<^file>\<open>$ISABELLE_HOME/src/HOL/ex/Set_Theory.thy\<close>
  \<^item> \<^url>\<open>http://planetmath.org/proofofschroederbernsteintheoremusingtarskiknastertheorem\<close>
  \<^item> Springer LNCS 828 (cover page)
\<close>

theorem Schroeder_Bernstein:
  fixes f :: "'a \<Rightarrow> 'b" and g :: "'b \<Rightarrow> 'a"
    and A :: "'a set" and B :: "'b set"
  assumes inj1: "inj_on f A" and sub1: "f ` A \<subseteq> B"
    and inj2: "inj_on g B" and sub2: "g ` B \<subseteq> A"
  shows "\<exists>h. bij_betw h A B"
proof (rule exI, rule bij_betw_imageI)
  define X where "X = lfp (\<lambda>X. A - (g ` (B - (f ` X))))"
  define g' where "g' = the_inv_into (B - (f ` X)) g"
  let ?h = "\<lambda>z. if z \<in> X then f z else g' z"

  have X: "X = A - (g ` (B - (f ` X)))"
    unfolding X_def by (rule lfp_unfold) (blast intro: monoI)
  then have X_compl: "A - X = g ` (B - (f ` X))"
    using sub2 by blast

  from inj2 have inj2': "inj_on g (B - (f ` X))"
    by (rule inj_on_subset) auto
  with X_compl have *: "g' ` (A - X) = B - (f ` X)"
    by (simp add: g'_def)

  from X have X_sub: "X \<subseteq> A" by auto
  from X sub1 have fX_sub: "f ` X \<subseteq> B" by auto

  show "?h ` A = B"
  proof -
    from X_sub have "?h ` A = ?h ` (X \<union> (A - X))" by auto
    also have "\<dots> = ?h ` X \<union> ?h ` (A - X)" by (simp only: image_Un)
    also have "?h ` X = f ` X" by auto
    also from * have "?h ` (A - X) = B - (f ` X)" by auto
    also from fX_sub have "f ` X \<union> (B - f ` X) = B" by blast
    finally show ?thesis .
  qed
  show "inj_on ?h A"
  proof -
    from inj1 X_sub have on_X: "inj_on f X"
      by (rule subset_inj_on)

    have on_X_compl: "inj_on g' (A - X)"
      unfolding g'_def X_compl
      by (rule inj_on_the_inv_into) (rule inj2')

    have impossible: False if eq: "f a = g' b" and a: "a \<in> X" and b: "b \<in> A - X" for a b
    proof -
      from a have fa: "f a \<in> f ` X" by (rule imageI)
      from b have "g' b \<in> g' ` (A - X)" by (rule imageI)
      with * have "g' b \<in> - (f ` X)" by simp
      with eq fa show False by simp
    qed

    show ?thesis
    proof (rule inj_onI)
      fix a b
      assume h: "?h a = ?h b"
      assume "a \<in> A" and "b \<in> A"
      then consider "a \<in> X" "b \<in> X" | "a \<in> A - X" "b \<in> A - X"
        | "a \<in> X" "b \<in> A - X" | "a \<in> A - X" "b \<in> X"
        by blast
      then show "a = b"
      proof cases
        case 1
        with h on_X show ?thesis by (simp add: inj_on_eq_iff)
      next
        case 2
        with h on_X_compl show ?thesis by (simp add: inj_on_eq_iff)
      next
        case 3
        with h impossible [of a b] have False by simp
        then show ?thesis ..
      next
        case 4
        with h impossible [of b a] have False by simp
        then show ?thesis ..
      qed
    qed
  qed
qed


subsection \<open>Inductive datatypes and primitive recursion\<close>

text \<open>Package setup.\<close>

ML_file \<open>Tools/Old_Datatype/old_datatype_aux.ML\<close>
ML_file \<open>Tools/Old_Datatype/old_datatype_prop.ML\<close>
ML_file \<open>Tools/Old_Datatype/old_datatype_data.ML\<close>
ML_file \<open>Tools/Old_Datatype/old_rep_datatype.ML\<close>
ML_file \<open>Tools/Old_Datatype/old_datatype_codegen.ML\<close>
ML_file \<open>Tools/BNF/bnf_fp_rec_sugar_util.ML\<close>
ML_file \<open>Tools/Old_Datatype/old_primrec.ML\<close>
ML_file \<open>Tools/BNF/bnf_lfp_rec_sugar.ML\<close>

text \<open>Lambda-abstractions with pattern matching:\<close>
syntax (ASCII)
  "_lam_pats_syntax" :: "cases_syn \<Rightarrow> 'a \<Rightarrow> 'b"  (\<open>(\<open>notation=abstraction\<close>%_)\<close> 10)
syntax
  "_lam_pats_syntax" :: "cases_syn \<Rightarrow> 'a \<Rightarrow> 'b"  (\<open>(\<open>notation=abstraction\<close>\<lambda>_)\<close> 10)
parse_translation \<open>
  let
    fun fun_tr ctxt [cs] =
      let
        val x = Syntax.free (fst (Name.variant "x" (Term.declare_term_frees cs Name.context)));
        val ft = Case_Translation.case_tr true ctxt [x, cs];
      in lambda x ft end
  in [(\<^syntax_const>\<open>_lam_pats_syntax\<close>, fun_tr)] end
\<close>

end
