(*  Title:      HOL/Real/HahnBanach/NormedSpace.thy
    ID:         $Id$
    Author:     Gertrud Bauer, TU Munich
*)

header {* Normed vector spaces *}

theory NormedSpace =  Subspace:

subsection {* Quasinorms *}

text {*
  A \emph{seminorm} @{text "\<parallel>\<cdot>\<parallel>"} is a function on a real vector space
  into the reals that has the following properties: it is positive
  definite, absolute homogenous and subadditive.
*}

locale norm_syntax =
  fixes norm :: "'a \<Rightarrow> real"    ("\<parallel>_\<parallel>")

locale seminorm = var V + norm_syntax +
  assumes ge_zero [iff?]: "x \<in> V \<Longrightarrow> 0 \<le> \<parallel>x\<parallel>"
    and abs_homogenous [iff?]: "x \<in> V \<Longrightarrow> \<parallel>a \<cdot> x\<parallel> = \<bar>a\<bar> * \<parallel>x\<parallel>"
    and subadditive [iff?]: "x \<in> V \<Longrightarrow> y \<in> V \<Longrightarrow> \<parallel>x + y\<parallel> \<le> \<parallel>x\<parallel> + \<parallel>y\<parallel>"

declare seminorm.intro [intro?]

lemma (in seminorm) diff_subadditive:
  includes vectorspace
  shows "x \<in> V \<Longrightarrow> y \<in> V \<Longrightarrow> \<parallel>x - y\<parallel> \<le> \<parallel>x\<parallel> + \<parallel>y\<parallel>"
proof -
  assume x: "x \<in> V" and y: "y \<in> V"
  hence "x - y = x + - 1 \<cdot> y"
    by (simp add: diff_eq2 negate_eq2a)
  also from x y have "\<parallel>\<dots>\<parallel> \<le> \<parallel>x\<parallel> + \<parallel>- 1 \<cdot> y\<parallel>"
    by (simp add: subadditive)
  also from y have "\<parallel>- 1 \<cdot> y\<parallel> = \<bar>- 1\<bar> * \<parallel>y\<parallel>"
    by (rule abs_homogenous)
  also have "\<dots> = \<parallel>y\<parallel>" by simp
  finally show ?thesis .
qed

lemma (in seminorm) minus:
  includes vectorspace
  shows "x \<in> V \<Longrightarrow> \<parallel>- x\<parallel> = \<parallel>x\<parallel>"
proof -
  assume x: "x \<in> V"
  hence "- x = - 1 \<cdot> x" by (simp only: negate_eq1)
  also from x have "\<parallel>\<dots>\<parallel> = \<bar>- 1\<bar> * \<parallel>x\<parallel>"
    by (rule abs_homogenous)
  also have "\<dots> = \<parallel>x\<parallel>" by simp
  finally show ?thesis .
qed


subsection {* Norms *}

text {*
  A \emph{norm} @{text "\<parallel>\<cdot>\<parallel>"} is a seminorm that maps only the
  @{text 0} vector to @{text 0}.
*}

locale norm = seminorm +
  assumes zero_iff [iff]: "x \<in> V \<Longrightarrow> (\<parallel>x\<parallel> = 0) = (x = 0)"


subsection {* Normed vector spaces *}

text {*
  A vector space together with a norm is called a \emph{normed
  space}.
*}

locale normed_vectorspace = vectorspace + norm

declare normed_vectorspace.intro [intro?]

lemma (in normed_vectorspace) gt_zero [intro?]:
  "x \<in> V \<Longrightarrow> x \<noteq> 0 \<Longrightarrow> 0 < \<parallel>x\<parallel>"
proof -
  assume x: "x \<in> V" and neq: "x \<noteq> 0"
  from x have "0 \<le> \<parallel>x\<parallel>" ..
  also have [symmetric]: "\<dots> \<noteq> 0"
  proof
    assume "\<parallel>x\<parallel> = 0"
    with x have "x = 0" by simp
    with neq show False by contradiction
  qed
  finally show ?thesis .
qed

text {*
  Any subspace of a normed vector space is again a normed vectorspace.
*}

lemma subspace_normed_vs [intro?]:
  includes subspace F E + normed_vectorspace E
  shows "normed_vectorspace F norm"
proof
  show "vectorspace F" by (rule vectorspace)
  have "seminorm E norm" . with subset show "seminorm F norm"
    by (simp add: seminorm_def)
  have "norm_axioms E norm" . with subset show "norm_axioms F norm"
    by (simp add: norm_axioms_def)
qed

end
