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

constdefs
  is_seminorm :: "'a::{plus, minus, zero} set \<Rightarrow> ('a \<Rightarrow> real) \<Rightarrow> bool"
  "is_seminorm V norm \<equiv> \<forall>x \<in> V. \<forall>y \<in> V. \<forall>a.
        0 \<le> norm x
      \<and> norm (a \<cdot> x) = \<bar>a\<bar> * norm x
      \<and> norm (x + y) \<le> norm x + norm y"

lemma is_seminormI [intro]:
  "(\<And>x y a. x \<in> V \<Longrightarrow> y \<in> V \<Longrightarrow> 0 \<le> norm x) \<Longrightarrow>
  (\<And>x a. x \<in> V \<Longrightarrow> norm (a \<cdot> x) = \<bar>a\<bar> * norm x) \<Longrightarrow>
  (\<And>x y. x \<in> V \<Longrightarrow> y \<in> V \<Longrightarrow> norm (x + y) \<le> norm x + norm y)
  \<Longrightarrow> is_seminorm V norm"
  by (unfold is_seminorm_def) auto

lemma seminorm_ge_zero [intro?]:
  "is_seminorm V norm \<Longrightarrow> x \<in> V \<Longrightarrow> 0 \<le> norm x"
  by (unfold is_seminorm_def) blast

lemma seminorm_abs_homogenous:
  "is_seminorm V norm \<Longrightarrow> x \<in> V
  \<Longrightarrow> norm (a \<cdot> x) = \<bar>a\<bar> * norm x"
  by (unfold is_seminorm_def) blast

lemma seminorm_subadditive:
  "is_seminorm V norm \<Longrightarrow> x \<in> V \<Longrightarrow> y \<in> V
  \<Longrightarrow> norm (x + y) \<le> norm x + norm y"
  by (unfold is_seminorm_def) blast

lemma seminorm_diff_subadditive:
  "is_seminorm V norm \<Longrightarrow> x \<in> V \<Longrightarrow> y \<in> V \<Longrightarrow> is_vectorspace V
  \<Longrightarrow> norm (x - y) \<le> norm x + norm y"
proof -
  assume "is_seminorm V norm"  "x \<in> V"  "y \<in> V"  "is_vectorspace V"
  have "norm (x - y) = norm (x + - 1 \<cdot> y)"
    by (simp! add: diff_eq2 negate_eq2a)
  also have "... \<le> norm x + norm  (- 1 \<cdot> y)"
    by (simp! add: seminorm_subadditive)
  also have "norm (- 1 \<cdot> y) = \<bar>- 1\<bar> * norm y"
    by (rule seminorm_abs_homogenous)
  also have "\<bar>- 1\<bar> = (1::real)" by (rule abs_minus_one)
  finally show "norm (x - y) \<le> norm x + norm y" by simp
qed

lemma seminorm_minus:
  "is_seminorm V norm \<Longrightarrow> x \<in> V \<Longrightarrow> is_vectorspace V
  \<Longrightarrow> norm (- x) = norm x"
proof -
  assume "is_seminorm V norm"  "x \<in> V"  "is_vectorspace V"
  have "norm (- x) = norm (- 1 \<cdot> x)" by (simp! only: negate_eq1)
  also have "... = \<bar>- 1\<bar> * norm x"
    by (rule seminorm_abs_homogenous)
  also have "\<bar>- 1\<bar> = (1::real)" by (rule abs_minus_one)
  finally show "norm (- x) = norm x" by simp
qed


subsection {* Norms *}

text {*
  A \emph{norm} @{text "\<parallel>\<cdot>\<parallel>"} is a seminorm that maps only the
  @{text 0} vector to @{text 0}.
*}

constdefs
  is_norm :: "'a::{plus, minus, zero} set \<Rightarrow> ('a \<Rightarrow> real) \<Rightarrow> bool"
  "is_norm V norm \<equiv> \<forall>x \<in> V. is_seminorm V norm
      \<and> (norm x = 0) = (x = 0)"

lemma is_normI [intro]:
  "\<forall>x \<in> V.  is_seminorm V norm  \<and> (norm x = 0) = (x = 0)
  \<Longrightarrow> is_norm V norm" by (simp only: is_norm_def)

lemma norm_is_seminorm [intro?]:
  "is_norm V norm \<Longrightarrow> x \<in> V \<Longrightarrow> is_seminorm V norm"
  by (unfold is_norm_def) blast

lemma norm_zero_iff:
  "is_norm V norm \<Longrightarrow> x \<in> V \<Longrightarrow> (norm x = 0) = (x = 0)"
  by (unfold is_norm_def) blast

lemma norm_ge_zero [intro?]:
  "is_norm V norm \<Longrightarrow> x \<in> V \<Longrightarrow> 0 \<le> norm x"
  by (unfold is_norm_def is_seminorm_def) blast


subsection {* Normed vector spaces *}

text{* A vector space together with a norm is called
a \emph{normed space}. *}

constdefs
  is_normed_vectorspace ::
  "'a::{plus, minus, zero} set \<Rightarrow> ('a \<Rightarrow> real) \<Rightarrow> bool"
  "is_normed_vectorspace V norm \<equiv>
      is_vectorspace V \<and> is_norm V norm"

lemma normed_vsI [intro]:
  "is_vectorspace V \<Longrightarrow> is_norm V norm
  \<Longrightarrow> is_normed_vectorspace V norm"
  by (unfold is_normed_vectorspace_def) blast

lemma normed_vs_vs [intro?]:
  "is_normed_vectorspace V norm \<Longrightarrow> is_vectorspace V"
  by (unfold is_normed_vectorspace_def) blast

lemma normed_vs_norm [intro?]:
  "is_normed_vectorspace V norm \<Longrightarrow> is_norm V norm"
  by (unfold is_normed_vectorspace_def) blast

lemma normed_vs_norm_ge_zero [intro?]:
  "is_normed_vectorspace V norm \<Longrightarrow> x \<in> V \<Longrightarrow> 0 \<le> norm x"
  by (unfold is_normed_vectorspace_def) (fast elim: norm_ge_zero)

lemma normed_vs_norm_gt_zero [intro?]:
  "is_normed_vectorspace V norm \<Longrightarrow> x \<in> V \<Longrightarrow> x \<noteq> 0 \<Longrightarrow> 0 < norm x"
proof (unfold is_normed_vectorspace_def, elim conjE)
  assume "x \<in> V"  "x \<noteq> 0"  "is_vectorspace V"  "is_norm V norm"
  have "0 \<le> norm x" ..
  also have "0 \<noteq> norm x"
  proof
    presume "norm x = 0"
    also have "?this = (x = 0)" by (rule norm_zero_iff)
    finally have "x = 0" .
    thus "False" by contradiction
  qed (rule sym)
  finally show "0 < norm x" .
qed

lemma normed_vs_norm_abs_homogenous [intro?]:
  "is_normed_vectorspace V norm \<Longrightarrow> x \<in> V
  \<Longrightarrow> norm (a \<cdot> x) = \<bar>a\<bar> * norm x"
  by (rule seminorm_abs_homogenous, rule norm_is_seminorm,
      rule normed_vs_norm)

lemma normed_vs_norm_subadditive [intro?]:
  "is_normed_vectorspace V norm \<Longrightarrow> x \<in> V \<Longrightarrow> y \<in> V
  \<Longrightarrow> norm (x + y) \<le> norm x + norm y"
  by (rule seminorm_subadditive, rule norm_is_seminorm,
     rule normed_vs_norm)

text{* Any subspace of a normed vector space is again a
normed vectorspace.*}

lemma subspace_normed_vs [intro?]:
  "is_vectorspace E \<Longrightarrow> is_subspace F E \<Longrightarrow>
  is_normed_vectorspace E norm \<Longrightarrow> is_normed_vectorspace F norm"
proof (rule normed_vsI)
  assume "is_subspace F E"  "is_vectorspace E"
         "is_normed_vectorspace E norm"
  show "is_vectorspace F" ..
  show "is_norm F norm"
  proof (intro is_normI ballI conjI)
    show "is_seminorm F norm"
    proof
      fix x y a presume "x \<in> E"
      show "0 \<le> norm x" ..
      show "norm (a \<cdot> x) = \<bar>a\<bar> * norm x" ..
      presume "y \<in> E"
      show "norm (x + y) \<le> norm x + norm y" ..
    qed (simp!)+

    fix x assume "x \<in> F"
    show "(norm x = 0) = (x = 0)"
    proof (rule norm_zero_iff)
      show "is_norm E norm" ..
    qed (simp!)
  qed
qed

end
