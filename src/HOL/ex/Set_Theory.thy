(*  Title:      HOL/ex/Set_Theory.thy
    Author:     Tobias Nipkow and Lawrence C Paulson
    Copyright   1991  University of Cambridge
*)

section \<open>Set Theory examples: Cantor's Theorem, Schröder-Bernstein Theorem, etc.\<close>

theory Set_Theory
imports Main
begin

text\<open>
  These two are cited in Benzmueller and Kohlhase's system description
  of LEO, CADE-15, 1998 (pages 139-143) as theorems LEO could not
  prove.
\<close>

lemma "(X = Y \<union> Z) =
    (Y \<subseteq> X \<and> Z \<subseteq> X \<and> (\<forall>V. Y \<subseteq> V \<and> Z \<subseteq> V \<longrightarrow> X \<subseteq> V))"
  by blast

lemma "(X = Y \<inter> Z) =
    (X \<subseteq> Y \<and> X \<subseteq> Z \<and> (\<forall>V. V \<subseteq> Y \<and> V \<subseteq> Z \<longrightarrow> V \<subseteq> X))"
  by blast

text \<open>
  Trivial example of term synthesis: apparently hard for some provers!
\<close>

schematic_goal "a \<noteq> b \<Longrightarrow> a \<in> ?X \<and> b \<notin> ?X"
  by blast


subsection \<open>Examples for the \<open>blast\<close> paper\<close>

lemma "(\<Union>x \<in> C. f x \<union> g x) = \<Union>(f ` C)  \<union>  \<Union>(g ` C)"
  \<comment> \<open>Union-image, called \<open>Un_Union_image\<close> in Main HOL\<close>
  by blast

lemma "(\<Inter>x \<in> C. f x \<inter> g x) = \<Inter>(f ` C) \<inter> \<Inter>(g ` C)"
  \<comment> \<open>Inter-image, called \<open>Int_Inter_image\<close> in Main HOL\<close>
  by blast

lemma singleton_example_1:
     "\<And>S::'a set set. \<forall>x \<in> S. \<forall>y \<in> S. x \<subseteq> y \<Longrightarrow> \<exists>z. S \<subseteq> {z}"
  by blast

lemma singleton_example_2:
     "\<forall>x \<in> S. \<Union>S \<subseteq> x \<Longrightarrow> \<exists>z. S \<subseteq> {z}"
  \<comment> \<open>Variant of the problem above.\<close>
  by blast

lemma "\<exists>!x. f (g x) = x \<Longrightarrow> \<exists>!y. g (f y) = y"
  \<comment> \<open>A unique fixpoint theorem --- \<open>fast\<close>/\<open>best\<close>/\<open>meson\<close> all fail.\<close>
  by metis


subsection \<open>Cantor's Theorem: There is no surjection from a set to its powerset\<close>

lemma cantor1: "\<not> (\<exists>f:: 'a \<Rightarrow> 'a set. \<forall>S. \<exists>x. f x = S)"
  \<comment> \<open>Requires best-first search because it is undirectional.\<close>
  by best

schematic_goal "\<forall>f:: 'a \<Rightarrow> 'a set. \<forall>x. f x \<noteq> ?S f"
  \<comment> \<open>This form displays the diagonal term.\<close>
  by best

schematic_goal "?S \<notin> range (f :: 'a \<Rightarrow> 'a set)"
  \<comment> \<open>This form exploits the set constructs.\<close>
  by (rule notI, erule rangeE, best)

schematic_goal "?S \<notin> range (f :: 'a \<Rightarrow> 'a set)"
  \<comment> \<open>Or just this!\<close>
  by best


subsection \<open>The Schröder-Bernstein Theorem\<close>

lemma decomposition: 
  obtains X where "X = - (g ` (- (f ` X)))"
  using lfp_unfold [OF monoI, of "\<lambda>X. - g ` (- f ` X)"]
  by blast

theorem Schroeder_Bernstein:
  fixes f :: "'a \<Rightarrow> 'b" and g :: "'b \<Rightarrow> 'a"
  assumes "inj f" "inj g"
  obtains h:: "'a \<Rightarrow> 'b" where "inj h" "surj h"
proof (rule decomposition)
  fix X
  assume X: "X = - (g ` (- (f ` X)))"
  let ?h = "\<lambda>z. if z \<in> X then f z else inv g z"
  show thesis
  proof
    have "inj_on (inv g) (-X)"
      by (metis X \<open>inj g\<close> bij_betw_def double_complement inj_imp_bij_betw_inv)
    with \<open>inj f\<close> show "inj ?h"
      unfolding inj_on_def by (metis Compl_iff X \<open>inj g\<close> imageI image_inv_f_f)
    show "surj ?h"
      using \<open>inj g\<close> X image_iff surj_def by fastforce
  qed
qed

subsection \<open>A simple party theorem\<close>

text\<open>\emph{At any party there are two people who know the same
number of people}. Provided the party consists of at least two people
and the knows relation is symmetric. Knowing yourself does not count
--- otherwise knows needs to be reflexive. (From Freek Wiedijk's talk
at TPHOLs 2007.)\<close>

lemma equal_number_of_acquaintances:
assumes "Domain R <= A" and "sym R" and "card A \<ge> 2"
shows "\<not> inj_on (%a. card(R `` {a} - {a})) A"
proof -
  let ?N = "%a. card(R `` {a} - {a})"
  let ?n = "card A"
  have "finite A" using \<open>card A \<ge> 2\<close> by(auto intro:ccontr)
  have 0: "R `` A <= A" using \<open>sym R\<close> \<open>Domain R <= A\<close>
    unfolding Domain_unfold sym_def by blast
  have h: "\<forall>a\<in>A. R `` {a} <= A" using 0 by blast
  hence 1: "\<forall>a\<in>A. finite(R `` {a})" using \<open>finite A\<close>
    by(blast intro: finite_subset)
  have sub: "?N ` A <= {0..<?n}"
  proof -
    have "\<forall>a\<in>A. R `` {a} - {a} < A" using h by blast
    thus ?thesis using psubset_card_mono[OF \<open>finite A\<close>] by auto
  qed
  show "~ inj_on ?N A" (is "~ ?I")
  proof
    assume ?I
    hence "?n = card(?N ` A)" by(rule card_image[symmetric])
    with sub \<open>finite A\<close> have 2[simp]: "?N ` A = {0..<?n}"
      using subset_card_intvl_is_intvl[of _ 0] by(auto)
    have "0 \<in> ?N ` A" and "?n - 1 \<in> ?N ` A"  using \<open>card A \<ge> 2\<close> by simp+
    then obtain a b where ab: "a\<in>A" "b\<in>A" and Na: "?N a = 0" and Nb: "?N b = ?n - 1"
      by (auto simp del: 2)
    have "a \<noteq> b" using Na Nb \<open>card A \<ge> 2\<close> by auto
    have "R `` {a} - {a} = {}" by (metis 1 Na ab card_eq_0_iff finite_Diff)
    hence "b \<notin> R `` {a}" using \<open>a\<noteq>b\<close> by blast
    hence "a \<notin> R `` {b}" by (metis Image_singleton_iff assms(2) sym_def)
    hence 3: "R `` {b} - {b} <= A - {a,b}" using 0 ab by blast
    have 4: "finite (A - {a,b})" using \<open>finite A\<close> by simp
    have "?N b <= ?n - 2" using ab \<open>a\<noteq>b\<close> \<open>finite A\<close> card_mono[OF 4 3] by simp
    then show False using Nb \<open>card A \<ge>  2\<close> by arith
  qed
qed

text \<open>
  From W. W. Bledsoe and Guohui Feng, SET-VAR. JAR 11 (3), 1993, pages
  293-314.

  Isabelle can prove the easy examples without any special mechanisms,
  but it can't prove the hard ones.
\<close>

lemma "\<exists>A. (\<forall>x \<in> A. x \<le> (0::int))"
  \<comment> \<open>Example 1, page 295.\<close>
  by force

lemma "D \<in> F \<Longrightarrow> \<exists>G. \<forall>A \<in> G. \<exists>B \<in> F. A \<subseteq> B"
  \<comment> \<open>Example 2.\<close>
  by force

lemma "P a \<Longrightarrow> \<exists>A. (\<forall>x \<in> A. P x) \<and> (\<exists>y. y \<in> A)"
  \<comment> \<open>Example 3.\<close>
  by force

lemma "a < b \<and> b < (c::int) \<Longrightarrow> \<exists>A. a \<notin> A \<and> b \<in> A \<and> c \<notin> A"
  \<comment> \<open>Example 4.\<close>
  by auto \<comment> \<open>slow\<close>

lemma "P (f b) \<Longrightarrow> \<exists>s A. (\<forall>x \<in> A. P x) \<and> f s \<in> A"
  \<comment> \<open>Example 5, page 298.\<close>
  by force

lemma "P (f b) \<Longrightarrow> \<exists>s A. (\<forall>x \<in> A. P x) \<and> f s \<in> A"
  \<comment> \<open>Example 6.\<close>
  by force

lemma "\<exists>A. a \<notin> A"
  \<comment> \<open>Example 7.\<close>
  by force

lemma "(\<forall>u v. u < (0::int) \<longrightarrow> u \<noteq> \<bar>v\<bar>)
    \<longrightarrow> (\<exists>A::int set. -2 \<in> A & (\<forall>y. \<bar>y\<bar> \<notin> A))"
  \<comment> \<open>Example 8 needs a small hint.\<close>
  by force
    \<comment> \<open>not \<open>blast\<close>, which can't simplify \<open>-2 < 0\<close>\<close>

text \<open>Example 9 omitted (requires the reals).\<close>

text \<open>The paper has no Example 10!\<close>

lemma "(\<forall>A. 0 \<in> A \<and> (\<forall>x \<in> A. Suc x \<in> A) \<longrightarrow> n \<in> A) \<and>
  P 0 \<and> (\<forall>x. P x \<longrightarrow> P (Suc x)) \<longrightarrow> P n"
  \<comment> \<open>Example 11: needs a hint.\<close>
by(metis nat.induct)

lemma
  "(\<forall>A. (0, 0) \<in> A \<and> (\<forall>x y. (x, y) \<in> A \<longrightarrow> (Suc x, Suc y) \<in> A) \<longrightarrow> (n, m) \<in> A)
    \<and> P n \<longrightarrow> P m"
  \<comment> \<open>Example 12.\<close>
  by auto

lemma
  "(\<forall>x. (\<exists>u. x = 2 * u) = (\<not> (\<exists>v. Suc x = 2 * v))) \<longrightarrow>
    (\<exists>A. \<forall>x. (x \<in> A) = (Suc x \<notin> A))"
  \<comment> \<open>Example EO1: typo in article, and with the obvious fix it seems
      to require arithmetic reasoning. 2024-06-19: now trivial for sledgehammer (LCP)\<close>
  by (metis even_Suc mem_Collect_eq)

end
