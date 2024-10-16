(* Author: Johannes Hölzl <hoelzl@in.tum.de> *)

section \<open>The Category of Measurable Spaces is not Cartesian Closed\<close>

theory Measure_Not_CCC
  imports "HOL-Probability.Probability"
begin

text \<open>
  We show that the category of measurable spaces with measurable functions as morphisms is not a
  Cartesian closed category. While the category has products and terminal objects, the exponential
  does not exist for each pair of measurable spaces.

  We show that the exponential $\mathbb{B}^\mathbb{C}$ does not exist, where $\mathbb{B}$ is the
  discrete measurable space on boolean values, and $\mathbb{C}$ is the $\sigma$-algebra consisting
  of all countable and co-countable real sets. We also define $\mathbb{R}$ to be the discrete
  measurable space on the reals.

  Now, the diagonal predicate \<^term>\<open>\<lambda>x y. x = y\<close> is $\mathbb{R}$-$\mathbb{B}^\mathbb{C}$-measurable,
  but \<^term>\<open>\<lambda>(x, y). x = y\<close> is not $(\mathbb{R} \times \mathbb{C})$-$\mathbb{B}$-measurable.
\<close>

definition COCOUNT :: "real measure" where
  "COCOUNT = sigma UNIV {{x} | x. True}"

abbreviation POW :: "real measure" where
  "POW \<equiv> count_space UNIV"

abbreviation BOOL :: "bool measure" where
  "BOOL \<equiv> count_space UNIV"

lemma measurable_const_iff: "(\<lambda>x. c) \<in> measurable A B \<longleftrightarrow> (space A = {} \<or> c \<in> space B)"
  by (auto simp: measurable_def)

lemma measurable_eq[measurable]: "((=) x) \<in> measurable COCOUNT BOOL"
  unfolding pred_def by (auto simp: COCOUNT_def)

lemma COCOUNT_eq: "A \<in> COCOUNT \<longleftrightarrow> countable A \<or> countable (UNIV - A)"
proof
  fix A assume "A \<in> COCOUNT"
  then have "A \<in> sigma_sets UNIV {{x} | x. True}"
    by (auto simp: COCOUNT_def)
  then show "countable A \<or> countable (UNIV - A)"
  proof induction
    case (Union F)
    moreover
    have "countable (UNIV - (\<Union>i. F i))" if "countable (UNIV - F i)" for i
      using that by (rule countable_subset[rotated]) auto
    ultimately show "countable (\<Union>i. F i) \<or> countable (UNIV - (\<Union>i. F i))"
      by blast
  qed (auto simp: Diff_Diff_Int)
next
  assume "countable A \<or> countable (UNIV - A)"
  moreover
  have A: "A \<in> COCOUNT" if "countable A" for A :: "real set"
  proof -
    have "A = (\<Union>a\<in>A. {a})"
      by auto
    also have "\<dots> \<in> COCOUNT"
      by (intro sets.countable_UN' that) (auto simp: COCOUNT_def) 
    finally show ?thesis .
  qed
  note A[of A]
  moreover
  have "A \<in> COCOUNT" if "countable (UNIV - A)"
  proof -
    from A that have "space COCOUNT - (UNIV - A) \<in> COCOUNT" by simp
    then show ?thesis
      by (auto simp: COCOUNT_def Diff_Diff_Int)
  qed
  ultimately show "A \<in> COCOUNT" 
    by blast
qed

lemma pair_COCOUNT:
  assumes A: "A \<in> sets (COCOUNT \<Otimes>\<^sub>M M)"
  shows "\<exists>J F X. X \<in> sets M \<and> F \<in> J \<rightarrow> sets M \<and> countable J \<and> A = (UNIV - J) \<times> X \<union> (SIGMA j:J. F j)"
  using A unfolding sets_pair_measure
proof induction
  case (Basic X)
  then obtain a b where X: "X = a \<times> b" and b: "b \<in> sets M" and a: "countable a \<or> countable (UNIV - a)"
    by (auto simp: COCOUNT_eq)
  from a show ?case
  proof 
    assume "countable a" with X b show ?thesis
      by (intro exI[of _ a] exI[of _ "\<lambda>_. b"] exI[of _ "{}"]) auto
  next
    assume "countable (UNIV - a)" with X b show ?thesis
      by (intro exI[of _ "UNIV - a"] exI[of _ "\<lambda>_. {}"] exI[of _ "b"]) auto
  qed
next
  case Empty then show ?case
    by (intro exI[of _ "{}"] exI[of _ "\<lambda>_. {}"] exI[of _ "{}"]) auto
next
  case (Compl A)
  then obtain J F X where XFJ: "X \<in> sets M" "F \<in> J \<rightarrow> sets M" "countable J"
    and A: "A = (UNIV - J) \<times> X \<union> Sigma J F"
    by auto
  have *: "space COCOUNT \<times> space M - A = (UNIV - J) \<times> (space M - X) \<union> (SIGMA j:J. space M - F j)"
    unfolding A by (auto simp: COCOUNT_def)
  show ?case
    using XFJ unfolding *
    by (intro exI[of _ J] exI[of _ "space M - X"] exI[of _ "\<lambda>j. space M - F j"]) auto
next
  case (Union A)
  obtain J F X where XFJ: "\<And>i. X i \<in> sets M" "\<And>i. F i \<in> J i \<rightarrow> sets M" "\<And>i. countable (J i)"
    and A_eq: "A = (\<lambda>i. (UNIV - J i) \<times> X i \<union> Sigma (J i) (F i))"
    unfolding fun_eq_iff using Union.IH by metis
  show ?case
  proof (intro exI conjI)
    define G where "G j = (\<Union>i. if j \<in> J i then F i j else X i)" for j
    show "(\<Union>i. X i) \<in> sets M" "countable (\<Union>i. J i)" "G \<in> (\<Union>i. J i) \<rightarrow> sets M"
      using XFJ by (auto simp: G_def Pi_iff)
    show "\<Union>(A ` UNIV) = (UNIV - (\<Union>i. J i)) \<times> (\<Union>i. X i) \<union> (SIGMA j:\<Union>i. J i. \<Union>i. if j \<in> J i then F i j else X i)"
      unfolding A_eq by (auto split: if_split_asm)
  qed
qed

context
  fixes EXP :: "(real \<Rightarrow> bool) measure"
  assumes eq: "\<And>P. case_prod P \<in> measurable (POW \<Otimes>\<^sub>M COCOUNT) BOOL \<longleftrightarrow> P \<in> measurable POW EXP"
begin

lemma space_EXP: "space EXP = measurable COCOUNT BOOL"
proof -
  have "f \<in> space EXP \<longleftrightarrow> f \<in> measurable COCOUNT BOOL" for f
  proof -
    have "f \<in> space EXP \<longleftrightarrow> (\<lambda>(a, b). f b) \<in> measurable (POW \<Otimes>\<^sub>M COCOUNT) BOOL"
      using eq[of "\<lambda>x. f"] by (simp add: measurable_const_iff)
    also have "\<dots> \<longleftrightarrow> f \<in> measurable COCOUNT BOOL"
      by auto
    finally show ?thesis .
  qed
  then show ?thesis by auto
qed

lemma measurable_eq_EXP: "(\<lambda>x y. x = y) \<in> measurable POW EXP"
  unfolding measurable_def by (auto simp: space_EXP)

lemma measurable_eq_pair: "(\<lambda>(y, x). x = y) \<in> measurable (COCOUNT \<Otimes>\<^sub>M POW) BOOL"
  using measurable_eq_EXP unfolding eq[symmetric]
  by (subst measurable_pair_swap_iff) simp

lemma ce: False
proof -
  have "{(y, x) \<in> space (COCOUNT \<Otimes>\<^sub>M POW). x = y} \<in> sets (COCOUNT \<Otimes>\<^sub>M POW)"
    using measurable_eq_pair unfolding pred_def by (simp add: split_beta')
  also have "{(y, x) \<in> space (COCOUNT \<Otimes>\<^sub>M POW). x = y} = (SIGMA j:UNIV. {j})"
    by (auto simp: space_pair_measure COCOUNT_def)
  finally obtain X F J where "countable (J::real set)"
    and eq: "(SIGMA j:UNIV. {j}) = (UNIV - J) \<times> X \<union> (SIGMA j:J. F j)"
    using pair_COCOUNT[of "SIGMA j:UNIV. {j}" POW] by auto
  have X_single: "\<And>x. x \<notin> J \<Longrightarrow> X = {x}"
    using eq[unfolded set_eq_iff] by force
  
  have "uncountable (UNIV - J)"
    using \<open>countable J\<close> uncountable_UNIV_real uncountable_minus_countable by blast
  then have "infinite (UNIV - J)"
    by (auto intro: countable_finite)
  then have "\<exists>A. finite A \<and> card A = 2 \<and> A \<subseteq> UNIV - J"
    by (rule infinite_arbitrarily_large)
  then obtain i j where ij: "i \<in> UNIV - J" "j \<in> UNIV - J" "i \<noteq> j"
    by (auto simp add: card_Suc_eq numeral_2_eq_2)
  have "{(i, i), (j, j)} \<subseteq> (SIGMA j:UNIV. {j})" by auto
  with ij X_single[of i] X_single[of j] show False
    by auto
qed

end

corollary "\<not> (\<exists>EXP. \<forall>P. case_prod P \<in> measurable (POW \<Otimes>\<^sub>M COCOUNT) BOOL \<longleftrightarrow> P \<in> measurable POW EXP)"
  using ce by blast

end

