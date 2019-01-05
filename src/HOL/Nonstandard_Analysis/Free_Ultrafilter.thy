(*  Title:      HOL/Nonstandard_Analysis/Free_Ultrafilter.thy
    Author:     Jacques D. Fleuriot, University of Cambridge
    Author:     Lawrence C Paulson
    Author:     Brian Huffman
*)

section \<open>Filters and Ultrafilters\<close>

theory Free_Ultrafilter
  imports "HOL-Library.Infinite_Set"
begin


subsection \<open>Definitions and basic properties\<close>

subsubsection \<open>Ultrafilters\<close>

locale ultrafilter =
  fixes F :: "'a filter"
  assumes proper: "F \<noteq> bot"
  assumes ultra: "eventually P F \<or> eventually (\<lambda>x. \<not> P x) F"
begin

lemma eventually_imp_frequently: "frequently P F \<Longrightarrow> eventually P F"
  using ultra[of P] by (simp add: frequently_def)

lemma frequently_eq_eventually: "frequently P F = eventually P F"
  using eventually_imp_frequently eventually_frequently[OF proper] ..

lemma eventually_disj_iff: "eventually (\<lambda>x. P x \<or> Q x) F \<longleftrightarrow> eventually P F \<or> eventually Q F"
  unfolding frequently_eq_eventually[symmetric] frequently_disj_iff ..

lemma eventually_all_iff: "eventually (\<lambda>x. \<forall>y. P x y) F = (\<forall>Y. eventually (\<lambda>x. P x (Y x)) F)"
  using frequently_all[of P F] by (simp add: frequently_eq_eventually)

lemma eventually_imp_iff: "eventually (\<lambda>x. P x \<longrightarrow> Q x) F \<longleftrightarrow> (eventually P F \<longrightarrow> eventually Q F)"
  using frequently_imp_iff[of P Q F] by (simp add: frequently_eq_eventually)

lemma eventually_iff_iff: "eventually (\<lambda>x. P x \<longleftrightarrow> Q x) F \<longleftrightarrow> (eventually P F \<longleftrightarrow> eventually Q F)"
  unfolding iff_conv_conj_imp eventually_conj_iff eventually_imp_iff by simp

lemma eventually_not_iff: "eventually (\<lambda>x. \<not> P x) F \<longleftrightarrow> \<not> eventually P F"
  unfolding not_eventually frequently_eq_eventually ..

end


subsection \<open>Maximal filter = Ultrafilter\<close>

text \<open>
   A filter \<open>F\<close> is an ultrafilter iff it is a maximal filter,
   i.e. whenever \<open>G\<close> is a filter and \<^prop>\<open>F \<subseteq> G\<close> then \<^prop>\<open>F = G\<close>
\<close>

text \<open>
  Lemma that shows existence of an extension to what was assumed to
  be a maximal filter. Will be used to derive contradiction in proof of
  property of ultrafilter.
\<close>

lemma extend_filter: "frequently P F \<Longrightarrow> inf F (principal {x. P x}) \<noteq> bot"
  by (simp add: trivial_limit_def eventually_inf_principal not_eventually)

lemma max_filter_ultrafilter:
  assumes "F \<noteq> bot"
  assumes max: "\<And>G. G \<noteq> bot \<Longrightarrow> G \<le> F \<Longrightarrow> F = G"
  shows "ultrafilter F"
proof
  show "eventually P F \<or> (\<forall>\<^sub>Fx in F. \<not> P x)" for P
  proof (rule disjCI)
    assume "\<not> (\<forall>\<^sub>Fx in F. \<not> P x)"
    then have "inf F (principal {x. P x}) \<noteq> bot"
      by (simp add: not_eventually extend_filter)
    then have F: "F = inf F (principal {x. P x})"
      by (rule max) simp
    show "eventually P F"
      by (subst F) (simp add: eventually_inf_principal)
  qed
qed fact

lemma le_filter_frequently: "F \<le> G \<longleftrightarrow> (\<forall>P. frequently P F \<longrightarrow> frequently P G)"
  unfolding frequently_def le_filter_def
  apply auto
  apply (erule_tac x="\<lambda>x. \<not> P x" in allE)
  apply auto
  done

lemma (in ultrafilter) max_filter:
  assumes G: "G \<noteq> bot"
    and sub: "G \<le> F"
  shows "F = G"
proof (rule antisym)
  show "F \<le> G"
    using sub
    by (auto simp: le_filter_frequently[of F] frequently_eq_eventually le_filter_def[of G]
             intro!: eventually_frequently G proper)
qed fact


subsection \<open>Ultrafilter Theorem\<close>

lemma ex_max_ultrafilter:
  fixes F :: "'a filter"
  assumes F: "F \<noteq> bot"
  shows "\<exists>U\<le>F. ultrafilter U"
proof -
  let ?X = "{G. G \<noteq> bot \<and> G \<le> F}"
  let ?R = "{(b, a). a \<noteq> bot \<and> a \<le> b \<and> b \<le> F}"

  have bot_notin_R: "c \<in> Chains ?R \<Longrightarrow> bot \<notin> c" for c
    by (auto simp: Chains_def)

  have [simp]: "Field ?R = ?X"
    by (auto simp: Field_def bot_unique)

  have "\<exists>m\<in>Field ?R. \<forall>a\<in>Field ?R. (m, a) \<in> ?R \<longrightarrow> a = m" (is "\<exists>m\<in>?A. ?B m")
  proof (rule Zorns_po_lemma)
    show "Partial_order ?R"
      by (auto simp: partial_order_on_def preorder_on_def
          antisym_def refl_on_def trans_def Field_def bot_unique)
    show "\<exists>u\<in>Field ?R. \<forall>a\<in>C. (a, u) \<in> ?R" if C: "C \<in> Chains ?R" for C
    proof (simp, intro exI conjI ballI)
      have Inf_C: "Inf C \<noteq> bot" "Inf C \<le> F" if "C \<noteq> {}"
      proof -
        from C that have "Inf C = bot \<longleftrightarrow> (\<exists>x\<in>C. x = bot)"
          unfolding trivial_limit_def by (intro eventually_Inf_base) (auto simp: Chains_def)
        with C show "Inf C \<noteq> bot"
          by (simp add: bot_notin_R)
        from that obtain x where "x \<in> C" by auto
        with C show "Inf C \<le> F"
          by (auto intro!: Inf_lower2[of x] simp: Chains_def)
      qed
      then have [simp]: "inf F (Inf C) = (if C = {} then F else Inf C)"
        using C by (auto simp add: inf_absorb2)
      from C show "inf F (Inf C) \<noteq> bot"
        by (simp add: F Inf_C)
      from C show "inf F (Inf C) \<le> F"
        by (simp add: Chains_def Inf_C F)
      with C show "inf F (Inf C) \<le> x" "x \<le> F" if "x \<in> C" for x
        using that  by (auto intro: Inf_lower simp: Chains_def)
    qed
  qed
  then obtain U where U: "U \<in> ?A" "?B U" ..
  show ?thesis
  proof
    from U show "U \<le> F \<and> ultrafilter U"
      by (auto intro!: max_filter_ultrafilter)
  qed
qed


subsubsection \<open>Free Ultrafilters\<close>

text \<open>There exists a free ultrafilter on any infinite set.\<close>

locale freeultrafilter = ultrafilter +
  assumes infinite: "eventually P F \<Longrightarrow> infinite {x. P x}"
begin

lemma finite: "finite {x. P x} \<Longrightarrow> \<not> eventually P F"
  by (erule contrapos_pn) (erule infinite)

lemma finite': "finite {x. \<not> P x} \<Longrightarrow> eventually P F"
  by (drule finite) (simp add: not_eventually frequently_eq_eventually)

lemma le_cofinite: "F \<le> cofinite"
  by (intro filter_leI)
    (auto simp add: eventually_cofinite not_eventually frequently_eq_eventually dest!: finite)

lemma singleton: "\<not> eventually (\<lambda>x. x = a) F"
  by (rule finite) simp

lemma singleton': "\<not> eventually ((=) a) F"
  by (rule finite) simp

lemma ultrafilter: "ultrafilter F" ..

end

lemma freeultrafilter_Ex:
  assumes [simp]: "infinite (UNIV :: 'a set)"
  shows "\<exists>U::'a filter. freeultrafilter U"
proof -
  from ex_max_ultrafilter[of "cofinite :: 'a filter"]
  obtain U :: "'a filter" where "U \<le> cofinite" "ultrafilter U"
    by auto
  interpret ultrafilter U by fact
  have "freeultrafilter U"
  proof
    fix P
    assume "eventually P U"
    with proper have "frequently P U"
      by (rule eventually_frequently)
    then have "frequently P cofinite"
      using \<open>U \<le> cofinite\<close> by (simp add: le_filter_frequently)
    then show "infinite {x. P x}"
      by (simp add: frequently_cofinite)
  qed
  then show ?thesis ..
qed

end
