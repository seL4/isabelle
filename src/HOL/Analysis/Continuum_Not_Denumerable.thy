(*  Title:      HOL/Analysis/Continuum_Not_Denumerable.thy
    Author:     Benjamin Porter, Monash University, NICTA, 2005
    Author:     Johannes Hölzl, TU München
*)

section \<open>Non-Denumerability of the Continuum\<close>

theory Continuum_Not_Denumerable
imports
  Complex_Main 
  "HOL-Library.Countable_Set"
begin

subsection\<^marker>\<open>tag unimportant\<close> \<open>Abstract\<close>

text \<open>
  The following document presents a proof that the Continuum is uncountable.
  It is formalised in the Isabelle/Isar theorem proving system.

  \<^bold>\<open>Theorem:\<close> The Continuum \<open>\<real>\<close> is not denumerable. In other words, there does
  not exist a function \<open>f: \<nat> \<Rightarrow> \<real>\<close> such that \<open>f\<close> is surjective.

  \<^bold>\<open>Outline:\<close> An elegant informal proof of this result uses Cantor's
  Diagonalisation argument. The proof presented here is not this one.

  First we formalise some properties of closed intervals, then we prove the
  Nested Interval Property. This property relies on the completeness of the
  Real numbers and is the foundation for our argument. Informally it states
  that an intersection of countable closed intervals (where each successive
  interval is a subset of the last) is non-empty. We then assume a surjective
  function \<open>f: \<nat> \<Rightarrow> \<real>\<close> exists and find a real \<open>x\<close> such that \<open>x\<close> is not in the
  range of \<open>f\<close> by generating a sequence of closed intervals then using the
  Nested Interval Property.
\<close>
text\<^marker>\<open>tag important\<close> \<open>%whitespace\<close>
theorem real_non_denum: "\<nexists>f :: nat \<Rightarrow> real. surj f"
proof
  assume "\<exists>f::nat \<Rightarrow> real. surj f"
  then obtain f :: "nat \<Rightarrow> real" where "surj f" ..

  txt \<open>First we construct a sequence of nested intervals, ignoring \<^term>\<open>range f\<close>.\<close>

  have "a < b \<Longrightarrow> \<exists>ka kb. ka < kb \<and> {ka..kb} \<subseteq> {a..b} \<and> c \<notin> {ka..kb}" for a b c :: real
    by (auto simp add: not_le cong: conj_cong)
      (metis dense le_less_linear less_linear less_trans order_refl)
  then obtain i j where ij:
    "a < b \<Longrightarrow> i a b c < j a b c"
      "a < b \<Longrightarrow> {i a b c .. j a b c} \<subseteq> {a .. b}"
      "a < b \<Longrightarrow> c \<notin> {i a b c .. j a b c}"
    for a b c :: real
    by metis

  define ivl where "ivl =
    rec_nat (f 0 + 1, f 0 + 2) (\<lambda>n x. (i (fst x) (snd x) (f n), j (fst x) (snd x) (f n)))"
  define I where "I n = {fst (ivl n) .. snd (ivl n)}" for n

  have ivl [simp]:
    "ivl 0 = (f 0 + 1, f 0 + 2)"
    "\<And>n. ivl (Suc n) = (i (fst (ivl n)) (snd (ivl n)) (f n), j (fst (ivl n)) (snd (ivl n)) (f n))"
    unfolding ivl_def by simp_all

  txt \<open>This is a decreasing sequence of non-empty intervals.\<close>

  have less: "fst (ivl n) < snd (ivl n)" for n
    by (induct n) (auto intro!: ij)

  have "decseq I"
    unfolding I_def decseq_Suc_iff ivl fst_conv snd_conv
    by (intro ij allI less)

  txt \<open>Now we apply the finite intersection property of compact sets.\<close>

  have "I 0 \<inter> (\<Inter>i. I i) \<noteq> {}"
  proof (rule compact_imp_fip_image)
    fix S :: "nat set"
    assume fin: "finite S"
    have "{} \<subset> I (Max (insert 0 S))"
      unfolding I_def using less[of "Max (insert 0 S)"] by auto
    also have "I (Max (insert 0 S)) \<subseteq> (\<Inter>i\<in>insert 0 S. I i)"
      using fin decseqD[OF \<open>decseq I\<close>, of _ "Max (insert 0 S)"]
      by (auto simp: Max_ge_iff)
    also have "(\<Inter>i\<in>insert 0 S. I i) = I 0 \<inter> (\<Inter>i\<in>S. I i)"
      by auto
    finally show "I 0 \<inter> (\<Inter>i\<in>S. I i) \<noteq> {}"
      by auto
  qed (auto simp: I_def)
  then obtain x where "x \<in> I n" for n
    by blast
  moreover from \<open>surj f\<close> obtain j where "x = f j"
    by blast
  ultimately have "f j \<in> I (Suc j)"
    by blast
  with ij(3)[OF less] show False
    unfolding I_def ivl fst_conv snd_conv by auto
qed

lemma uncountable_UNIV_real: "uncountable (UNIV :: real set)"
  using real_non_denum unfolding uncountable_def by auto

corollary complex_non_denum: "\<nexists>f :: nat \<Rightarrow> complex. surj f"
  by (metis (full_types) Re_complex_of_real comp_surj real_non_denum surj_def)

lemma uncountable_UNIV_complex: "uncountable (UNIV :: complex set)"
  using complex_non_denum unfolding uncountable_def by auto

lemma bij_betw_open_intervals:
  fixes a b c d :: real
  assumes "a < b" "c < d"
  shows "\<exists>f. bij_betw f {a<..<b} {c<..<d}"
proof -
  define f where "f a b c d x = (d - c)/(b - a) * (x - a) + c" for a b c d x :: real
  have "f a b c d x < d" "c < f a b c d x"
    if *: "a < b" "c < d" "a < x" "x < b"
    for a b c d x :: real
  proof -
    note that
    moreover from * have "(d - c) * (x - a) < (d - c) * (b - a)"
      by (intro mult_strict_left_mono) simp_all
    moreover from * have "0 < (d - c) * (x - a) / (b - a)"
      by simp
    ultimately show "f a b c d x < d" "c < f a b c d x"
      by (simp_all add: f_def field_simps)
  qed
  with assms have "bij_betw (f a b c d) {a<..<b} {c<..<d}"
    by (intro bij_betw_byWitness[where f'="f c d a b"]) (auto simp: f_def)
  then show ?thesis by auto
qed

lemma bij_betw_tan: "bij_betw tan {-pi/2<..<pi/2} UNIV"
  using arctan_ubound by (intro bij_betw_byWitness[where f'=arctan]) (auto simp: arctan arctan_tan)

lemma uncountable_open_interval: "uncountable {a<..<b} \<longleftrightarrow> a < b" for a b :: real
proof
  show "a < b" if "uncountable {a<..<b}"
    using uncountable_def that by force
  show "uncountable {a<..<b}" if "a < b"
  proof -
    obtain f where "bij_betw f {a <..< b} {-pi/2<..<pi/2}"
      using bij_betw_open_intervals[OF \<open>a < b\<close>, of "-pi/2" "pi/2"] by auto
    then show ?thesis
      by (metis bij_betw_tan uncountable_bij_betw uncountable_UNIV_real)
  qed
qed

lemma uncountable_half_open_interval_1: "uncountable {a..<b} \<longleftrightarrow> a < b" for a b :: real
  apply auto
  using atLeastLessThan_empty_iff
  apply fastforce
  using uncountable_open_interval [of a b]
  apply (metis countable_Un_iff ivl_disj_un_singleton(3))
  done

lemma uncountable_half_open_interval_2: "uncountable {a<..b} \<longleftrightarrow> a < b" for a b :: real
  apply auto
  using atLeastLessThan_empty_iff
  apply fastforce
  using uncountable_open_interval [of a b]
  apply (metis countable_Un_iff ivl_disj_un_singleton(4))
  done

lemma real_interval_avoid_countable_set:
  fixes a b :: real and A :: "real set"
  assumes "a < b" and "countable A"
  shows "\<exists>x\<in>{a<..<b}. x \<notin> A"
proof -
  from \<open>countable A\<close> have *: "countable (A \<inter> {a<..<b})"
    by auto
  with \<open>a < b\<close> have "\<not> countable {a<..<b}"
    by (simp add: uncountable_open_interval)
  with * have "A \<inter> {a<..<b} \<noteq> {a<..<b}"
    by auto
  then have "A \<inter> {a<..<b} \<subset> {a<..<b}"
    by (intro psubsetI) auto
  then have "\<exists>x. x \<in> {a<..<b} - A \<inter> {a<..<b}"
    by (rule psubset_imp_ex_mem)
  then show ?thesis
    by auto
qed

lemma uncountable_closed_interval: "uncountable {a..b} \<longleftrightarrow> a < b" for a b :: real
  using infinite_Icc_iff by (fastforce dest: countable_finite real_interval_avoid_countable_set)

lemma open_minus_countable:
  fixes S A :: "real set"
  assumes "countable A" "S \<noteq> {}" "open S"
  shows "\<exists>x\<in>S. x \<notin> A"
proof -
  obtain x where "x \<in> S"
    using \<open>S \<noteq> {}\<close> by auto
  then obtain e where "0 < e" "{y. dist y x < e} \<subseteq> S"
    using \<open>open S\<close> by (auto simp: open_dist subset_eq)
  moreover have "{y. dist y x < e} = {x - e <..< x + e}"
    by (auto simp: dist_real_def)
  ultimately have "uncountable (S - A)"
    using uncountable_open_interval[of "x - e" "x + e"] \<open>countable A\<close>
    by (intro uncountable_minus_countable) (auto dest: countable_subset)
  then show ?thesis
    unfolding uncountable_def by auto
qed

end
