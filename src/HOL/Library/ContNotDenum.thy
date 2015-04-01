(*  Title:      HOL/Library/ContNotDenum.thy
    Author:     Benjamin Porter, Monash University, NICTA, 2005
    Author:     Johannes Hölzl, TU München
*)

section {* Non-denumerability of the Continuum. *}

theory ContNotDenum
imports Complex_Main Countable_Set
begin

subsection {* Abstract *}

text {* The following document presents a proof that the Continuum is
uncountable. It is formalised in the Isabelle/Isar theorem proving
system.

{\em Theorem:} The Continuum @{text "\<real>"} is not denumerable. In other
words, there does not exist a function @{text "f: \<nat> \<Rightarrow> \<real>"} such that f is
surjective.

{\em Outline:} An elegant informal proof of this result uses Cantor's
Diagonalisation argument. The proof presented here is not this
one. First we formalise some properties of closed intervals, then we
prove the Nested Interval Property. This property relies on the
completeness of the Real numbers and is the foundation for our
argument. Informally it states that an intersection of countable
closed intervals (where each successive interval is a subset of the
last) is non-empty. We then assume a surjective function @{text
"f: \<nat> \<Rightarrow> \<real>"} exists and find a real x such that x is not in the range of f
by generating a sequence of closed intervals then using the NIP. *}

theorem real_non_denum: "\<not> (\<exists>f :: nat \<Rightarrow> real. surj f)"
proof
  assume "\<exists>f::nat \<Rightarrow> real. surj f"
  then obtain f :: "nat \<Rightarrow> real" where "surj f" ..

  txt {* First we construct a sequence of nested intervals, ignoring @{term "range f"}. *}

  have "\<forall>a b c::real. a < b \<longrightarrow> (\<exists>ka kb. ka < kb \<and> {ka..kb} \<subseteq> {a..b} \<and> c \<notin> {ka..kb})"
    using assms
    by (auto simp add: not_le cong: conj_cong)
       (metis dense le_less_linear less_linear less_trans order_refl)
  then obtain i j where ij:
    "\<And>a b c::real. a < b \<Longrightarrow> i a b c < j a b c"
    "\<And>a b c. a < b \<Longrightarrow> {i a b c .. j a b c} \<subseteq> {a .. b}"
    "\<And>a b c. a < b \<Longrightarrow> c \<notin> {i a b c .. j a b c}"
    by metis

  def ivl \<equiv> "rec_nat (f 0 + 1, f 0 + 2) (\<lambda>n x. (i (fst x) (snd x) (f n), j (fst x) (snd x) (f n)))"
  def I \<equiv> "\<lambda>n. {fst (ivl n) .. snd (ivl n)}"

  have ivl[simp]:
    "ivl 0 = (f 0 + 1, f 0 + 2)"
    "\<And>n. ivl (Suc n) = (i (fst (ivl n)) (snd (ivl n)) (f n), j (fst (ivl n)) (snd (ivl n)) (f n))"
    unfolding ivl_def by simp_all

  txt {* This is a decreasing sequence of non-empty intervals. *}

  { fix n have "fst (ivl n) < snd (ivl n)"
      by (induct n) (auto intro!: ij) }
  note less = this

  have "decseq I"
    unfolding I_def decseq_Suc_iff ivl fst_conv snd_conv by (intro ij allI less)

  txt {* Now we apply the finite intersection property of compact sets. *}

  have "I 0 \<inter> (\<Inter>i. I i) \<noteq> {}"
  proof (rule compact_imp_fip_image)
    fix S :: "nat set" assume fin: "finite S"
    have "{} \<subset> I (Max (insert 0 S))"
      unfolding I_def using less[of "Max (insert 0 S)"] by auto
    also have "I (Max (insert 0 S)) \<subseteq> (\<Inter>i\<in>insert 0 S. I i)"
      using fin decseqD[OF `decseq I`, of _ "Max (insert 0 S)"] by (auto simp: Max_ge_iff)
    also have "(\<Inter>i\<in>insert 0 S. I i) = I 0 \<inter> (\<Inter>i\<in>S. I i)"
      by auto
    finally show "I 0 \<inter> (\<Inter>i\<in>S. I i) \<noteq> {}"
      by auto
  qed (auto simp: I_def)
  then obtain x where "\<And>n. x \<in> I n"
    by blast
  moreover from `surj f` obtain j where "x = f j"
    by blast
  ultimately have "f j \<in> I (Suc j)"
    by blast
  with ij(3)[OF less] show False
    unfolding I_def ivl fst_conv snd_conv by auto
qed

lemma uncountable_UNIV_real: "uncountable (UNIV::real set)"
  using real_non_denum unfolding uncountable_def by auto

lemma bij_betw_open_intervals:
  fixes a b c d :: real
  assumes "a < b" "c < d"
  shows "\<exists>f. bij_betw f {a<..<b} {c<..<d}"
proof -
  def f \<equiv> "\<lambda>a b c d x::real. (d - c)/(b - a) * (x - a) + c"
  { fix a b c d x :: real assume *: "a < b" "c < d" "a < x" "x < b"
    moreover from * have "(d - c) * (x - a) < (d - c) * (b - a)"
      by (intro mult_strict_left_mono) simp_all
    moreover from * have "0 < (d - c) * (x - a) / (b - a)"
      by simp
    ultimately have "f a b c d x < d" "c < f a b c d x"
      by (simp_all add: f_def field_simps) }
  with assms have "bij_betw (f a b c d) {a<..<b} {c<..<d}"
    by (intro bij_betw_byWitness[where f'="f c d a b"]) (auto simp: f_def)
  thus ?thesis by auto
qed

lemma bij_betw_tan: "bij_betw tan {-pi/2<..<pi/2} UNIV"
  using arctan_ubound by (intro bij_betw_byWitness[where f'=arctan]) (auto simp: arctan arctan_tan)

lemma uncountable_open_interval:
  fixes a b :: real assumes ab: "a < b"
  shows "uncountable {a<..<b}"
proof -
  obtain f where "bij_betw f {a <..< b} {-pi/2<..<pi/2}"
    using bij_betw_open_intervals[OF `a < b`, of "-pi/2" "pi/2"] by auto
  then show ?thesis
    by (metis bij_betw_tan uncountable_bij_betw uncountable_UNIV_real)
qed

end

