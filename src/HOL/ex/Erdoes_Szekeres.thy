(*   Title: HOL/ex/Erdoes_Szekeres.thy
     Author: Lukas Bulwahn <lukas.bulwahn-at-gmail.com>
*)

section \<open>The Erdoes-Szekeres Theorem\<close>

theory Erdoes_Szekeres
imports Main
begin

subsection \<open>Addition to @{theory Lattices_Big} Theory\<close>

lemma Max_gr:
  assumes "finite A"
  assumes "a \<in> A" "a > x"
  shows "x < Max A"
using assms Max_ge less_le_trans by blast

subsection \<open>Additions to @{theory Finite_Set} Theory\<close>

lemma obtain_subset_with_card_n:
  assumes "n \<le> card S"
  obtains T where "T \<subseteq> S" "card T = n"
proof -
  from assms obtain n' where "card S = n + n'" by (metis le_add_diff_inverse)
  from this that show ?thesis
  proof (induct n' arbitrary: S)
    case 0 from this show ?case by auto
  next
    case Suc from this show ?case by (simp add: card_Suc_eq) (metis subset_insertI2)
  qed
qed

lemma exists_set_with_max_card:
  assumes "finite S" "S \<noteq> {}"
  shows "\<exists>s \<in> S. card s = Max (card ` S)"
using assms
proof (induct S rule: finite.induct)
  case (insertI S' s')
  show ?case
  proof (cases "S' \<noteq> {}")
    case True
    from this insertI.hyps(2) obtain s where s: "s \<in> S'" "card s = Max (card ` S')" by auto
    from this(1) have that: "(if card s \<ge> card s' then s else s') \<in> insert s' S'" by auto
    have "card (if card s \<ge> card s' then s else s') = Max (card ` insert s' S')"
      using insertI(1) \<open>S' \<noteq> {}\<close> s by auto
    from this that show ?thesis by blast
  qed (auto)
qed (auto)

subsection \<open>Definition of Monotonicity over a Carrier Set\<close>

definition
  "mono_on f R S = (\<forall>i\<in>S. \<forall>j\<in>S. i \<le> j \<longrightarrow> R (f i) (f j))"

lemma mono_on_empty [simp]: "mono_on f R {}"
unfolding mono_on_def by auto

lemma mono_on_singleton [simp]: "reflp R \<Longrightarrow> mono_on f R {x}"
unfolding mono_on_def reflp_def by auto

lemma mono_on_subset: "T \<subseteq> S \<Longrightarrow> mono_on f R S \<Longrightarrow> mono_on f R T"
unfolding mono_on_def by (simp add: subset_iff)

lemma not_mono_on_subset: "T \<subseteq> S \<Longrightarrow> \<not> mono_on f R T \<Longrightarrow> \<not> mono_on f R S"
unfolding mono_on_def by blast

lemma [simp]:
  "reflp ((\<le>) :: 'a::order \<Rightarrow> _ \<Rightarrow> bool)"
  "reflp ((\<ge>) :: 'a::order \<Rightarrow> _ \<Rightarrow> bool)"
  "transp ((\<le>) :: 'a::order \<Rightarrow> _ \<Rightarrow> bool)"
  "transp ((\<ge>) :: 'a::order \<Rightarrow> _ \<Rightarrow> bool)"
unfolding reflp_def transp_def by auto

subsection \<open>The Erdoes-Szekeres Theorem following Seidenberg's (1959) argument\<close>

lemma Erdoes_Szekeres:
  fixes f :: "_ \<Rightarrow> 'a::linorder"
  shows "(\<exists>S. S \<subseteq> {0..m * n} \<and> card S = m + 1 \<and> mono_on f (\<le>) S) \<or>
         (\<exists>S. S \<subseteq> {0..m * n} \<and> card S = n + 1 \<and> mono_on f (\<ge>) S)"
proof (rule ccontr)
  let ?max_subseq = "\<lambda>R k. Max (card ` {S. S \<subseteq> {0..k} \<and> mono_on f R S \<and> k \<in> S})"
  define phi where "phi k = (?max_subseq (\<le>) k, ?max_subseq (\<ge>) k)" for k

  have one_member: "\<And>R k. reflp R \<Longrightarrow> {k} \<in> {S. S \<subseteq> {0..k} \<and> mono_on f R S \<and> k \<in> S}" by auto

  {
    fix R
    assume reflp: "reflp (R :: 'a::linorder \<Rightarrow> _)"
    from one_member[OF this] have non_empty: "\<And>k. {S. S \<subseteq> {0..k} \<and> mono_on f R S \<and> k \<in> S} \<noteq> {}" by force
    from one_member[OF reflp] have "\<And>k. card {k} \<in> card ` {S. S \<subseteq> {0..k} \<and> mono_on f R S \<and> k \<in> S}" by blast
    from this have lower_bound: "\<And>k. k \<le> m * n \<Longrightarrow> ?max_subseq R k \<ge> 1"
      by (auto intro!: Max_ge)

    fix b
    assume not_mono_at: "\<forall>S. S \<subseteq> {0..m * n} \<and> card S = b + 1 \<longrightarrow> \<not> mono_on f R S"

    {
      fix S
      assume "S \<subseteq> {0..m * n}" "card S \<ge> b + 1"
      moreover from \<open>card S \<ge> b + 1\<close> obtain T where "T \<subseteq> S \<and> card T = Suc b"
        using obtain_subset_with_card_n by (metis Suc_eq_plus1)
      ultimately have "\<not> mono_on f R S" using not_mono_at by (auto dest: not_mono_on_subset)
    }
    from this have "\<forall>S. S \<subseteq> {0..m * n} \<and> mono_on f R S \<longrightarrow> card S \<le> b"
      by (metis Suc_eq_plus1 Suc_leI not_le)
    from this have "\<And>k. k \<le> m * n \<Longrightarrow> \<forall>S. S \<subseteq> {0..k} \<and> mono_on f R S \<longrightarrow> card S \<le> b"
      using order_trans by force
    from this non_empty have upper_bound: "\<And>k. k \<le> m * n \<Longrightarrow> ?max_subseq R k \<le> b"
      by (auto intro: Max.boundedI)

    from upper_bound lower_bound have "\<And>k. k \<le> m * n \<Longrightarrow> 1 \<le> ?max_subseq R k \<and> ?max_subseq R k \<le> b"
      by auto
  } note bounds = this

  assume contraposition: "\<not> ?thesis"
  from contraposition bounds[of "(\<le>)" "m"] bounds[of "(\<ge>)" "n"]
    have "\<And>k. k \<le> m * n \<Longrightarrow> 1 \<le> ?max_subseq (\<le>) k \<and> ?max_subseq (\<le>) k \<le> m"
    and  "\<And>k. k \<le> m * n \<Longrightarrow> 1 \<le> ?max_subseq (\<ge>) k \<and> ?max_subseq (\<ge>) k \<le> n"
    using reflp_def by simp+
  from this have "\<forall>i \<in> {0..m * n}. phi i \<in> {1..m} \<times> {1..n}"
    unfolding phi_def by auto
  from this have subseteq: "phi ` {0..m * n} \<subseteq> {1..m} \<times> {1..n}" by blast
  have card_product: "card ({1..m} \<times> {1..n}) = m * n" by (simp add: card_cartesian_product)
  have "finite ({1..m} \<times> {1..n})" by blast
  from subseteq card_product this have card_le: "card (phi ` {0..m * n}) \<le> m * n" by (metis card_mono)

  {
    fix i j
    assume "i < (j :: nat)"
    {
      fix R
      assume R: "reflp (R :: 'a::linorder \<Rightarrow> _)" "transp R" "R (f i) (f j)"
      from one_member[OF \<open>reflp R\<close>, of "i"] have
        "\<exists>S \<in> {S. S \<subseteq> {0..i} \<and> mono_on f R S \<and> i \<in> S}. card S = ?max_subseq R i"
        by (intro exists_set_with_max_card) auto
      from this obtain S where S: "S \<subseteq> {0..i} \<and> mono_on f R S \<and> i \<in> S" "card S = ?max_subseq R i" by auto
      from S \<open>i < j\<close> finite_subset have "j \<notin> S" "finite S" "insert j S \<subseteq> {0..j}" by auto
      from S(1) R \<open>i < j\<close> this have "mono_on f R (insert j S)"
        unfolding mono_on_def reflp_def transp_def
        by (metis atLeastAtMost_iff insert_iff le_antisym subsetCE)
      from this have d: "insert j S \<in> {S. S \<subseteq> {0..j} \<and> mono_on f R S \<and> j \<in> S}"
        using \<open>insert j S \<subseteq> {0..j}\<close> by blast
      from this \<open>j \<notin> S\<close> S(1) have "card (insert j S) \<in>
        card ` {S. S \<subseteq> {0..j} \<and> mono_on f R S \<and> j \<in> S} \<and> card S < card (insert j S)"
        by (auto intro!: imageI) (auto simp add: \<open>finite S\<close>)
      from this S(2) have "?max_subseq R i < ?max_subseq R j" by (auto intro: Max_gr)
    } note max_subseq_increase = this
    have "?max_subseq (\<le>) i < ?max_subseq (\<le>) j \<or> ?max_subseq (\<ge>) i < ?max_subseq (\<ge>) j"
    proof (cases "f j \<ge> f i")
      case True
      from this max_subseq_increase[of "(\<le>)", simplified] show ?thesis by simp
    next
      case False
      from this max_subseq_increase[of "(\<ge>)", simplified] show ?thesis by simp
    qed
    from this have "phi i \<noteq> phi j" using phi_def by auto
  }
  from this have "inj phi" unfolding inj_on_def by (metis less_linear)
  from this have card_eq: "card (phi ` {0..m * n}) = m * n + 1" by (simp add: card_image inj_on_def)
  from card_le card_eq show False by simp
qed

end
