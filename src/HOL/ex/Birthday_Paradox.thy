(*  Title:      HOL/ex/Birthday_Paradox.thy
    Author:     Lukas Bulwahn, TU Muenchen, 2007
*)

section \<open>A Formulation of the Birthday Paradox\<close>

theory Birthday_Paradox
  imports "HOL-Library.FuncSet"
begin

section \<open>Cardinality\<close>

lemma card_product_dependent:
  assumes "finite S"
    and "\<forall>x \<in> S. finite (T x)"
  shows "card {(x, y). x \<in> S \<and> y \<in> T x} = (\<Sum>x \<in> S. card (T x))"
  using card_SigmaI[OF assms, symmetric]
  by (auto intro!: arg_cong[where f=card] simp add: Sigma_def)

lemma card_extensional_funcset_inj_on:
  assumes "finite S" "finite T" "card S \<le> card T"
  shows "card {f \<in> extensional_funcset S T. inj_on f S} = fact (card T) div (fact (card T - card S))"
  using assms
proof (induct S arbitrary: T rule: finite_induct)
  case empty
  from this show ?case
    by (simp add: Collect_conv_if PiE_empty_domain)
next
  case (insert x S)
  have finite_delete: "finite {f : extensional_funcset S (T - {x}). inj_on f S}" for x
  proof -
    from \<open>finite T\<close> have "finite (T - {x})"
      by auto
    from \<open>finite S\<close> this have *: "finite (extensional_funcset S (T - {x}))"
      by (rule finite_PiE)
    have "{f : extensional_funcset S (T - {x}). inj_on f S} \<subseteq> (extensional_funcset S (T - {x}))"
      by auto
    with * show ?thesis
      by (auto intro: finite_subset)
  qed
  from insert have hyps: "\<forall>y \<in> T. card ({g. g \<in> extensional_funcset S (T - {y}) \<and> inj_on g S}) =
      fact (card T - 1) div fact ((card T - 1) - card S)"(is "\<forall> _ \<in> T. _ = ?k")
    by auto
  from extensional_funcset_extend_domain_inj_on_eq[OF \<open>x \<notin> S\<close>]
  have "card {f. f \<in> extensional_funcset (insert x S) T \<and> inj_on f (insert x S)} =
      card ((\<lambda>(y, g). g(x := y)) ` {(y, g). y \<in> T \<and> g \<in> extensional_funcset S (T - {y}) \<and> inj_on g S})"
    by metis
  also from extensional_funcset_extend_domain_inj_onI[OF \<open>x \<notin> S\<close>, of T]
  have "\<dots> = card {(y, g). y \<in> T \<and> g \<in> extensional_funcset S (T - {y}) \<and> inj_on g S}"
    by (simp add: card_image)
  also have "card {(y, g). y \<in> T \<and> g \<in> extensional_funcset S (T - {y}) \<and> inj_on g S} =
      card {(y, g). y \<in> T \<and> g \<in> {f \<in> extensional_funcset S (T - {y}). inj_on f S}}"
    by auto
  also from \<open>finite T\<close> finite_delete
  have "\<dots> = (\<Sum>y \<in> T. card {g. g \<in> extensional_funcset S (T - {y}) \<and>  inj_on g S})"
    by (subst card_product_dependent) auto
  also from hyps have "\<dots> = (card T) * ?k"
    by auto
  also have "\<dots> = card T * fact (card T - 1) div fact (card T - card (insert x S))"
    using insert unfolding div_mult1_eq[of "card T" "fact (card T - 1)"]
    by (simp add: fact_mod)
  also have "\<dots> = fact (card T) div fact (card T - card (insert x S))"
    using insert by (simp add: fact_reduce[of "card T"])
  finally show ?case .
qed

lemma card_extensional_funcset_not_inj_on:
  assumes "finite S" "finite T" "card S \<le> card T"
  shows "card {f \<in> extensional_funcset S T. \<not> inj_on f S} =
    (card T) ^ (card S) - (fact (card T)) div (fact (card T - card S))"
proof -
  have subset: "{f \<in> extensional_funcset S T. inj_on f S} \<subseteq> extensional_funcset S T"
    by auto
  from finite_subset[OF subset] assms
  have finite: "finite {f : extensional_funcset S T. inj_on f S}"
    by (auto intro!: finite_PiE)
  have "{f \<in> extensional_funcset S T. \<not> inj_on f S} =
    extensional_funcset S T - {f \<in> extensional_funcset S T. inj_on f S}" by auto
  from assms this finite subset show ?thesis
    by (simp add: card_Diff_subset card_PiE card_extensional_funcset_inj_on prod_constant)
qed

lemma prod_upto_nat_unfold:
  "prod f {m..(n::nat)} = (if n < m then 1 else (if n = 0 then f 0 else f n * prod f {m..(n - 1)}))"
  by auto (auto simp add: gr0_conv_Suc atLeastAtMostSuc_conv)


section \<open>Birthday paradox\<close>

lemma birthday_paradox:
  assumes "card S = 23" "card T = 365"
  shows "2 * card {f \<in> extensional_funcset S T. \<not> inj_on f S} \<ge> card (extensional_funcset S T)"
proof -
  from \<open>card S = 23\<close> \<open>card T = 365\<close> have "finite S" "finite T" "card S \<le> card T"
    by (auto intro: card_ge_0_finite)
  from assms show ?thesis
    using card_PiE[OF \<open>finite S\<close>, of "\<lambda>i. T"] \<open>finite S\<close>
      card_extensional_funcset_not_inj_on[OF \<open>finite S\<close> \<open>finite T\<close> \<open>card S \<le> card T\<close>]
    by (simp add: fact_div_fact prod_upto_nat_unfold prod_constant)
qed

end
