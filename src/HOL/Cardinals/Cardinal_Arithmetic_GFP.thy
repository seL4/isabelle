(*  Title:      HOL/Cardinals/Cardinal_Arithmetic_GFP.thy
    Author:     Dmitriy Traytel, TU Muenchen
    Copyright   2012

Cardinal arithmetic (GFP).
*)

header {* Cardinal Arithmetic (GFP) *}

theory Cardinal_Arithmetic_GFP
imports Cardinal_Arithmetic_LFP
begin


subsection {* Binary sum *}

lemma Cinfinite_csum:
  "Cinfinite r1 \<or> Cinfinite r2 \<Longrightarrow> Cinfinite (r1 +c r2)"
unfolding cinfinite_def csum_def by (metis Field_card_of card_of_Card_order finite_Plus_iff)

lemma Cinfinite_csum_strong:
  "\<lbrakk>Cinfinite r1; Cinfinite r2\<rbrakk> \<Longrightarrow> Cinfinite (r1 +c r2)"
by (metis Cinfinite_csum)


subsection {* Exponentiation *}

lemma card_order_cexp:
  assumes "card_order r1" "card_order r2"
  shows "card_order (r1 ^c r2)"
proof -
  have "Field r1 = UNIV" "Field r2 = UNIV" using assms card_order_on_Card_order by auto
  thus ?thesis unfolding cexp_def Func_def by (simp add: card_of_card_order_on)
qed

lemma Cinfinite_ordLess_cexp:
  assumes r: "Cinfinite r"
  shows "r <o r ^c r"
proof -
  have "r <o ctwo ^c r" using r by (simp only: ordLess_ctwo_cexp)
  also have "ctwo ^c r \<le>o r ^c r"
    by (rule cexp_mono1[OF ctwo_ordLeq_Cinfinite]) (auto simp: r ctwo_not_czero Card_order_ctwo)
  finally show ?thesis .
qed

lemma infinite_ordLeq_cexp:
  assumes "Cinfinite r"
  shows "r \<le>o r ^c r"
by (rule ordLess_imp_ordLeq[OF Cinfinite_ordLess_cexp[OF assms]])

end
