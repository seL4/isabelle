(*  Title:      HOL/Cardinals/Cardinal_Arithmetic.thy
    Author:     Dmitriy Traytel, TU Muenchen
    Copyright   2012

Cardinal arithmetic.
*)

header {* Cardinal Arithmetic  *}

theory Cardinal_Arithmetic
imports Cardinal_Arithmetic_FP Cardinal_Order_Relation
begin


subsection {* Binary sum *}

lemma csum_Cnotzero2:
  "Cnotzero r2 \<Longrightarrow> Cnotzero (r1 +c r2)"
unfolding csum_def
by (metis Cnotzero_imp_not_empty Field_card_of Plus_eq_empty_conv card_of_card_order_on czeroE)

lemma single_cone:
  "|{x}| =o cone"
proof -
  let ?f = "\<lambda>x. ()"
  have "bij_betw ?f {x} {()}" unfolding bij_betw_def by auto
  thus ?thesis unfolding cone_def using card_of_ordIso by blast
qed

lemma cone_Cnotzero: "Cnotzero cone"
by (simp add: cone_not_czero Card_order_cone)

lemma cone_ordLeq_ctwo: "cone \<le>o ctwo"
unfolding cone_def ctwo_def card_of_ordLeq[symmetric] by auto


subsection {* Product *}

lemma Times_cprod: "|A \<times> B| =o |A| *c |B|"
by (simp only: cprod_def Field_card_of card_of_refl)

lemma cprod_cong2: "p2 =o r2 \<Longrightarrow> q *c p2 =o q *c r2"
by (simp only: cprod_def ordIso_Times_cong2)

lemma ordLeq_cprod1: "\<lbrakk>Card_order p1; Cnotzero p2\<rbrakk> \<Longrightarrow> p1 \<le>o p1 *c p2"
unfolding cprod_def by (metis Card_order_Times1 czeroI)

lemma cprod_infinite: "Cinfinite r \<Longrightarrow> r *c r =o r"
using cprod_infinite1' Cinfinite_Cnotzero ordLeq_refl by blast


subsection {* Exponentiation *}

lemma cexp_czero: "r ^c czero =o cone"
unfolding cexp_def czero_def Field_card_of Func_empty by (rule single_cone)

lemma Pow_cexp_ctwo:
  "|Pow A| =o ctwo ^c |A|"
unfolding ctwo_def cexp_def Field_card_of by (rule card_of_Pow_Func)

lemma Cnotzero_cexp:
  assumes "Cnotzero q" "Card_order r"
  shows "Cnotzero (q ^c r)"
proof (cases "r =o czero")
  case False thus ?thesis
    apply -
    apply (rule Cnotzero_mono)
    apply (rule assms(1))
    apply (rule Card_order_cexp)
    apply (rule ordLeq_cexp1)
    apply (rule conjI)
    apply (rule notI)
    apply (erule notE)
    apply (rule ordIso_transitive)
    apply assumption
    apply (rule czero_ordIso)
    apply (rule assms(2))
    apply (rule conjunct2)
    apply (rule assms(1))
  done
next
  case True thus ?thesis
    apply -
    apply (rule Cnotzero_mono)
    apply (rule cone_Cnotzero)
    apply (rule Card_order_cexp)
    apply (rule ordIso_imp_ordLeq)
    apply (rule ordIso_symmetric)
    apply (rule ordIso_transitive)
    apply (rule cexp_cong2)
    apply assumption
    apply (rule conjunct2)
    apply (rule assms(1))
    apply (rule assms(2))
    apply (rule cexp_czero)
  done
qed

lemma Cinfinite_ctwo_cexp:
  "Cinfinite r \<Longrightarrow> Cinfinite (ctwo ^c r)"
unfolding ctwo_def cexp_def cinfinite_def Field_card_of
by (rule conjI, rule infinite_Func, auto)

lemma cone_ordLeq_iff_Field:
  assumes "cone \<le>o r"
  shows "Field r \<noteq> {}"
proof (rule ccontr)
  assume "\<not> Field r \<noteq> {}"
  hence "Field r = {}" by simp
  thus False using card_of_empty3
    card_of_mono2[OF assms] Cnotzero_imp_not_empty[OF cone_Cnotzero] by auto
qed

lemma cone_ordLeq_cexp: "cone \<le>o r1 \<Longrightarrow> cone \<le>o r1 ^c r2"
by (simp add: cexp_def cone_def Func_non_emp card_of_singl_ordLeq cone_ordLeq_iff_Field)

lemma Card_order_czero: "Card_order czero"
by (simp only: card_of_Card_order czero_def)

lemma cexp_mono2'':
  assumes 2: "p2 \<le>o r2"
  and n1: "Cnotzero q"
  and n2: "Card_order p2"
  shows "q ^c p2 \<le>o q ^c r2"
proof (cases "p2 =o (czero :: 'a rel)")
  case True
  hence "q ^c p2 =o q ^c (czero :: 'a rel)" using n1 n2 cexp_cong2 Card_order_czero by blast
  also have "q ^c (czero :: 'a rel) =o cone" using cexp_czero by blast
  also have "cone \<le>o q ^c r2" using cone_ordLeq_cexp cone_ordLeq_Cnotzero n1 by blast
  finally show ?thesis .
next
  case False thus ?thesis using assms cexp_mono2' czeroI by metis
qed

lemma csum_cexp: "\<lbrakk>Cinfinite r1; Cinfinite r2; Card_order q; ctwo \<le>o q\<rbrakk> \<Longrightarrow>
  q ^c r1 +c q ^c r2 \<le>o q ^c (r1 +c r2)"
apply (rule csum_cinfinite_bound)
apply (rule cexp_mono2)
apply (rule ordLeq_csum1)
apply (erule conjunct2)
apply assumption
apply (rule notE)
apply (rule cinfinite_not_czero[of r1])
apply (erule conjunct1)
apply assumption
apply (erule conjunct2)
apply (rule cexp_mono2)
apply (rule ordLeq_csum2)
apply (erule conjunct2)
apply assumption
apply (rule notE)
apply (rule cinfinite_not_czero[of r2])
apply (erule conjunct1)
apply assumption
apply (erule conjunct2)
apply (rule Card_order_cexp)
apply (rule Card_order_cexp)
apply (rule Cinfinite_cexp)
apply assumption
apply (rule Cinfinite_csum)
by (rule disjI1)

lemma csum_cexp': "\<lbrakk>Cinfinite r; Card_order q; ctwo \<le>o q\<rbrakk> \<Longrightarrow> q +c r \<le>o q ^c r"
apply (rule csum_cinfinite_bound)
    apply (metis Cinfinite_Cnotzero ordLeq_cexp1)
   apply (metis ordLeq_cexp2)
  apply blast+
by (metis Cinfinite_cexp)

lemma card_of_Sigma_ordLeq_Cinfinite:
  "\<lbrakk>Cinfinite r; |I| \<le>o r; \<forall>i \<in> I. |A i| \<le>o r\<rbrakk> \<Longrightarrow> |SIGMA i : I. A i| \<le>o r"
unfolding cinfinite_def by (blast intro: card_of_Sigma_ordLeq_infinite_Field)


subsection {* Powerset *}

lemma Card_order_cpow: "Card_order (cpow r)"
unfolding cpow_def by (rule card_of_Card_order)

lemma cardSuc_ordLeq_cpow: "Card_order r \<Longrightarrow> cardSuc r \<le>o cpow r"
unfolding cpow_def by (metis Card_order_Pow cardSuc_ordLess_ordLeq card_of_Card_order)

lemma cpow_cexp_ctwo: "cpow r =o ctwo ^c r"
unfolding cpow_def ctwo_def cexp_def Field_card_of by (rule card_of_Pow_Func)


subsection {* Lists *}

text {*
  The following collection of lemmas should be seen as an user interface to the HOL theory
  of cardinals. It is not expected to be complete in any sense, since its
  development was driven by demand arising from the development of the (co)datatype package.
*}

lemma clists_Cinfinite: "Cinfinite r \<Longrightarrow> clists r =o r"
unfolding cinfinite_def clists_def by (blast intro: Card_order_lists_infinite)

lemma Card_order_clists: "Card_order (clists r)"
unfolding clists_def by (rule card_of_Card_order)

lemma Cnotzero_clists: "Cnotzero (clists r)"
by (simp add: clists_def card_of_ordIso_czero_iff_empty lists_not_empty)

end
