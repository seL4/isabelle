(*  Title:      HOL/Cardinals/Cardinal_Arithmetic.thy
    Author:     Dmitriy Traytel, TU Muenchen
    Copyright   2012

Cardinal arithmetic.
*)

section {* Cardinal Arithmetic *}

theory Cardinal_Arithmetic
imports BNF_Cardinal_Arithmetic Cardinal_Order_Relation
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

lemma csum_czero1: "Card_order r \<Longrightarrow> r +c czero =o r"
  unfolding czero_def csum_def Field_card_of
  by (rule ordIso_transitive[OF ordIso_symmetric[OF card_of_Plus_empty1] card_of_Field_ordIso])

lemma csum_czero2: "Card_order r \<Longrightarrow> czero +c r =o r"
  unfolding czero_def csum_def Field_card_of
  by (rule ordIso_transitive[OF ordIso_symmetric[OF card_of_Plus_empty2] card_of_Field_ordIso])


subsection {* Product *}

lemma Times_cprod: "|A \<times> B| =o |A| *c |B|"
by (simp only: cprod_def Field_card_of card_of_refl)

lemma card_of_Times_singleton:
fixes A :: "'a set"
shows "|A \<times> {x}| =o |A|"
proof -
  def f \<equiv> "\<lambda>(a::'a,b::'b). (a)"
  have "A \<subseteq> f ` (A <*> {x})" unfolding f_def by (auto simp: image_iff)
  hence "bij_betw f (A <*> {x}) A"  unfolding bij_betw_def inj_on_def f_def by fastforce
  thus ?thesis using card_of_ordIso by blast
qed

lemma cprod_assoc: "(r *c s) *c t =o r *c s *c t"
  unfolding cprod_def Field_card_of by (rule card_of_Times_assoc)

lemma cprod_czero: "r *c czero =o czero"
  unfolding cprod_def czero_def Field_card_of by (simp add: card_of_empty_ordIso)

lemma cprod_cone: "Card_order r \<Longrightarrow> r *c cone =o r"
  unfolding cprod_def cone_def Field_card_of
  by (drule card_of_Field_ordIso) (erule ordIso_transitive[OF card_of_Times_singleton])


lemma ordLeq_cprod1: "\<lbrakk>Card_order p1; Cnotzero p2\<rbrakk> \<Longrightarrow> p1 \<le>o p1 *c p2"
unfolding cprod_def by (metis Card_order_Times1 czeroI)


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
by (simp add: cexp_def cone_def Func_non_emp cone_ordLeq_iff_Field)

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

lemma card_order_cexp:
  assumes "card_order r1" "card_order r2"
  shows "card_order (r1 ^c r2)"
proof -
  have "Field r1 = UNIV" "Field r2 = UNIV" using assms card_order_on_Card_order by auto
  thus ?thesis unfolding cexp_def Func_def by simp
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

lemma czero_cexp: "Cnotzero r \<Longrightarrow> czero ^c r =o czero"
  by (drule Cnotzero_imp_not_empty) (simp add: cexp_def czero_def card_of_empty_ordIso)

lemma Func_singleton:
fixes x :: 'b and A :: "'a set"
shows "|Func A {x}| =o |{x}|"
proof (rule ordIso_symmetric)
  def f \<equiv> "\<lambda>y a. if y = x \<and> a \<in> A then x else undefined"
  have "Func A {x} \<subseteq> f ` {x}" unfolding f_def Func_def by (force simp: fun_eq_iff)
  hence "bij_betw f {x} (Func A {x})" unfolding bij_betw_def inj_on_def f_def Func_def
    by (auto split: split_if_asm)
  thus "|{x}| =o |Func A {x}|" using card_of_ordIso by blast
qed

lemma cone_cexp: "cone ^c r =o cone"
  unfolding cexp_def cone_def Field_card_of by (rule Func_singleton)

lemma card_of_Func_squared:
  fixes A :: "'a set"
  shows "|Func (UNIV :: bool set) A| =o |A \<times> A|"
proof (rule ordIso_symmetric)
  def f \<equiv> "\<lambda>(x::'a,y) b. if A = {} then undefined else if b then x else y"
  have "Func (UNIV :: bool set) A \<subseteq> f ` (A \<times> A)" unfolding f_def Func_def
    by (auto simp: image_iff fun_eq_iff split: option.splits split_if_asm) blast
  hence "bij_betw f (A \<times> A) (Func (UNIV :: bool set) A)"
    unfolding bij_betw_def inj_on_def f_def Func_def by (auto simp: fun_eq_iff)
  thus "|A \<times> A| =o |Func (UNIV :: bool set) A|" using card_of_ordIso by blast
qed

lemma cexp_ctwo: "r ^c ctwo =o r *c r"
  unfolding cexp_def ctwo_def cprod_def Field_card_of by (rule card_of_Func_squared)

lemma card_of_Func_Plus:
  fixes A :: "'a set" and B :: "'b set" and C :: "'c set"
  shows "|Func (A <+> B) C| =o |Func A C \<times> Func B C|"
proof (rule ordIso_symmetric)
  def f \<equiv> "\<lambda>(g :: 'a => 'c, h::'b \<Rightarrow> 'c) ab. case ab of Inl a \<Rightarrow> g a | Inr b \<Rightarrow> h b"
  def f' \<equiv> "\<lambda>(f :: ('a + 'b) \<Rightarrow> 'c). (\<lambda>a. f (Inl a), \<lambda>b. f (Inr b))"
  have "f ` (Func A C \<times> Func B C) \<subseteq> Func (A <+> B) C"
    unfolding Func_def f_def by (force split: sum.splits)
  moreover have "f' ` Func (A <+> B) C \<subseteq> Func A C \<times> Func B C" unfolding Func_def f'_def by force
  moreover have "\<forall>a \<in> Func A C \<times> Func B C. f' (f a) = a" unfolding f'_def f_def Func_def by auto
  moreover have "\<forall>a' \<in> Func (A <+> B) C. f (f' a') = a'" unfolding f'_def f_def Func_def
    by (auto split: sum.splits)
  ultimately have "bij_betw f (Func A C \<times> Func B C) (Func (A <+> B) C)"
    by (intro bij_betw_byWitness[of _ f' f])
  thus "|Func A C \<times> Func B C| =o |Func (A <+> B) C|" using card_of_ordIso by blast
qed

lemma cexp_csum: "r ^c (s +c t) =o r ^c s *c r ^c t"
  unfolding cexp_def cprod_def csum_def Field_card_of by (rule card_of_Func_Plus)


subsection {* Powerset *}

definition cpow where "cpow r = |Pow (Field r)|"

lemma card_order_cpow: "card_order r \<Longrightarrow> card_order (cpow r)"
by (simp only: cpow_def Field_card_order Pow_UNIV card_of_card_order_on)

lemma cpow_greater_eq: "Card_order r \<Longrightarrow> r \<le>o cpow r"
by (rule ordLess_imp_ordLeq) (simp only: cpow_def Card_order_Pow)

lemma Cinfinite_cpow: "Cinfinite r \<Longrightarrow> Cinfinite (cpow r)"
unfolding cpow_def cinfinite_def by (metis Field_card_of card_of_Card_order infinite_Pow)

lemma Card_order_cpow: "Card_order (cpow r)"
unfolding cpow_def by (rule card_of_Card_order)

lemma cardSuc_ordLeq_cpow: "Card_order r \<Longrightarrow> cardSuc r \<le>o cpow r"
unfolding cpow_def by (metis Card_order_Pow cardSuc_ordLess_ordLeq card_of_Card_order)

lemma cpow_cexp_ctwo: "cpow r =o ctwo ^c r"
unfolding cpow_def ctwo_def cexp_def Field_card_of by (rule card_of_Pow_Func)

subsection {* Inverse image *}

lemma vimage_ordLeq:
assumes "|A| \<le>o k" and "\<forall> a \<in> A. |vimage f {a}| \<le>o k" and "Cinfinite k"
shows "|vimage f A| \<le>o k"
proof-
  have "vimage f A = (\<Union> a \<in> A. vimage f {a})" by auto
  also have "|\<Union> a \<in> A. vimage f {a}| \<le>o k"
  using UNION_Cinfinite_bound[OF assms] .
  finally show ?thesis .
qed

subsection {* Maximum *}

definition cmax where
  "cmax r s =
    (if cinfinite r \<or> cinfinite s then czero +c r +c s
     else natLeq_on (max (card (Field r)) (card (Field s))) +c czero)"

lemma cmax_com: "cmax r s =o cmax s r"
  unfolding cmax_def
  by (auto simp: max.commute intro: csum_cong2[OF csum_com] csum_cong2[OF czero_ordIso])

lemma cmax1:
  assumes "Card_order r" "Card_order s" "s \<le>o r"
  shows "cmax r s =o r"
unfolding cmax_def proof (split if_splits, intro conjI impI)
  assume "cinfinite r \<or> cinfinite s"
  hence Cinf: "Cinfinite r" using assms(1,3) by (metis cinfinite_mono)
  have "czero +c r +c s =o r +c s" by (rule csum_czero2[OF Card_order_csum])
  also have "r +c s =o r" by (rule csum_absorb1[OF Cinf assms(3)])
  finally show "czero +c r +c s =o r" .
next
  assume "\<not> (cinfinite r \<or> cinfinite s)"
  hence fin: "finite (Field r)" and "finite (Field s)" unfolding cinfinite_def by simp_all
  moreover
  { from assms(2) have "|Field s| =o s" by (rule card_of_Field_ordIso)
    also from assms(3) have "s \<le>o r" .
    also from assms(1) have "r =o |Field r|" by (rule ordIso_symmetric[OF card_of_Field_ordIso])
    finally have "|Field s| \<le>o |Field r|" .
  }
  ultimately have "card (Field s) \<le> card (Field r)" by (subst sym[OF finite_card_of_iff_card2])
  hence "max (card (Field r)) (card (Field s)) = card (Field r)" by (rule max_absorb1)
  hence "natLeq_on (max (card (Field r)) (card (Field s))) +c czero =
    natLeq_on (card (Field r)) +c czero" by simp
  also have "\<dots> =o natLeq_on (card (Field r))" by (rule csum_czero1[OF natLeq_on_Card_order])
  also have "natLeq_on (card (Field r)) =o |Field r|"
    by (rule ordIso_symmetric[OF finite_imp_card_of_natLeq_on[OF fin]])
  also from assms(1) have "|Field r| =o r" by (rule card_of_Field_ordIso)
  finally show "natLeq_on (max (card (Field r)) (card (Field s))) +c czero =o r" .
qed

lemma cmax2:
  assumes "Card_order r" "Card_order s" "r \<le>o s"
  shows "cmax r s =o s"
  by (metis assms cmax1 cmax_com ordIso_transitive)

lemma csum_absorb2: "Cinfinite r2 \<Longrightarrow> r1 \<le>o r2 \<Longrightarrow> r1 +c r2 =o r2"
  by (metis csum_absorb2')

lemma cprod_infinite2': "\<lbrakk>Cnotzero r1; Cinfinite r2; r1 \<le>o r2\<rbrakk> \<Longrightarrow> r1 *c r2 =o r2"
  unfolding ordIso_iff_ordLeq
  by (intro conjI cprod_cinfinite_bound ordLeq_cprod2 ordLeq_refl)
    (auto dest!: ordIso_imp_ordLeq not_ordLeq_ordLess simp: czero_def Card_order_empty)

context
  fixes r s
  assumes r: "Cinfinite r"
  and     s: "Cinfinite s"
begin

lemma cmax_csum: "cmax r s =o r +c s"
proof (cases "r \<le>o s")
  case True
  hence "cmax r s =o s" by (metis cmax2 r s)
  also have "s =o r +c s" by (metis True csum_absorb2 ordIso_symmetric s)
  finally show ?thesis .
next
  case False
  hence "s \<le>o r" by (metis ordLeq_total r s card_order_on_def)
  hence "cmax r s =o r" by (metis cmax1 r s)
  also have "r =o r +c s" by (metis `s \<le>o r` csum_absorb1 ordIso_symmetric r)
  finally show ?thesis .
qed

lemma cmax_cprod: "cmax r s =o r *c s"
proof (cases "r \<le>o s")
  case True
  hence "cmax r s =o s" by (metis cmax2 r s)
  also have "s =o r *c s" by (metis Cinfinite_Cnotzero True cprod_infinite2' ordIso_symmetric r s)
  finally show ?thesis .
next
  case False
  hence "s \<le>o r" by (metis ordLeq_total r s card_order_on_def)
  hence "cmax r s =o r" by (metis cmax1 r s)
  also have "r =o r *c s" by (metis Cinfinite_Cnotzero `s \<le>o r` cprod_infinite1' ordIso_symmetric r s)
  finally show ?thesis .
qed

end

lemma Card_order_cmax:
assumes r: "Card_order r" and s: "Card_order s"
shows "Card_order (cmax r s)"
unfolding cmax_def by (auto simp: Card_order_csum)

lemma ordLeq_cmax:
assumes r: "Card_order r" and s: "Card_order s"
shows "r \<le>o cmax r s \<and> s \<le>o cmax r s"
proof-
  {assume "r \<le>o s"
   hence ?thesis by (metis cmax2 ordIso_iff_ordLeq ordLeq_transitive r s)
  }
  moreover
  {assume "s \<le>o r"
   hence ?thesis using cmax_com by (metis cmax2 ordIso_iff_ordLeq ordLeq_transitive r s)
  }
  ultimately show ?thesis using r s ordLeq_total unfolding card_order_on_def by auto
qed

lemmas ordLeq_cmax1 = ordLeq_cmax[THEN conjunct1] and
       ordLeq_cmax2 = ordLeq_cmax[THEN conjunct2]

lemma finite_cmax:
assumes r: "Card_order r" and s: "Card_order s"
shows "finite (Field (cmax r s)) \<longleftrightarrow> finite (Field r) \<and> finite (Field s)"
proof-
  {assume "r \<le>o s"
   hence ?thesis by (metis cmax2 ordIso_finite_Field ordLeq_finite_Field r s)
  }
  moreover
  {assume "s \<le>o r"
   hence ?thesis by (metis cmax1 ordIso_finite_Field ordLeq_finite_Field r s)
  }
  ultimately show ?thesis using r s ordLeq_total unfolding card_order_on_def by auto
qed

end
