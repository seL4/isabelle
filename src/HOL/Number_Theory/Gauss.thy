(*  Title:      HOL/Number_Theory/Gauss.thy
    Authors:    Jeremy Avigad, David Gray, and Adam Kramer

Ported by lcp but unfinished.
*)

section \<open>Gauss' Lemma\<close>

theory Gauss
  imports Euler_Criterion
begin

lemma cong_prime_prod_zero_nat:
  "[a * b = 0] (mod p) \<Longrightarrow> prime p \<Longrightarrow> [a = 0] (mod p) \<or> [b = 0] (mod p)"
  for a :: nat
  by (auto simp add: cong_altdef_nat prime_dvd_mult_iff)

lemma cong_prime_prod_zero_int:
  "[a * b = 0] (mod p) \<Longrightarrow> prime p \<Longrightarrow> [a = 0] (mod p) \<or> [b = 0] (mod p)"
  for a :: int
  by (simp add: cong_0_iff prime_dvd_mult_iff)


locale GAUSS =
  fixes p :: "nat"
  fixes a :: "int"
  assumes p_prime: "prime p"
  assumes p_ge_2: "2 < p"
  assumes p_a_relprime: "[a \<noteq> 0](mod p)"
  assumes a_nonzero: "0 < a"
begin

definition "A = {0::int <.. ((int p - 1) div 2)}"
definition "B = (\<lambda>x. x * a) ` A"
definition "C = (\<lambda>x. x mod p) ` B"
definition "D = C \<inter> {.. (int p - 1) div 2}"
definition "E = C \<inter> {(int p - 1) div 2 <..}"
definition "F = (\<lambda>x. (int p - x)) ` E"


subsection \<open>Basic properties of p\<close>

lemma odd_p: "odd p"
  by (metis p_prime p_ge_2 prime_odd_nat)

lemma p_minus_one_l: "(int p - 1) div 2 < p"
proof -
  have "(p - 1) div 2 \<le> (p - 1) div 1"
    by (metis div_by_1 div_le_dividend)
  also have "\<dots> = p - 1" by simp
  finally show ?thesis
    using p_ge_2 by arith
qed

lemma p_eq2: "int p = (2 * ((int p - 1) div 2)) + 1"
  using odd_p p_ge_2 nonzero_mult_div_cancel_left [of 2 "p - 1"] by simp

lemma p_odd_int: obtains z :: int where "int p = 2 * z + 1" "0 < z"
proof
  let ?z = "(int p - 1) div 2"
  show "int p = 2 * ?z + 1" by (rule p_eq2)
  show "0 < ?z"
    using p_ge_2 by linarith
qed


subsection \<open>Basic Properties of the Gauss Sets\<close>

lemma finite_A: "finite A"
  by (auto simp add: A_def)

lemma finite_B: "finite B"
  by (auto simp add: B_def finite_A)

lemma finite_C: "finite C"
  by (auto simp add: C_def finite_B)

lemma finite_D: "finite D"
  by (auto simp add: D_def finite_C)

lemma finite_E: "finite E"
  by (auto simp add: E_def finite_C)

lemma finite_F: "finite F"
  by (auto simp add: F_def finite_E)

lemma C_eq: "C = D \<union> E"
  by (auto simp add: C_def D_def E_def)

lemma A_card_eq: "card A = nat ((int p - 1) div 2)"
  by (auto simp add: A_def)

lemma inj_on_xa_A: "inj_on (\<lambda>x. x * a) A"
  using a_nonzero by (simp add: A_def inj_on_def)

definition ResSet :: "int \<Rightarrow> int set \<Rightarrow> bool"
  where "ResSet m X \<longleftrightarrow> (\<forall>y1 y2. y1 \<in> X \<and> y2 \<in> X \<and> [y1 = y2] (mod m) \<longrightarrow> y1 = y2)"

lemma ResSet_image:
  "0 < m \<Longrightarrow> ResSet m A \<Longrightarrow> \<forall>x \<in> A. \<forall>y \<in> A. ([f x = f y](mod m) \<longrightarrow> x = y) \<Longrightarrow> ResSet m (f ` A)"
  by (auto simp add: ResSet_def)

lemma A_res: "ResSet p A"
  using p_ge_2 by (auto simp add: A_def ResSet_def intro!: cong_less_imp_eq_int)

lemma B_res: "ResSet p B"
proof -
  have *: "x = y"
    if a: "[x * a = y * a] (mod p)"
    and b: "0 < x"
    and c: "x \<le> (int p - 1) div 2"
    and d: "0 < y"
    and e: "y \<le> (int p - 1) div 2"
    for x y
  proof -
    from p_a_relprime have "\<not> p dvd a"
      by (simp add: cong_0_iff)
    with p_prime prime_imp_coprime [of _ "nat \<bar>a\<bar>"]
    have "coprime a (int p)"
      by (simp_all add: ac_simps)
    with a cong_mult_rcancel [of a "int p" x y] have "[x = y] (mod p)"
      by simp
    with cong_less_imp_eq_int [of x y p] p_minus_one_l
      order_le_less_trans [of x "(int p - 1) div 2" p]
      order_le_less_trans [of y "(int p - 1) div 2" p]
    show ?thesis
      by (metis b c cong_less_imp_eq_int d e zero_less_imp_eq_int of_nat_0_le_iff)
  qed
  show ?thesis
    using p_ge_2 p_a_relprime p_minus_one_l
    by (metis "*" A_def A_res B_def GAUSS.ResSet_image GAUSS_axioms greaterThanAtMost_iff odd_p odd_pos of_nat_0_less_iff)
qed

lemma SR_B_inj: "inj_on (\<lambda>x. x mod p) B"
proof -
  have False
    if a: "x * a mod p = y * a mod p"
    and b: "0 < x"
    and c: "x \<le> (int p - 1) div 2"
    and d: "0 < y"
    and e: "y \<le> (int p - 1) div 2"
    and f: "x \<noteq> y"
    for x y
  proof -
    from a have a': "[x * a = y * a](mod p)"
      using cong_def by blast
    from p_a_relprime have "\<not>p dvd a"
      by (simp add: cong_0_iff)
    with p_prime prime_imp_coprime [of _ "nat \<bar>a\<bar>"]
    have "coprime a (int p)"
      by (simp_all add: ac_simps)  
    with a' cong_mult_rcancel [of a "int p" x y]
    have "[x = y] (mod p)" by simp
    with cong_less_imp_eq_int [of x y p] p_minus_one_l
      order_le_less_trans [of x "(int p - 1) div 2" p]
      order_le_less_trans [of y "(int p - 1) div 2" p]
    have "x = y"
      by (metis b c cong_less_imp_eq_int d e zero_less_imp_eq_int of_nat_0_le_iff)
    then show ?thesis
      by (simp add: f)
  qed
  then show ?thesis
    by (auto simp add: B_def inj_on_def A_def) metis
qed

lemma nonzero_mod_p: "0 < x \<Longrightarrow> x < int p \<Longrightarrow> [x \<noteq> 0](mod p)"
  for x :: int
  by (simp add: cong_def)

lemma A_ncong_p: "x \<in> A \<Longrightarrow> [x \<noteq> 0](mod p)"
  by (rule nonzero_mod_p) (auto simp add: A_def)

lemma A_greater_zero: "x \<in> A \<Longrightarrow> 0 < x"
  by (auto simp add: A_def)

lemma B_ncong_p: "x \<in> B \<Longrightarrow> [x \<noteq> 0](mod p)"
  by (auto simp: B_def p_prime p_a_relprime A_ncong_p dest: cong_prime_prod_zero_int)

lemma B_greater_zero: "x \<in> B \<Longrightarrow> 0 < x"
  using a_nonzero by (auto simp add: B_def A_greater_zero)

lemma B_mod_greater_zero:
  "0 < x mod int p" if "x \<in> B"
proof -
  from that have "x mod int p \<noteq> 0"
    using B_ncong_p cong_def cong_mult_self_left by blast
  moreover from that have "0 < x"
    by (rule B_greater_zero)
  then have "0 \<le> x mod int p"
    by (auto simp add: mod_int_pos_iff intro: neq_le_trans)
  ultimately show ?thesis
    by simp
qed

lemma C_greater_zero: "y \<in> C \<Longrightarrow> 0 < y"
  by (auto simp add: C_def B_mod_greater_zero)

lemma F_subset: "F \<subseteq> {x. 0 < x \<and> x \<le> ((int p - 1) div 2)}"
  using p_ge_2 by (auto simp add: F_def E_def C_def intro: p_odd_int)

lemma D_subset: "D \<subseteq> {x. 0 < x \<and> x \<le> ((p - 1) div 2)}"
  by (auto simp add: D_def C_greater_zero)

lemma F_eq: "F = {x. \<exists>y \<in> A. (x = p - ((y * a) mod p) \<and> (int p - 1) div 2 < (y * a) mod p)}"
  by (auto simp add: F_def E_def D_def C_def B_def A_def)

lemma D_eq: "D = {x. \<exists>y \<in> A. (x = (y * a) mod p \<and> (y * a) mod p \<le> (int p - 1) div 2)}"
  by (auto simp add: D_def C_def B_def A_def)

lemma all_A_relprime:
  "coprime x p" if "x \<in> A"
proof -
  from A_ncong_p [OF that] have "\<not> int p dvd x"
    by (simp add: cong_0_iff)
  with p_prime show ?thesis
    by (metis (no_types) coprime_commute prime_imp_coprime prime_nat_int_transfer)
qed
  
lemma A_prod_relprime: "coprime (prod id A) p"
  by (auto intro: prod_coprime_left all_A_relprime)


subsection \<open>Relationships Between Gauss Sets\<close>

lemma StandardRes_inj_on_ResSet: "ResSet m X \<Longrightarrow> inj_on (\<lambda>b. b mod m) X"
  by (auto simp add: ResSet_def inj_on_def cong_def)

lemma B_card_eq_A: "card B = card A"
  using finite_A by (simp add: finite_A B_def inj_on_xa_A card_image)

lemma B_card_eq: "card B = nat ((int p - 1) div 2)"
  by (simp add: B_card_eq_A A_card_eq)

lemma F_card_eq_E: "card F = card E"
  using finite_E by (simp add: F_def card_image)

lemma C_card_eq_B: "card C = card B"
proof -
  have "inj_on (\<lambda>x. x mod p) B"
    by (metis SR_B_inj)
  then show ?thesis
    by (metis C_def card_image)
qed

lemma D_E_disj: "D \<inter> E = {}"
  by (auto simp add: D_def E_def)

lemma C_card_eq_D_plus_E: "card C = card D + card E"
  by (auto simp add: C_eq card_Un_disjoint D_E_disj finite_D finite_E)

lemma C_prod_eq_D_times_E: "prod id E * prod id D = prod id C"
  by (metis C_eq D_E_disj finite_D finite_E inf_commute prod.union_disjoint sup_commute)

lemma C_B_zcong_prod: "[prod id C = prod id B] (mod p)"
  apply (auto simp add: C_def)
  apply (insert finite_B SR_B_inj)
  apply (drule prod.reindex [of "\<lambda>x. x mod int p" B id])
  apply auto
  apply (rule cong_prod)
  apply (auto simp add: cong_def)
  done

lemma F_Un_D_subset: "(F \<union> D) \<subseteq> A"
  by (intro Un_least subset_trans [OF F_subset] subset_trans [OF D_subset]) (auto simp: A_def)

lemma F_D_disj: "(F \<inter> D) = {}"
proof (auto simp add: F_eq D_eq)
  fix y z :: int
  assume "p - (y * a) mod p = (z * a) mod p"
  then have "[(y * a) mod p + (z * a) mod p = 0] (mod p)"
    by (metis add.commute diff_eq_eq dvd_refl cong_def dvd_eq_mod_eq_0 mod_0)
  moreover have "[y * a = (y * a) mod p] (mod p)"
    by (metis cong_def mod_mod_trivial)
  ultimately have "[a * (y + z) = 0] (mod p)"
    by (metis cong_def mod_add_left_eq mod_add_right_eq mult.commute ring_class.ring_distribs(1))
  with p_prime a_nonzero p_a_relprime have a: "[y + z = 0] (mod p)"
    by (auto dest!: cong_prime_prod_zero_int)
  assume b: "y \<in> A" and c: "z \<in> A"
  then have "0 < y + z"
    by (auto simp: A_def)
  moreover from b c p_eq2 have "y + z < p"
    by (auto simp: A_def)
  ultimately show False
    by (metis a nonzero_mod_p)
qed

lemma F_Un_D_card: "card (F \<union> D) = nat ((p - 1) div 2)"
proof -
  have "card (F \<union> D) = card E + card D"
    by (auto simp add: finite_F finite_D F_D_disj card_Un_disjoint F_card_eq_E)
  then have "card (F \<union> D) = card C"
    by (simp add: C_card_eq_D_plus_E)
  then show "card (F \<union> D) = nat ((p - 1) div 2)"
    by (simp add: C_card_eq_B B_card_eq)
qed

lemma F_Un_D_eq_A: "F \<union> D = A"
  using finite_A F_Un_D_subset A_card_eq F_Un_D_card by (auto simp add: card_seteq)

lemma prod_D_F_eq_prod_A: "prod id D * prod id F = prod id A"
  by (metis F_D_disj F_Un_D_eq_A Int_commute Un_commute finite_D finite_F prod.union_disjoint)

lemma prod_F_zcong: "[prod id F = ((-1) ^ (card E)) * prod id E] (mod p)"
proof -
  have FE: "prod id F = prod ((-) p) E"
    using finite_E prod.reindex[OF inj_on_diff_left] by (auto simp add: F_def)
  then have "\<forall>x \<in> E. [(p-x) mod p = - x](mod p)"
    by (metis cong_def minus_mod_self1 mod_mod_trivial)
  then have "[prod ((\<lambda>x. x mod p) \<circ> ((-) p)) E = prod (uminus) E](mod p)"
    using finite_E p_ge_2 cong_prod [of E "(\<lambda>x. x mod p) \<circ> ((-) p)" uminus p]
    by auto
  then have two: "[prod id F = prod (uminus) E](mod p)"
    by (metis FE cong_cong_mod_int cong_refl cong_prod minus_mod_self1)
  have "prod uminus E = (-1) ^ card E * prod id E"
    using finite_E by (induct set: finite) auto
  with two show ?thesis
    by simp
qed


subsection \<open>Gauss' Lemma\<close>

lemma aux: "prod id A * (- 1) ^ card E * a ^ card A * (- 1) ^ card E = prod id A * a ^ card A"
  by auto

theorem pre_gauss_lemma: "[a ^ nat((int p - 1) div 2) = (-1) ^ (card E)] (mod p)"
proof -
  have "[prod id A = prod id F * prod id D](mod p)"
    by (auto simp: prod_D_F_eq_prod_A mult.commute cong del: prod.cong_simp)
  then have "[prod id A = ((-1)^(card E) * prod id E) * prod id D] (mod p)"
    by (rule cong_trans) (metis cong_scalar_right prod_F_zcong)
  then have "[prod id A = ((-1)^(card E) * prod id C)] (mod p)"
    using finite_D finite_E by (auto simp add: ac_simps C_prod_eq_D_times_E C_eq D_E_disj prod.union_disjoint)
  then have "[prod id A = ((-1)^(card E) * prod id B)] (mod p)"
    by (rule cong_trans) (metis C_B_zcong_prod cong_scalar_left)
  then have "[prod id A = ((-1)^(card E) * prod id ((\<lambda>x. x * a) ` A))] (mod p)"
    by (simp add: B_def)
  then have "[prod id A = ((-1)^(card E) * prod (\<lambda>x. x * a) A)] (mod p)"
    by (simp add: inj_on_xa_A prod.reindex)
  moreover have "prod (\<lambda>x. x * a) A = prod (\<lambda>x. a) A * prod id A"
    using finite_A by (induct set: finite) auto
  ultimately have "[prod id A = ((-1)^(card E) * (prod (\<lambda>x. a) A * prod id A))] (mod p)"
    by simp
  then have "[prod id A = ((-1)^(card E) * a^(card A) * prod id A)](mod p)"
    by (rule cong_trans)
      (simp add: cong_scalar_left cong_scalar_right finite_A ac_simps)
  then have a: "[prod id A * (-1)^(card E) =
      ((-1)^(card E) * a^(card A) * prod id A * (-1)^(card E))](mod p)"
    by (rule cong_scalar_right)
  then have "[prod id A * (-1)^(card E) = prod id A *
      (-1)^(card E) * a^(card A) * (-1)^(card E)](mod p)"
    by (rule cong_trans) (simp add: a ac_simps)
  then have "[prod id A * (-1)^(card E) = prod id A * a^(card A)](mod p)"
    by (rule cong_trans) (simp add: aux cong del: prod.cong_simp)
  with A_prod_relprime have "[(- 1) ^ card E = a ^ card A](mod p)"
    by (metis cong_mult_lcancel)
  then show ?thesis
    by (simp add: A_card_eq cong_sym)
qed

theorem gauss_lemma: "Legendre a p = (-1) ^ (card E)"
proof -
  from euler_criterion p_prime p_ge_2 have "[Legendre a p = a^(nat (((p) - 1) div 2))] (mod p)"
    by auto
  moreover have "int ((p - 1) div 2) = (int p - 1) div 2"
    using p_eq2 by linarith
  then have "[a ^ nat (int ((p - 1) div 2)) = a ^ nat ((int p - 1) div 2)] (mod int p)"
    by force
  ultimately have "[Legendre a p = (-1) ^ (card E)] (mod p)"
    using pre_gauss_lemma cong_trans by blast
  moreover from p_a_relprime have "Legendre a p = 1 \<or> Legendre a p = -1"
    by (auto simp add: Legendre_def)
  moreover have "(-1::int) ^ (card E) = 1 \<or> (-1::int) ^ (card E) = -1"
    using neg_one_even_power neg_one_odd_power by blast
  moreover have "[1 \<noteq> - 1] (mod int p)"
    using cong_iff_dvd_diff [where 'a=int] nonzero_mod_p[of 2] p_odd_int   
    by fastforce
  ultimately show ?thesis
    by (auto simp add: cong_sym)
qed

end

end
