(*  Title:      HOL/Old_Number_Theory/Gauss.thy
    Authors:    Jeremy Avigad, David Gray, and Adam Kramer
*)

header {* Gauss' Lemma *}

theory Gauss
imports Euler
begin

locale GAUSS =
  fixes p :: "int"
  fixes a :: "int"

  assumes p_prime: "zprime p"
  assumes p_g_2: "2 < p"
  assumes p_a_relprime: "~[a = 0](mod p)"
  assumes a_nonzero:    "0 < a"
begin

definition "A = {(x::int). 0 < x & x \<le> ((p - 1) div 2)}"
definition "B = (%x. x * a) ` A"
definition "C = StandardRes p ` B"
definition "D = C \<inter> {x. x \<le> ((p - 1) div 2)}"
definition "E = C \<inter> {x. ((p - 1) div 2) < x}"
definition "F = (%x. (p - x)) ` E"


subsection {* Basic properties of p *}

lemma p_odd: "p \<in> zOdd"
  by (auto simp add: p_prime p_g_2 zprime_zOdd_eq_grt_2)

lemma p_g_0: "0 < p"
  using p_g_2 by auto

lemma int_nat: "int (nat ((p - 1) div 2)) = (p - 1) div 2"
  using ListMem.insert p_g_2 by (auto simp add: pos_imp_zdiv_nonneg_iff)

lemma p_minus_one_l: "(p - 1) div 2 < p"
proof -
  have "(p - 1) div 2 \<le> (p - 1) div 1"
    by (rule zdiv_mono2) (auto simp add: p_g_0)
  also have "\<dots> = p - 1" by simp
  finally show ?thesis by simp
qed

lemma p_eq: "p = (2 * (p - 1) div 2) + 1"
  using div_mult_self1_is_id [of 2 "p - 1"] by auto


lemma (in -) zodd_imp_zdiv_eq: "x \<in> zOdd ==> 2 * (x - 1) div 2 = 2 * ((x - 1) div 2)"
  apply (frule odd_minus_one_even)
  apply (simp add: zEven_def)
  apply (subgoal_tac "2 \<noteq> 0")
  apply (frule_tac b = "2 :: int" and a = "x - 1" in div_mult_self1_is_id)
  apply (auto simp add: even_div_2_prop2)
  done


lemma p_eq2: "p = (2 * ((p - 1) div 2)) + 1"
  apply (insert p_eq p_prime p_g_2 zprime_zOdd_eq_grt_2 [of p], auto)
  apply (frule zodd_imp_zdiv_eq, auto)
  done


subsection {* Basic Properties of the Gauss Sets *}

lemma finite_A: "finite (A)"
by (auto simp add: A_def)

lemma finite_B: "finite (B)"
by (auto simp add: B_def finite_A)

lemma finite_C: "finite (C)"
by (auto simp add: C_def finite_B)

lemma finite_D: "finite (D)"
by (auto simp add: D_def finite_C)

lemma finite_E: "finite (E)"
by (auto simp add: E_def finite_C)

lemma finite_F: "finite (F)"
by (auto simp add: F_def finite_E)

lemma C_eq: "C = D \<union> E"
by (auto simp add: C_def D_def E_def)

lemma A_card_eq: "card A = nat ((p - 1) div 2)"
  apply (auto simp add: A_def)
  apply (insert int_nat)
  apply (erule subst)
  apply (auto simp add: card_bdd_int_set_l_le)
  done

lemma inj_on_xa_A: "inj_on (%x. x * a) A"
  using a_nonzero by (simp add: A_def inj_on_def)

lemma A_res: "ResSet p A"
  apply (auto simp add: A_def ResSet_def)
  apply (rule_tac m = p in zcong_less_eq)
  apply (insert p_g_2, auto)
  done

lemma B_res: "ResSet p B"
  apply (insert p_g_2 p_a_relprime p_minus_one_l)
  apply (auto simp add: B_def)
  apply (rule ResSet_image)
  apply (auto simp add: A_res)
  apply (auto simp add: A_def)
proof -
  fix x fix y
  assume a: "[x * a = y * a] (mod p)"
  assume b: "0 < x"
  assume c: "x \<le> (p - 1) div 2"
  assume d: "0 < y"
  assume e: "y \<le> (p - 1) div 2"
  from a p_a_relprime p_prime a_nonzero zcong_cancel [of p a x y]
  have "[x = y](mod p)"
    by (simp add: zprime_imp_zrelprime zcong_def p_g_0 order_le_less)
  with zcong_less_eq [of x y p] p_minus_one_l
      order_le_less_trans [of x "(p - 1) div 2" p]
      order_le_less_trans [of y "(p - 1) div 2" p] show "x = y"
    by (simp add: b c d e p_minus_one_l p_g_0)
qed

lemma SR_B_inj: "inj_on (StandardRes p) B"
  apply (auto simp add: B_def StandardRes_def inj_on_def A_def)
proof -
  fix x fix y
  assume a: "x * a mod p = y * a mod p"
  assume b: "0 < x"
  assume c: "x \<le> (p - 1) div 2"
  assume d: "0 < y"
  assume e: "y \<le> (p - 1) div 2"
  assume f: "x \<noteq> y"
  from a have "[x * a = y * a](mod p)"
    by (simp add: zcong_zmod_eq p_g_0)
  with p_a_relprime p_prime a_nonzero zcong_cancel [of p a x y]
  have "[x = y](mod p)"
    by (simp add: zprime_imp_zrelprime zcong_def p_g_0 order_le_less)
  with zcong_less_eq [of x y p] p_minus_one_l
    order_le_less_trans [of x "(p - 1) div 2" p]
    order_le_less_trans [of y "(p - 1) div 2" p] have "x = y"
    by (simp add: b c d e p_minus_one_l p_g_0)
  then have False
    by (simp add: f)
  then show "a = 0"
    by simp
qed

lemma inj_on_pminusx_E: "inj_on (%x. p - x) E"
  apply (auto simp add: E_def C_def B_def A_def)
  apply (rule_tac g = "%x. -1 * (x - p)" in inj_on_inverseI)
  apply auto
  done

lemma A_ncong_p: "x \<in> A ==> ~[x = 0](mod p)"
  apply (auto simp add: A_def)
  apply (frule_tac m = p in zcong_not_zero)
  apply (insert p_minus_one_l)
  apply auto
  done

lemma A_greater_zero: "x \<in> A ==> 0 < x"
  by (auto simp add: A_def)

lemma B_ncong_p: "x \<in> B ==> ~[x = 0](mod p)"
  apply (auto simp add: B_def)
  apply (frule A_ncong_p)
  apply (insert p_a_relprime p_prime a_nonzero)
  apply (frule_tac a = x and b = a in zcong_zprime_prod_zero_contra)
  apply (auto simp add: A_greater_zero)
  done

lemma B_greater_zero: "x \<in> B ==> 0 < x"
  using a_nonzero by (auto simp add: B_def mult_pos_pos A_greater_zero)

lemma C_ncong_p: "x \<in> C ==>  ~[x = 0](mod p)"
  apply (auto simp add: C_def)
  apply (frule B_ncong_p)
  apply (subgoal_tac "[x = StandardRes p x](mod p)")
  defer apply (simp add: StandardRes_prop1)
  apply (frule_tac a = x and b = "StandardRes p x" and c = 0 in zcong_trans)
  apply auto
  done

lemma C_greater_zero: "y \<in> C ==> 0 < y"
  apply (auto simp add: C_def)
proof -
  fix x
  assume a: "x \<in> B"
  from p_g_0 have "0 \<le> StandardRes p x"
    by (simp add: StandardRes_lbound)
  moreover have "~[x = 0] (mod p)"
    by (simp add: a B_ncong_p)
  then have "StandardRes p x \<noteq> 0"
    by (simp add: StandardRes_prop3)
  ultimately show "0 < StandardRes p x"
    by (simp add: order_le_less)
qed

lemma D_ncong_p: "x \<in> D ==> ~[x = 0](mod p)"
  by (auto simp add: D_def C_ncong_p)

lemma E_ncong_p: "x \<in> E ==> ~[x = 0](mod p)"
  by (auto simp add: E_def C_ncong_p)

lemma F_ncong_p: "x \<in> F ==> ~[x = 0](mod p)"
  apply (auto simp add: F_def)
proof -
  fix x assume a: "x \<in> E" assume b: "[p - x = 0] (mod p)"
  from E_ncong_p have "~[x = 0] (mod p)"
    by (simp add: a)
  moreover from a have "0 < x"
    by (simp add: a E_def C_greater_zero)
  moreover from a have "x < p"
    by (auto simp add: E_def C_def p_g_0 StandardRes_ubound)
  ultimately have "~[p - x = 0] (mod p)"
    by (simp add: zcong_not_zero)
  from this show False by (simp add: b)
qed

lemma F_subset: "F \<subseteq> {x. 0 < x & x \<le> ((p - 1) div 2)}"
  apply (auto simp add: F_def E_def)
  apply (insert p_g_0)
  apply (frule_tac x = xa in StandardRes_ubound)
  apply (frule_tac x = x in StandardRes_ubound)
  apply (subgoal_tac "xa = StandardRes p xa")
  apply (auto simp add: C_def StandardRes_prop2 StandardRes_prop1)
proof -
  from zodd_imp_zdiv_eq p_prime p_g_2 zprime_zOdd_eq_grt_2 have
    "2 * (p - 1) div 2 = 2 * ((p - 1) div 2)"
    by simp
  with p_eq2 show " !!x. [| (p - 1) div 2 < StandardRes p x; x \<in> B |]
      ==> p - StandardRes p x \<le> (p - 1) div 2"
    by simp
qed

lemma D_subset: "D \<subseteq> {x. 0 < x & x \<le> ((p - 1) div 2)}"
  by (auto simp add: D_def C_greater_zero)

lemma F_eq: "F = {x. \<exists>y \<in> A. ( x = p - (StandardRes p (y*a)) & (p - 1) div 2 < StandardRes p (y*a))}"
  by (auto simp add: F_def E_def D_def C_def B_def A_def)

lemma D_eq: "D = {x. \<exists>y \<in> A. ( x = StandardRes p (y*a) & StandardRes p (y*a) \<le> (p - 1) div 2)}"
  by (auto simp add: D_def C_def B_def A_def)

lemma D_leq: "x \<in> D ==> x \<le> (p - 1) div 2"
  by (auto simp add: D_eq)

lemma F_ge: "x \<in> F ==> x \<le> (p - 1) div 2"
  apply (auto simp add: F_eq A_def)
proof -
  fix y
  assume "(p - 1) div 2 < StandardRes p (y * a)"
  then have "p - StandardRes p (y * a) < p - ((p - 1) div 2)"
    by arith
  also from p_eq2 have "... = 2 * ((p - 1) div 2) + 1 - ((p - 1) div 2)"
    by auto
  also have "2 * ((p - 1) div 2) + 1 - (p - 1) div 2 = (p - 1) div 2 + 1"
    by arith
  finally show "p - StandardRes p (y * a) \<le> (p - 1) div 2"
    using zless_add1_eq [of "p - StandardRes p (y * a)" "(p - 1) div 2"] by auto
qed

lemma all_A_relprime: "\<forall>x \<in> A. zgcd x p = 1"
  using p_prime p_minus_one_l by (auto simp add: A_def zless_zprime_imp_zrelprime)

lemma A_prod_relprime: "zgcd (setprod id A) p = 1"
by(rule all_relprime_prod_relprime[OF finite_A all_A_relprime])


subsection {* Relationships Between Gauss Sets *}

lemma B_card_eq_A: "card B = card A"
  using finite_A by (simp add: finite_A B_def inj_on_xa_A card_image)

lemma B_card_eq: "card B = nat ((p - 1) div 2)"
  by (simp add: B_card_eq_A A_card_eq)

lemma F_card_eq_E: "card F = card E"
  using finite_E by (simp add: F_def inj_on_pminusx_E card_image)

lemma C_card_eq_B: "card C = card B"
  apply (insert finite_B)
  apply (subgoal_tac "inj_on (StandardRes p) B")
  apply (simp add: B_def C_def card_image)
  apply (rule StandardRes_inj_on_ResSet)
  apply (simp add: B_res)
  done

lemma D_E_disj: "D \<inter> E = {}"
  by (auto simp add: D_def E_def)

lemma C_card_eq_D_plus_E: "card C = card D + card E"
  by (auto simp add: C_eq card_Un_disjoint D_E_disj finite_D finite_E)

lemma C_prod_eq_D_times_E: "setprod id E * setprod id D = setprod id C"
  apply (insert D_E_disj finite_D finite_E C_eq)
  apply (frule setprod_Un_disjoint [of D E id])
  apply auto
  done

lemma C_B_zcong_prod: "[setprod id C = setprod id B] (mod p)"
  apply (auto simp add: C_def)
  apply (insert finite_B SR_B_inj)
  apply (frule_tac f = "StandardRes p" in setprod_reindex_id [symmetric], auto)
  apply (rule setprod_same_function_zcong)
  apply (auto simp add: StandardRes_prop1 zcong_sym p_g_0)
  done

lemma F_Un_D_subset: "(F \<union> D) \<subseteq> A"
  apply (rule Un_least)
  apply (auto simp add: A_def F_subset D_subset)
  done

lemma F_D_disj: "(F \<inter> D) = {}"
  apply (simp add: F_eq D_eq)
  apply (auto simp add: F_eq D_eq)
proof -
  fix y fix ya
  assume "p - StandardRes p (y * a) = StandardRes p (ya * a)"
  then have "p = StandardRes p (y * a) + StandardRes p (ya * a)"
    by arith
  moreover have "p dvd p"
    by auto
  ultimately have "p dvd (StandardRes p (y * a) + StandardRes p (ya * a))"
    by auto
  then have a: "[StandardRes p (y * a) + StandardRes p (ya * a) = 0] (mod p)"
    by (auto simp add: zcong_def)
  have "[y * a = StandardRes p (y * a)] (mod p)"
    by (simp only: zcong_sym StandardRes_prop1)
  moreover have "[ya * a = StandardRes p (ya * a)] (mod p)"
    by (simp only: zcong_sym StandardRes_prop1)
  ultimately have "[y * a + ya * a =
    StandardRes p (y * a) + StandardRes p (ya * a)] (mod p)"
    by (rule zcong_zadd)
  with a have "[y * a + ya * a = 0] (mod p)"
    apply (elim zcong_trans)
    by (simp only: zcong_refl)
  also have "y * a + ya * a = a * (y + ya)"
    by (simp add: right_distrib mult_commute)
  finally have "[a * (y + ya) = 0] (mod p)" .
  with p_prime a_nonzero zcong_zprime_prod_zero [of p a "y + ya"]
    p_a_relprime
  have a: "[y + ya = 0] (mod p)"
    by auto
  assume b: "y \<in> A" and c: "ya: A"
  with A_def have "0 < y + ya"
    by auto
  moreover from b c A_def have "y + ya \<le> (p - 1) div 2 + (p - 1) div 2"
    by auto
  moreover from b c p_eq2 A_def have "y + ya < p"
    by auto
  ultimately show False
    apply simp
    apply (frule_tac m = p in zcong_not_zero)
    apply (auto simp add: a)
    done
qed

lemma F_Un_D_card: "card (F \<union> D) = nat ((p - 1) div 2)"
proof -
  have "card (F \<union> D) = card E + card D"
    by (auto simp add: finite_F finite_D F_D_disj
      card_Un_disjoint F_card_eq_E)
  then have "card (F \<union> D) = card C"
    by (simp add: C_card_eq_D_plus_E)
  from this show "card (F \<union> D) = nat ((p - 1) div 2)"
    by (simp add: C_card_eq_B B_card_eq)
qed

lemma F_Un_D_eq_A: "F \<union> D = A"
  using finite_A F_Un_D_subset A_card_eq F_Un_D_card by (auto simp add: card_seteq)

lemma prod_D_F_eq_prod_A:
    "(setprod id D) * (setprod id F) = setprod id A"
  apply (insert F_D_disj finite_D finite_F)
  apply (frule setprod_Un_disjoint [of F D id])
  apply (auto simp add: F_Un_D_eq_A)
  done

lemma prod_F_zcong:
  "[setprod id F = ((-1) ^ (card E)) * (setprod id E)] (mod p)"
proof -
  have "setprod id F = setprod id (op - p ` E)"
    by (auto simp add: F_def)
  then have "setprod id F = setprod (op - p) E"
    apply simp
    apply (insert finite_E inj_on_pminusx_E)
    apply (frule_tac f = "op - p" in setprod_reindex_id, auto)
    done
  then have one:
    "[setprod id F = setprod (StandardRes p o (op - p)) E] (mod p)"
    apply simp
    apply (insert p_g_0 finite_E StandardRes_prod)
    by (auto)
  moreover have a: "\<forall>x \<in> E. [p - x = 0 - x] (mod p)"
    apply clarify
    apply (insert zcong_id [of p])
    apply (rule_tac a = p and m = p and c = x and d = x in zcong_zdiff, auto)
    done
  moreover have b: "\<forall>x \<in> E. [StandardRes p (p - x) = p - x](mod p)"
    apply clarify
    apply (simp add: StandardRes_prop1 zcong_sym)
    done
  moreover have "\<forall>x \<in> E. [StandardRes p (p - x) = - x](mod p)"
    apply clarify
    apply (insert a b)
    apply (rule_tac b = "p - x" in zcong_trans, auto)
    done
  ultimately have c:
    "[setprod (StandardRes p o (op - p)) E = setprod (uminus) E](mod p)"
    apply simp
    using finite_E p_g_0
      setprod_same_function_zcong [of E "StandardRes p o (op - p)" uminus p]
    by auto
  then have two: "[setprod id F = setprod (uminus) E](mod p)"
    apply (insert one c)
    apply (rule zcong_trans [of "setprod id F"
                               "setprod (StandardRes p o op - p) E" p
                               "setprod uminus E"], auto)
    done
  also have "setprod uminus E = (setprod id E) * (-1)^(card E)"
    using finite_E by (induct set: finite) auto
  then have "setprod uminus E = (-1) ^ (card E) * (setprod id E)"
    by (simp add: mult_commute)
  with two show ?thesis
    by simp
qed


subsection {* Gauss' Lemma *}

lemma aux: "setprod id A * -1 ^ card E * a ^ card A * -1 ^ card E = setprod id A * a ^ card A"
  by (auto simp add: finite_E neg_one_special)

theorem pre_gauss_lemma:
  "[a ^ nat((p - 1) div 2) = (-1) ^ (card E)] (mod p)"
proof -
  have "[setprod id A = setprod id F * setprod id D](mod p)"
    by (auto simp add: prod_D_F_eq_prod_A mult_commute cong del:setprod_cong)
  then have "[setprod id A = ((-1)^(card E) * setprod id E) *
      setprod id D] (mod p)"
    apply (rule zcong_trans)
    apply (auto simp add: prod_F_zcong zcong_scalar cong del: setprod_cong)
    done
  then have "[setprod id A = ((-1)^(card E) * setprod id C)] (mod p)"
    apply (rule zcong_trans)
    apply (insert C_prod_eq_D_times_E, erule subst)
    apply (subst mult_assoc, auto)
    done
  then have "[setprod id A = ((-1)^(card E) * setprod id B)] (mod p)"
    apply (rule zcong_trans)
    apply (simp add: C_B_zcong_prod zcong_scalar2 cong del:setprod_cong)
    done
  then have "[setprod id A = ((-1)^(card E) *
    (setprod id ((%x. x * a) ` A)))] (mod p)"
    by (simp add: B_def)
  then have "[setprod id A = ((-1)^(card E) * (setprod (%x. x * a) A))]
    (mod p)"
    by (simp add:finite_A inj_on_xa_A setprod_reindex_id[symmetric] cong del:setprod_cong)
  moreover have "setprod (%x. x * a) A =
    setprod (%x. a) A * setprod id A"
    using finite_A by (induct set: finite) auto
  ultimately have "[setprod id A = ((-1)^(card E) * (setprod (%x. a) A *
    setprod id A))] (mod p)"
    by simp
  then have "[setprod id A = ((-1)^(card E) * a^(card A) *
      setprod id A)](mod p)"
    apply (rule zcong_trans)
    apply (simp add: zcong_scalar2 zcong_scalar finite_A setprod_constant mult_assoc)
    done
  then have a: "[setprod id A * (-1)^(card E) =
      ((-1)^(card E) * a^(card A) * setprod id A * (-1)^(card E))](mod p)"
    by (rule zcong_scalar)
  then have "[setprod id A * (-1)^(card E) = setprod id A *
      (-1)^(card E) * a^(card A) * (-1)^(card E)](mod p)"
    apply (rule zcong_trans)
    apply (simp add: a mult_commute mult_left_commute)
    done
  then have "[setprod id A * (-1)^(card E) = setprod id A *
      a^(card A)](mod p)"
    apply (rule zcong_trans)
    apply (simp add: aux cong del:setprod_cong)
    done
  with this zcong_cancel2 [of p "setprod id A" "-1 ^ card E" "a ^ card A"]
      p_g_0 A_prod_relprime have "[-1 ^ card E = a ^ card A](mod p)"
    by (simp add: order_less_imp_le)
  from this show ?thesis
    by (simp add: A_card_eq zcong_sym)
qed

theorem gauss_lemma: "(Legendre a p) = (-1) ^ (card E)"
proof -
  from Euler_Criterion p_prime p_g_2 have
      "[(Legendre a p) = a^(nat (((p) - 1) div 2))] (mod p)"
    by auto
  moreover note pre_gauss_lemma
  ultimately have "[(Legendre a p) = (-1) ^ (card E)] (mod p)"
    by (rule zcong_trans)
  moreover from p_a_relprime have "(Legendre a p) = 1 | (Legendre a p) = (-1)"
    by (auto simp add: Legendre_def)
  moreover have "(-1::int) ^ (card E) = 1 | (-1::int) ^ (card E) = -1"
    by (rule neg_one_power)
  ultimately show ?thesis
    by (auto simp add: p_g_2 one_not_neg_one_mod_m zcong_sym)
qed

end

end
