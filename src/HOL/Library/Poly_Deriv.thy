(*  Title:      HOL/Library/Poly_Deriv.thy
    Author:     Amine Chaieb
    Author:     Brian Huffman
*)

header{* Polynomials and Differentiation *}

theory Poly_Deriv
imports Deriv Polynomial
begin

subsection {* Derivatives of univariate polynomials *}

function pderiv :: "'a::real_normed_field poly \<Rightarrow> 'a poly"
where
  [simp del]: "pderiv (pCons a p) = (if p = 0 then 0 else p + pCons 0 (pderiv p))"
  by (auto intro: pCons_cases)

termination pderiv
  by (relation "measure degree") simp_all

lemma pderiv_0 [simp]:
  "pderiv 0 = 0"
  using pderiv.simps [of 0 0] by simp

lemma pderiv_pCons:
  "pderiv (pCons a p) = p + pCons 0 (pderiv p)"
  by (simp add: pderiv.simps)

lemma coeff_pderiv: "coeff (pderiv p) n = of_nat (Suc n) * coeff p (Suc n)"
  by (induct p arbitrary: n) 
     (auto simp add: pderiv_pCons coeff_pCons algebra_simps split: nat.split)

primrec pderiv_coeffs :: "'a::comm_monoid_add list \<Rightarrow> 'a list"
where
  "pderiv_coeffs [] = []"
| "pderiv_coeffs (x # xs) = plus_coeffs xs (cCons 0 (pderiv_coeffs xs))"

lemma coeffs_pderiv [code abstract]:
  "coeffs (pderiv p) = pderiv_coeffs (coeffs p)"
  by (rule sym, induct p) (simp_all add: pderiv_pCons coeffs_plus_eq_plus_coeffs cCons_def)

lemma pderiv_eq_0_iff: "pderiv p = 0 \<longleftrightarrow> degree p = 0"
  apply (rule iffI)
  apply (cases p, simp)
  apply (simp add: poly_eq_iff coeff_pderiv del: of_nat_Suc)
  apply (simp add: poly_eq_iff coeff_pderiv coeff_eq_0)
  done

lemma degree_pderiv: "degree (pderiv p) = degree p - 1"
  apply (rule order_antisym [OF degree_le])
  apply (simp add: coeff_pderiv coeff_eq_0)
  apply (cases "degree p", simp)
  apply (rule le_degree)
  apply (simp add: coeff_pderiv del: of_nat_Suc)
  apply (metis degree_0 leading_coeff_0_iff nat.distinct(1))
  done

lemma pderiv_singleton [simp]: "pderiv [:a:] = 0"
by (simp add: pderiv_pCons)

lemma pderiv_add: "pderiv (p + q) = pderiv p + pderiv q"
by (rule poly_eqI, simp add: coeff_pderiv algebra_simps)

lemma pderiv_minus: "pderiv (- p) = - pderiv p"
by (rule poly_eqI, simp add: coeff_pderiv)

lemma pderiv_diff: "pderiv (p - q) = pderiv p - pderiv q"
by (rule poly_eqI, simp add: coeff_pderiv algebra_simps)

lemma pderiv_smult: "pderiv (smult a p) = smult a (pderiv p)"
by (rule poly_eqI, simp add: coeff_pderiv algebra_simps)

lemma pderiv_mult: "pderiv (p * q) = p * pderiv q + q * pderiv p"
by (induct p) (auto simp: pderiv_add pderiv_smult pderiv_pCons algebra_simps)

lemma pderiv_power_Suc:
  "pderiv (p ^ Suc n) = smult (of_nat (Suc n)) (p ^ n) * pderiv p"
apply (induct n)
apply simp
apply (subst power_Suc)
apply (subst pderiv_mult)
apply (erule ssubst)
apply (simp only: of_nat_Suc smult_add_left smult_1_left)
apply (simp add: algebra_simps)
done

lemma DERIV_pow2: "DERIV (%x. x ^ Suc n) x :> real (Suc n) * (x ^ n)"
by (rule DERIV_cong, rule DERIV_pow, simp)
declare DERIV_pow2 [simp] DERIV_pow [simp]

lemma DERIV_add_const: "DERIV f x :> D ==>  DERIV (%x. a + f x :: 'a::real_normed_field) x :> D"
by (rule DERIV_cong, rule DERIV_add, auto)

lemma poly_DERIV[simp]: "DERIV (%x. poly p x) x :> poly (pderiv p) x"
  by (induct p, auto intro!: derivative_eq_intros simp add: pderiv_pCons)

text{* Consequences of the derivative theorem above*}

lemma poly_differentiable[simp]: "(%x. poly p x) differentiable (at x::real filter)"
apply (simp add: real_differentiable_def)
apply (blast intro: poly_DERIV)
done

lemma poly_isCont[simp]: "isCont (%x. poly p x) (x::real)"
by (rule poly_DERIV [THEN DERIV_isCont])

lemma poly_IVT_pos: "[| a < b; poly p (a::real) < 0; 0 < poly p b |]
      ==> \<exists>x. a < x & x < b & (poly p x = 0)"
using IVT_objl [of "poly p" a 0 b]
by (auto simp add: order_le_less)

lemma poly_IVT_neg: "[| (a::real) < b; 0 < poly p a; poly p b < 0 |]
      ==> \<exists>x. a < x & x < b & (poly p x = 0)"
by (insert poly_IVT_pos [where p = "- p" ]) simp

lemma poly_MVT: "(a::real) < b ==>
     \<exists>x. a < x & x < b & (poly p b - poly p a = (b - a) * poly (pderiv p) x)"
using MVT [of a b "poly p"]
apply auto
apply (rule_tac x = z in exI)
apply (auto simp add: mult_left_cancel poly_DERIV [THEN DERIV_unique])
done

text{*Lemmas for Derivatives*}

lemma order_unique_lemma:
  fixes p :: "'a::idom poly"
  assumes "[:-a, 1:] ^ n dvd p" "\<not> [:-a, 1:] ^ Suc n dvd p"
  shows "n = order a p"
unfolding Polynomial.order_def
apply (rule Least_equality [symmetric])
apply (fact assms)
apply (rule classical)
apply (erule notE)
unfolding not_less_eq_eq
using assms(1) apply (rule power_le_dvd)
apply assumption
done

lemma lemma_order_pderiv1:
  "pderiv ([:- a, 1:] ^ Suc n * q) = [:- a, 1:] ^ Suc n * pderiv q +
    smult (of_nat (Suc n)) (q * [:- a, 1:] ^ n)"
apply (simp only: pderiv_mult pderiv_power_Suc)
apply (simp del: power_Suc of_nat_Suc add: pderiv_pCons)
done

lemma dvd_add_cancel1:
  fixes a b c :: "'a::comm_ring_1"
  shows "a dvd b + c \<Longrightarrow> a dvd b \<Longrightarrow> a dvd c"
  by (drule (1) Rings.dvd_diff, simp)

lemma lemma_order_pderiv:
  assumes n: "0 < n" 
      and pd: "pderiv p \<noteq> 0" 
      and pe: "p = [:- a, 1:] ^ n * q" 
      and nd: "~ [:- a, 1:] dvd q"
    shows "n = Suc (order a (pderiv p))"
using n 
proof -
  have "pderiv ([:- a, 1:] ^ n * q) \<noteq> 0"
    using assms by auto
  obtain n' where "n = Suc n'" "0 < Suc n'" "pderiv ([:- a, 1:] ^ Suc n' * q) \<noteq> 0"
    using assms by (cases n) auto
  then have *: "!!k l. k dvd k * pderiv q + smult (of_nat (Suc n')) l \<Longrightarrow> k dvd l"
    by (metis dvd_add_cancel1 dvd_smult_iff dvd_triv_left of_nat_eq_0_iff old.nat.distinct(2))
  have "n' = order a (pderiv ([:- a, 1:] ^ Suc n' * q))" 
  proof (rule order_unique_lemma)
    show "[:- a, 1:] ^ n' dvd pderiv ([:- a, 1:] ^ Suc n' * q)"
      apply (subst lemma_order_pderiv1)
      apply (rule dvd_add)
      apply (metis dvdI dvd_mult2 power_Suc2)
      apply (metis dvd_smult dvd_triv_right)
      done
  next
    show "\<not> [:- a, 1:] ^ Suc n' dvd pderiv ([:- a, 1:] ^ Suc n' * q)"
     apply (subst lemma_order_pderiv1)
     by (metis * nd dvd_mult_cancel_right field_power_not_zero pCons_eq_0_iff power_Suc zero_neq_one)
  qed
  then show ?thesis
    by (metis `n = Suc n'` pe)
qed

lemma order_decomp:
     "p \<noteq> 0
      ==> \<exists>q. p = [:-a, 1:] ^ (order a p) * q &
                ~([:-a, 1:] dvd q)"
apply (drule order [where a=a])
by (metis dvdE dvd_mult_cancel_left power_Suc2)

lemma order_pderiv: "[| pderiv p \<noteq> 0; order a p \<noteq> 0 |]
      ==> (order a p = Suc (order a (pderiv p)))"
apply (case_tac "p = 0", simp)
apply (drule_tac a = a and p = p in order_decomp)
using neq0_conv
apply (blast intro: lemma_order_pderiv)
done

lemma order_mult: "p * q \<noteq> 0 \<Longrightarrow> order a (p * q) = order a p + order a q"
proof -
  def i \<equiv> "order a p"
  def j \<equiv> "order a q"
  def t \<equiv> "[:-a, 1:]"
  have t_dvd_iff: "\<And>u. t dvd u \<longleftrightarrow> poly u a = 0"
    unfolding t_def by (simp add: dvd_iff_poly_eq_0)
  assume "p * q \<noteq> 0"
  then show "order a (p * q) = i + j"
    apply clarsimp
    apply (drule order [where a=a and p=p, folded i_def t_def])
    apply (drule order [where a=a and p=q, folded j_def t_def])
    apply clarify
    apply (erule dvdE)+
    apply (rule order_unique_lemma [symmetric], fold t_def)
    apply (simp_all add: power_add t_dvd_iff)
    done
qed

text{*Now justify the standard squarefree decomposition, i.e. f / gcd(f,f'). *}

lemma order_divides: "[:-a, 1:] ^ n dvd p \<longleftrightarrow> p = 0 \<or> n \<le> order a p"
apply (cases "p = 0", auto)
apply (drule order_2 [where a=a and p=p])
apply (metis not_less_eq_eq power_le_dvd)
apply (erule power_le_dvd [OF order_1])
done

lemma poly_squarefree_decomp_order:
  assumes "pderiv p \<noteq> 0"
  and p: "p = q * d"
  and p': "pderiv p = e * d"
  and d: "d = r * p + s * pderiv p"
  shows "order a q = (if order a p = 0 then 0 else 1)"
proof (rule classical)
  assume 1: "order a q \<noteq> (if order a p = 0 then 0 else 1)"
  from `pderiv p \<noteq> 0` have "p \<noteq> 0" by auto
  with p have "order a p = order a q + order a d"
    by (simp add: order_mult)
  with 1 have "order a p \<noteq> 0" by (auto split: if_splits)
  have "order a (pderiv p) = order a e + order a d"
    using `pderiv p \<noteq> 0` `pderiv p = e * d` by (simp add: order_mult)
  have "order a p = Suc (order a (pderiv p))"
    using `pderiv p \<noteq> 0` `order a p \<noteq> 0` by (rule order_pderiv)
  have "d \<noteq> 0" using `p \<noteq> 0` `p = q * d` by simp
  have "([:-a, 1:] ^ (order a (pderiv p))) dvd d"
    apply (simp add: d)
    apply (rule dvd_add)
    apply (rule dvd_mult)
    apply (simp add: order_divides `p \<noteq> 0`
           `order a p = Suc (order a (pderiv p))`)
    apply (rule dvd_mult)
    apply (simp add: order_divides)
    done
  then have "order a (pderiv p) \<le> order a d"
    using `d \<noteq> 0` by (simp add: order_divides)
  show ?thesis
    using `order a p = order a q + order a d`
    using `order a (pderiv p) = order a e + order a d`
    using `order a p = Suc (order a (pderiv p))`
    using `order a (pderiv p) \<le> order a d`
    by auto
qed

lemma poly_squarefree_decomp_order2: "[| pderiv p \<noteq> 0;
         p = q * d;
         pderiv p = e * d;
         d = r * p + s * pderiv p
      |] ==> \<forall>a. order a q = (if order a p = 0 then 0 else 1)"
by (blast intro: poly_squarefree_decomp_order)

lemma order_pderiv2: "[| pderiv p \<noteq> 0; order a p \<noteq> 0 |]
      ==> (order a (pderiv p) = n) = (order a p = Suc n)"
by (auto dest: order_pderiv)

definition
  rsquarefree :: "'a::idom poly => bool" where
  "rsquarefree p = (p \<noteq> 0 & (\<forall>a. (order a p = 0) | (order a p = 1)))"

lemma pderiv_iszero: "pderiv p = 0 \<Longrightarrow> \<exists>h. p = [:h:]"
apply (simp add: pderiv_eq_0_iff)
apply (case_tac p, auto split: if_splits)
done

lemma rsquarefree_roots:
  "rsquarefree p = (\<forall>a. ~(poly p a = 0 & poly (pderiv p) a = 0))"
apply (simp add: rsquarefree_def)
apply (case_tac "p = 0", simp, simp)
apply (case_tac "pderiv p = 0")
apply simp
apply (drule pderiv_iszero, clarsimp)
apply (metis coeff_0 coeff_pCons_0 degree_pCons_0 le0 le_antisym order_degree)
apply (force simp add: order_root order_pderiv2)
done

lemma poly_squarefree_decomp:
  assumes "pderiv p \<noteq> 0"
    and "p = q * d"
    and "pderiv p = e * d"
    and "d = r * p + s * pderiv p"
  shows "rsquarefree q & (\<forall>a. (poly q a = 0) = (poly p a = 0))"
proof -
  from `pderiv p \<noteq> 0` have "p \<noteq> 0" by auto
  with `p = q * d` have "q \<noteq> 0" by simp
  have "\<forall>a. order a q = (if order a p = 0 then 0 else 1)"
    using assms by (rule poly_squarefree_decomp_order2)
  with `p \<noteq> 0` `q \<noteq> 0` show ?thesis
    by (simp add: rsquarefree_def order_root)
qed

end
