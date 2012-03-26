(*  Title:      HOL/Library/Poly_Deriv.thy
    Author:     Amine Chaieb
    Author:     Brian Huffman
*)

header{* Polynomials and Differentiation *}

theory Poly_Deriv
imports Deriv Polynomial
begin

subsection {* Derivatives of univariate polynomials *}

definition
  pderiv :: "'a::real_normed_field poly \<Rightarrow> 'a poly" where
  "pderiv = poly_rec 0 (\<lambda>a p p'. p + pCons 0 p')"

lemma pderiv_0 [simp]: "pderiv 0 = 0"
  unfolding pderiv_def by (simp add: poly_rec_0)

lemma pderiv_pCons: "pderiv (pCons a p) = p + pCons 0 (pderiv p)"
  unfolding pderiv_def by (simp add: poly_rec_pCons)

lemma coeff_pderiv: "coeff (pderiv p) n = of_nat (Suc n) * coeff p (Suc n)"
  apply (induct p arbitrary: n, simp)
  apply (simp add: pderiv_pCons coeff_pCons algebra_simps split: nat.split)
  done

lemma pderiv_eq_0_iff: "pderiv p = 0 \<longleftrightarrow> degree p = 0"
  apply (rule iffI)
  apply (cases p, simp)
  apply (simp add: expand_poly_eq coeff_pderiv del: of_nat_Suc)
  apply (simp add: expand_poly_eq coeff_pderiv coeff_eq_0)
  done

lemma degree_pderiv: "degree (pderiv p) = degree p - 1"
  apply (rule order_antisym [OF degree_le])
  apply (simp add: coeff_pderiv coeff_eq_0)
  apply (cases "degree p", simp)
  apply (rule le_degree)
  apply (simp add: coeff_pderiv del: of_nat_Suc)
  apply (rule subst, assumption)
  apply (rule leading_coeff_neq_0, clarsimp)
  done

lemma pderiv_singleton [simp]: "pderiv [:a:] = 0"
by (simp add: pderiv_pCons)

lemma pderiv_add: "pderiv (p + q) = pderiv p + pderiv q"
by (rule poly_ext, simp add: coeff_pderiv algebra_simps)

lemma pderiv_minus: "pderiv (- p) = - pderiv p"
by (rule poly_ext, simp add: coeff_pderiv)

lemma pderiv_diff: "pderiv (p - q) = pderiv p - pderiv q"
by (rule poly_ext, simp add: coeff_pderiv algebra_simps)

lemma pderiv_smult: "pderiv (smult a p) = smult a (pderiv p)"
by (rule poly_ext, simp add: coeff_pderiv algebra_simps)

lemma pderiv_mult: "pderiv (p * q) = p * pderiv q + q * pderiv p"
apply (induct p)
apply simp
apply (simp add: pderiv_add pderiv_smult pderiv_pCons algebra_simps)
done

lemma pderiv_power_Suc:
  "pderiv (p ^ Suc n) = smult (of_nat (Suc n)) (p ^ n) * pderiv p"
apply (induct n)
apply simp
apply (subst power_Suc)
apply (subst pderiv_mult)
apply (erule ssubst)
apply (simp only: of_nat_Suc smult_add_left smult_1_left)
apply (simp add: algebra_simps) (* FIXME *)
done

lemma DERIV_cmult2: "DERIV f x :> D ==> DERIV (%x. (f x) * c :: real) x :> D * c"
by (simp add: DERIV_cmult mult_commute [of _ c])

lemma DERIV_pow2: "DERIV (%x. x ^ Suc n) x :> real (Suc n) * (x ^ n)"
by (rule DERIV_cong, rule DERIV_pow, simp)
declare DERIV_pow2 [simp] DERIV_pow [simp]

lemma DERIV_add_const: "DERIV f x :> D ==>  DERIV (%x. a + f x :: 'a::real_normed_field) x :> D"
by (rule DERIV_cong, rule DERIV_add, auto)

lemma poly_DERIV[simp]: "DERIV (%x. poly p x) x :> poly (pderiv p) x"
  by (induct p, auto intro!: DERIV_intros simp add: pderiv_pCons)

text{* Consequences of the derivative theorem above*}

lemma poly_differentiable[simp]: "(%x. poly p x) differentiable (x::real)"
apply (simp add: differentiable_def)
apply (blast intro: poly_DERIV)
done

lemma poly_isCont[simp]: "isCont (%x. poly p x) (x::real)"
by (rule poly_DERIV [THEN DERIV_isCont])

lemma poly_IVT_pos: "[| a < b; poly p (a::real) < 0; 0 < poly p b |]
      ==> \<exists>x. a < x & x < b & (poly p x = 0)"
apply (cut_tac f = "%x. poly p x" and a = a and b = b and y = 0 in IVT_objl)
apply (auto simp add: order_le_less)
done

lemma poly_IVT_neg: "[| (a::real) < b; 0 < poly p a; poly p b < 0 |]
      ==> \<exists>x. a < x & x < b & (poly p x = 0)"
by (insert poly_IVT_pos [where p = "- p" ]) simp

lemma poly_MVT: "(a::real) < b ==>
     \<exists>x. a < x & x < b & (poly p b - poly p a = (b - a) * poly (pderiv p) x)"
apply (drule_tac f = "poly p" in MVT, auto)
apply (rule_tac x = z in exI)
apply (auto simp add: real_mult_left_cancel poly_DERIV [THEN DERIV_unique])
done

text{*Lemmas for Derivatives*}

lemma order_unique_lemma:
  fixes p :: "'a::idom poly"
  assumes "[:-a, 1:] ^ n dvd p \<and> \<not> [:-a, 1:] ^ Suc n dvd p"
  shows "n = order a p"
unfolding Polynomial.order_def
apply (rule Least_equality [symmetric])
apply (rule assms [THEN conjunct2])
apply (erule contrapos_np)
apply (rule power_le_dvd)
apply (rule assms [THEN conjunct1])
apply simp
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

lemma lemma_order_pderiv [rule_format]:
     "\<forall>p q a. 0 < n &
       pderiv p \<noteq> 0 &
       p = [:- a, 1:] ^ n * q & ~ [:- a, 1:] dvd q
       --> n = Suc (order a (pderiv p))"
 apply (cases "n", safe, rename_tac n p q a)
 apply (rule order_unique_lemma)
 apply (rule conjI)
  apply (subst lemma_order_pderiv1)
  apply (rule dvd_add)
   apply (rule dvd_mult2)
   apply (rule le_imp_power_dvd, simp)
  apply (rule dvd_smult)
  apply (rule dvd_mult)
  apply (rule dvd_refl)
 apply (subst lemma_order_pderiv1)
 apply (erule contrapos_nn) back
 apply (subgoal_tac "[:- a, 1:] ^ Suc n dvd q * [:- a, 1:] ^ n")
  apply (simp del: mult_pCons_left)
 apply (drule dvd_add_cancel1)
  apply (simp del: mult_pCons_left)
 apply (drule dvd_smult_cancel, simp del: of_nat_Suc)
 apply assumption
done

lemma order_decomp:
     "p \<noteq> 0
      ==> \<exists>q. p = [:-a, 1:] ^ (order a p) * q &
                ~([:-a, 1:] dvd q)"
apply (drule order [where a=a])
apply (erule conjE)
apply (erule dvdE)
apply (rule exI)
apply (rule conjI, assumption)
apply (erule contrapos_nn)
apply (erule ssubst) back
apply (subst power_Suc2)
apply (erule mult_dvd_mono [OF dvd_refl])
done

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
    apply (rule order_unique_lemma [symmetric], fold t_def)
    apply (erule dvdE)+
    apply (simp add: power_add t_dvd_iff)
    done
qed

text{*Now justify the standard squarefree decomposition, i.e. f / gcd(f,f'). *}

lemma order_divides: "[:-a, 1:] ^ n dvd p \<longleftrightarrow> p = 0 \<or> n \<le> order a p"
apply (cases "p = 0", auto)
apply (drule order_2 [where a=a and p=p])
apply (erule contrapos_np)
apply (erule power_le_dvd)
apply simp
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
apply (blast intro: poly_squarefree_decomp_order)
done

lemma order_pderiv2: "[| pderiv p \<noteq> 0; order a p \<noteq> 0 |]
      ==> (order a (pderiv p) = n) = (order a p = Suc n)"
apply (auto dest: order_pderiv)
done

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
apply (drule pderiv_iszero, clarify)
apply simp
apply (rule allI)
apply (cut_tac p = "[:h:]" and a = a in order_root)
apply simp
apply (auto simp add: order_root order_pderiv2)
apply (erule_tac x="a" in allE, simp)
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
