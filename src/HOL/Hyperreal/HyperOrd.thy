(*  Title:	 Real/Hyperreal/HyperOrd.thy
    Author:      Jacques D. Fleuriot
    Copyright:   2000 University of Edinburgh
    Description: Type "hypreal" is a linear order and also 
                 satisfies plus_ac0: + is an AC-operator with zero
*)

theory HyperOrd = HyperDef:

ML
{*
val left_distrib = thm"left_distrib";
*}

(*** Monotonicity results ***)

lemma hypreal_add_less_le_mono: "[|(i::hypreal)<j;  k\<le>l |] ==> i + k < j + l"
by (auto dest!: order_le_imp_less_or_eq intro: hypreal_add_less_mono1 add_strict_mono)

lemma hypreal_add_less_mono2: "!!(A::hypreal). A < B ==> C + A < C + B"
by (auto intro: hypreal_add_less_mono1 simp add: hypreal_add_commute)

lemma hypreal_add_le_less_mono: "[|(i::hypreal)\<le>j;  k<l |] ==> i + k < j + l"
apply (erule add_right_mono [THEN order_le_less_trans])
apply (erule add_strict_left_mono) 
done

lemma hypreal_add_zero_less_le_mono: "[|r < x; (0::hypreal) \<le> y|] ==> r < x + y"
by (auto dest: hypreal_add_less_le_mono)

lemma hypreal_add_order: "[| 0 < x; 0 < y |] ==> (0::hypreal) < x + y"
apply (erule order_less_trans)
apply (drule hypreal_add_less_mono2, simp)
done

lemma hypreal_le_add_order: "[| 0 \<le> x; 0 \<le> y |] ==> (0::hypreal) \<le> x + y"
apply (drule order_le_imp_less_or_eq)+
apply (auto intro: hypreal_add_order order_less_imp_le)
done

text{*The precondition could be weakened to @{term "0\<le>x"}*}
lemma hypreal_mult_less_mono:
     "[| u<v;  x<y;  (0::hypreal) < v;  0 < x |] ==> u*x < v* y"
 by (simp add: Ring_and_Field.mult_strict_mono order_less_imp_le)


subsection{*Existence of Infinite Hyperreal Number*}

lemma Rep_hypreal_omega: "Rep_hypreal(omega) \<in> hypreal"
apply (unfold omega_def)
apply (rule Rep_hypreal)
done

text{*Existence of infinite number not corresponding to any real number.
Use assumption that member @{term FreeUltrafilterNat} is not finite.*}


text{*A few lemmas first*}

lemma lemma_omega_empty_singleton_disj: "{n::nat. x = real n} = {} |  
      (\<exists>y. {n::nat. x = real n} = {y})"
by (force dest: inj_real_of_nat [THEN injD])

lemma lemma_finite_omega_set: "finite {n::nat. x = real n}"
by (cut_tac x = x in lemma_omega_empty_singleton_disj, auto)

lemma not_ex_hypreal_of_real_eq_omega: 
      "~ (\<exists>x. hypreal_of_real x = omega)"
apply (unfold omega_def hypreal_of_real_def)
apply (auto simp add: real_of_nat_Suc diff_eq_eq [symmetric] 
            lemma_finite_omega_set [THEN FreeUltrafilterNat_finite])
done

lemma hypreal_of_real_not_eq_omega: "hypreal_of_real x \<noteq> omega"
by (cut_tac not_ex_hypreal_of_real_eq_omega, auto)

text{*Existence of infinitesimal number also not corresponding to any
 real number*}

lemma lemma_epsilon_empty_singleton_disj:
     "{n::nat. x = inverse(real(Suc n))} = {} |  
      (\<exists>y. {n::nat. x = inverse(real(Suc n))} = {y})"
apply (auto simp add: inj_real_of_nat [THEN inj_eq])
done

lemma lemma_finite_epsilon_set: "finite {n. x = inverse(real(Suc n))}"
by (cut_tac x = x in lemma_epsilon_empty_singleton_disj, auto)

lemma not_ex_hypreal_of_real_eq_epsilon: 
      "~ (\<exists>x. hypreal_of_real x = epsilon)"
apply (unfold epsilon_def hypreal_of_real_def)
apply (auto simp add: lemma_finite_epsilon_set [THEN FreeUltrafilterNat_finite])
done

lemma hypreal_of_real_not_eq_epsilon: "hypreal_of_real x \<noteq> epsilon"
by (cut_tac not_ex_hypreal_of_real_eq_epsilon, auto)

lemma hypreal_epsilon_not_zero: "epsilon \<noteq> 0"
by (unfold epsilon_def hypreal_zero_def, auto)

lemma hypreal_epsilon_inverse_omega: "epsilon = inverse(omega)"
by (simp add: hypreal_inverse omega_def epsilon_def)


ML
{*
val hypreal_add_less_mono1 = thm"hypreal_add_less_mono1";
val hypreal_mult_order = thm"hypreal_mult_order";
val hypreal_le_add_order = thm"hypreal_le_add_order";
val hypreal_add_left_le_mono1 = thm"hypreal_add_left_le_mono1";
val hypreal_add_less_le_mono = thm"hypreal_add_less_le_mono";
val hypreal_add_le_less_mono = thm"hypreal_add_le_less_mono";
val hypreal_add_zero_less_le_mono = thm"hypreal_add_zero_less_le_mono";
val hypreal_mult_less_mono1 = thm"hypreal_mult_less_mono1";
val hypreal_mult_less_mono2 = thm"hypreal_mult_less_mono2";
val hypreal_mult_less_mono = thm"hypreal_mult_less_mono";
val Rep_hypreal_omega = thm"Rep_hypreal_omega";
val lemma_omega_empty_singleton_disj = thm"lemma_omega_empty_singleton_disj";
val lemma_finite_omega_set = thm"lemma_finite_omega_set";
val not_ex_hypreal_of_real_eq_omega = thm"not_ex_hypreal_of_real_eq_omega";
val hypreal_of_real_not_eq_omega = thm"hypreal_of_real_not_eq_omega";
val not_ex_hypreal_of_real_eq_epsilon = thm"not_ex_hypreal_of_real_eq_epsilon";
val hypreal_of_real_not_eq_epsilon = thm"hypreal_of_real_not_eq_epsilon";
val hypreal_epsilon_not_zero = thm"hypreal_epsilon_not_zero";
val hypreal_epsilon_inverse_omega = thm"hypreal_epsilon_inverse_omega";
*}

end
