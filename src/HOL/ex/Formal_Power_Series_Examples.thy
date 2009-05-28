(*  Title:      Formal_Power_Series_Examples.thy
    ID:         
    Author:     Amine Chaieb, University of Cambridge
*)

header{* Some applications of formal power series and some properties over complex numbers*}

theory Formal_Power_Series_Examples
  imports Formal_Power_Series Binomial Complex
begin

section{* The generalized binomial theorem *}
lemma gbinomial_theorem: 
  "((a::'a::{field_char_0, division_by_zero})+b) ^ n = (\<Sum>k=0..n. of_nat (n choose k) * a^k * b^(n-k))"
proof-
  from E_add_mult[of a b] 
  have "(E (a + b)) $ n = (E a * E b)$n" by simp
  then have "(a + b) ^ n = (\<Sum>i\<Colon>nat = 0\<Colon>nat..n. a ^ i * b ^ (n - i)  * (of_nat (fact n) / of_nat (fact i * fact (n - i))))"
    by (simp add: field_simps fps_mult_nth of_nat_mult[symmetric] setsum_right_distrib)
  then show ?thesis 
    apply simp
    apply (rule setsum_cong2)
    apply simp
    apply (frule binomial_fact[where ?'a = 'a, symmetric])
    by (simp add: field_simps of_nat_mult)
qed

text{* And the nat-form -- also available from Binomial.thy *}
lemma binomial_theorem: "(a+b) ^ n = (\<Sum>k=0..n. (n choose k) * a^k * b^(n-k))"
  using gbinomial_theorem[of "of_nat a" "of_nat b" n]
  unfolding of_nat_add[symmetric] of_nat_power[symmetric] of_nat_mult[symmetric] of_nat_setsum[symmetric]
  by simp

section {* The binomial series and Vandermonde's identity *}
definition "fps_binomial a = Abs_fps (\<lambda>n. a gchoose n)"

lemma fps_binomial_nth[simp]: "fps_binomial a $ n = a gchoose n"
  by (simp add: fps_binomial_def)

lemma fps_binomial_ODE_unique:
  fixes c :: "'a::field_char_0"
  shows "fps_deriv a = (fps_const c * a) / (1 + X) \<longleftrightarrow> a = fps_const (a$0) * fps_binomial c"
  (is "?lhs \<longleftrightarrow> ?rhs")
proof-
  let ?da = "fps_deriv a"
  let ?x1 = "(1 + X):: 'a fps"
  let ?l = "?x1 * ?da"
  let ?r = "fps_const c * a"
  have x10: "?x1 $ 0 \<noteq> 0" by simp
  have "?l = ?r \<longleftrightarrow> inverse ?x1 * ?l = inverse ?x1 * ?r" by simp
  also have "\<dots> \<longleftrightarrow> ?da = (fps_const c * a) / ?x1"
    apply (simp only: fps_divide_def  mult_assoc[symmetric] inverse_mult_eq_1[OF x10])
    by (simp add: ring_simps)
  finally have eq: "?l = ?r \<longleftrightarrow> ?lhs" by simp
  moreover
  {assume h: "?l = ?r" 
    {fix n
      from h have lrn: "?l $ n = ?r$n" by simp
      
      from lrn 
      have "a$ Suc n = ((c - of_nat n) / of_nat (Suc n)) * a $n" 
	apply (simp add: ring_simps del: of_nat_Suc)
	by (cases n, simp_all add: field_simps del: of_nat_Suc)
    }
    note th0 = this
    {fix n have "a$n = (c gchoose n) * a$0"
      proof(induct n)
	case 0 thus ?case by simp
      next
	case (Suc m)
	thus ?case unfolding th0
	  apply (simp add: field_simps del: of_nat_Suc)
	  unfolding mult_assoc[symmetric] gbinomial_mult_1
	  by (simp add: ring_simps)
      qed}
    note th1 = this
    have ?rhs
      apply (simp add: fps_eq_iff)
      apply (subst th1)
      by (simp add: ring_simps)}
  moreover
  {assume h: ?rhs
  have th00:"\<And>x y. x * (a$0 * y) = a$0 * (x*y)" by (simp add: mult_commute)
    have "?l = ?r" 
      apply (subst h)
      apply (subst (2) h)
      apply (clarsimp simp add: fps_eq_iff ring_simps)
      unfolding mult_assoc[symmetric] th00 gbinomial_mult_1
      by (simp add: ring_simps gbinomial_mult_1)}
  ultimately show ?thesis by blast
qed

lemma fps_binomial_deriv: "fps_deriv (fps_binomial c) = fps_const c * fps_binomial c / (1 + X)"
proof-
  let ?a = "fps_binomial c"
  have th0: "?a = fps_const (?a$0) * ?a" by (simp)
  from iffD2[OF fps_binomial_ODE_unique, OF th0] show ?thesis .
qed

lemma fps_binomial_add_mult: "fps_binomial (c+d) = fps_binomial c * fps_binomial d" (is "?l = ?r")
proof-
  let ?P = "?r - ?l"
  let ?b = "fps_binomial"
  let ?db = "\<lambda>x. fps_deriv (?b x)"
  have "fps_deriv ?P = ?db c * ?b d + ?b c * ?db d - ?db (c + d)"  by simp
  also have "\<dots> = inverse (1 + X) * (fps_const c * ?b c * ?b d + fps_const d * ?b c * ?b d - fps_const (c+d) * ?b (c + d))"
    unfolding fps_binomial_deriv
    by (simp add: fps_divide_def ring_simps)
  also have "\<dots> = (fps_const (c + d)/ (1 + X)) * ?P"
    by (simp add: ring_simps fps_divide_def fps_const_add[symmetric] del: fps_const_add)
  finally have th0: "fps_deriv ?P = fps_const (c+d) * ?P / (1 + X)"
    by (simp add: fps_divide_def)
  have "?P = fps_const (?P$0) * ?b (c + d)"
    unfolding fps_binomial_ODE_unique[symmetric]
    using th0 by simp
  hence "?P = 0" by (simp add: fps_mult_nth)
  then show ?thesis by simp
qed

lemma fps_minomial_minus_one: "fps_binomial (- 1) = inverse (1 + X)"
  (is "?l = inverse ?r")
proof-
  have th: "?r$0 \<noteq> 0" by simp
  have th': "fps_deriv (inverse ?r) = fps_const (- 1) * inverse ?r / (1 + X)"
    by (simp add: fps_inverse_deriv[OF th] fps_divide_def power2_eq_square mult_commute fps_const_neg[symmetric] del: fps_const_neg)
  have eq: "inverse ?r $ 0 = 1"
    by (simp add: fps_inverse_def)
  from iffD1[OF fps_binomial_ODE_unique[of "inverse (1 + X)" "- 1"] th'] eq
  show ?thesis by (simp add: fps_inverse_def)
qed

lemma gbinomial_Vandermond: "setsum (\<lambda>k. (a gchoose k) * (b gchoose (n - k))) {0..n} = (a + b) gchoose n"
proof-
  let ?ba = "fps_binomial a"
  let ?bb = "fps_binomial b"
  let ?bab = "fps_binomial (a + b)"
  from fps_binomial_add_mult[of a b] have "?bab $ n = (?ba * ?bb)$n" by simp
  then show ?thesis by (simp add: fps_mult_nth)
qed

lemma binomial_Vandermond: "setsum (\<lambda>k. (a choose k) * (b choose (n - k))) {0..n} = (a + b) choose n"
  using gbinomial_Vandermond[of "(of_nat a)" "of_nat b" n]
  
  apply (simp only: binomial_gbinomial[symmetric] of_nat_mult[symmetric] of_nat_setsum[symmetric] of_nat_add[symmetric])
  by simp

lemma binomial_symmetric: assumes kn: "k \<le> n" 
  shows "n choose k = n choose (n - k)"
proof-
  from kn have kn': "n - k \<le> n" by arith
  from binomial_fact_lemma[OF kn] binomial_fact_lemma[OF kn']
  have "fact k * fact (n - k) * (n choose k) = fact (n - k) * fact (n - (n - k)) * (n choose (n - k))" by simp
  then show ?thesis using kn by simp
qed
  
lemma binomial_Vandermond_same: "setsum (\<lambda>k. (n choose k)^2) {0..n} = (2*n) choose n"
  using binomial_Vandermond[of n n n,symmetric]
  unfolding nat_mult_2 apply (simp add: power2_eq_square)
  apply (rule setsum_cong2)
  by (auto intro:  binomial_symmetric)

section {* Relation between formal sine/cosine and the exponential FPS*}
lemma Eii_sin_cos:
  "E (ii * c) = fps_cos c + fps_const ii * fps_sin c "
  (is "?l = ?r")
proof-
  {fix n::nat
    {assume en: "even n"
      from en obtain m where m: "n = 2*m" 
	unfolding even_mult_two_ex by blast
      
      have "?l $n = ?r$n" 
	by (simp add: m fps_sin_def fps_cos_def power_mult_distrib
	  power_mult power_minus)}
    moreover
    {assume on: "odd n"
      from on obtain m where m: "n = 2*m + 1" 
	unfolding odd_nat_equiv_def2 by (auto simp add: nat_mult_2)  
      have "?l $n = ?r$n" 
	by (simp add: m fps_sin_def fps_cos_def power_mult_distrib
	  power_mult power_minus)}
    ultimately have "?l $n = ?r$n"  by blast}
  then show ?thesis by (simp add: fps_eq_iff)
qed

lemma fps_sin_neg[simp]: "fps_sin (- c) = - fps_sin c"
by (simp add: fps_eq_iff fps_sin_def)

lemma fps_cos_neg[simp]: "fps_cos (- c) = fps_cos c"
  by (simp add: fps_eq_iff fps_cos_def)
lemma E_minus_ii_sin_cos: "E (- (ii * c)) = fps_cos c - fps_const ii * fps_sin c "
  unfolding minus_mult_right Eii_sin_cos by simp

lemma fps_const_minus: "fps_const (c::'a::group_add) - fps_const d = fps_const (c - d)  "by (simp add: fps_eq_iff fps_const_def)

lemma fps_number_of_fps_const: "number_of i = fps_const (number_of i :: 'a:: {comm_ring_1, number_ring})"
  apply (subst (2) number_of_eq)
apply(rule int_induct[of _ 0])
apply (simp_all add: number_of_fps_def)
by (simp_all add: fps_const_add[symmetric] fps_const_minus[symmetric])

lemma fps_cos_Eii:
  "fps_cos c = (E (ii * c) + E (- ii * c)) / fps_const 2"
proof-
  have th: "fps_cos c + fps_cos c = fps_cos c * fps_const 2" 
    by (simp add: fps_eq_iff fps_number_of_fps_const complex_number_of_def[symmetric])
  show ?thesis
  unfolding Eii_sin_cos minus_mult_commute
  by (simp add: fps_number_of_fps_const fps_divide_def fps_const_inverse th complex_number_of_def[symmetric])
qed

lemma fps_sin_Eii:
  "fps_sin c = (E (ii * c) - E (- ii * c)) / fps_const (2*ii)"
proof-
  have th: "fps_const \<i> * fps_sin c + fps_const \<i> * fps_sin c = fps_sin c * fps_const (2 * ii)" 
    by (simp add: fps_eq_iff fps_number_of_fps_const complex_number_of_def[symmetric])
  show ?thesis
  unfolding Eii_sin_cos minus_mult_commute
  by (simp add: fps_divide_def fps_const_inverse th)
qed

lemma fps_const_mult_2: "fps_const (2::'a::number_ring) * a = a +a"
  by (simp add: fps_eq_iff fps_number_of_fps_const)

lemma fps_const_mult_2_right: "a * fps_const (2::'a::number_ring) = a +a"
  by (simp add: fps_eq_iff fps_number_of_fps_const)

lemma fps_tan_Eii:
  "fps_tan c = (E (ii * c) - E (- ii * c)) / (fps_const ii * (E (ii * c) + E (- ii * c)))"
  unfolding fps_tan_def fps_sin_Eii fps_cos_Eii mult_minus_left E_neg
  apply (simp add: fps_divide_def fps_inverse_mult fps_const_mult[symmetric] fps_const_inverse del: fps_const_mult)
  by simp

lemma fps_demoivre: "(fps_cos a + fps_const ii * fps_sin a)^n = fps_cos (of_nat n * a) + fps_const ii * fps_sin (of_nat n * a)"
  unfolding Eii_sin_cos[symmetric] E_power_mult
  by (simp add: mult_ac)

text{* Now some trigonometric identities *}
lemma fps_sin_add: 
  "fps_sin (a+b) = fps_sin (a::complex) * fps_cos b + fps_cos a * fps_sin b"
proof-
  let ?ca = "fps_cos a"
  let ?cb = "fps_cos b"
  let ?sa = "fps_sin a"
  let ?sb = "fps_sin b"
  let ?i = "fps_const ii"
  have i: "?i*?i = fps_const -1" by simp
  have "fps_sin (a + b) = 
    ((?ca + ?i * ?sa) * (?cb + ?i*?sb) - (?ca - ?i*?sa) * (?cb - ?i*?sb)) *
    fps_const (- (\<i> / 2))"
    apply(simp add: fps_sin_Eii[of "a+b"] fps_divide_def minus_mult_commute)
    unfolding right_distrib
    apply (simp add: Eii_sin_cos E_minus_ii_sin_cos fps_const_inverse E_add_mult)
    by (simp add: ring_simps)
  also have "\<dots> = (?ca * ?cb + ?i*?ca * ?sb + ?i * ?sa * ?cb + (?i*?i)*?sa*?sb - ?ca*?cb + ?i*?ca * ?sb + ?i*?sa*?cb - (?i*?i)*?sa * ?sb) * fps_const (- ii/2)"
    by (simp add: ring_simps)
  also have "\<dots> = (fps_const 2 * ?i * (?ca * ?sb + ?sa * ?cb)) * fps_const (- ii/2)"
    apply simp
  apply (simp add: ring_simps)
    apply (simp add:  ring_simps add: fps_const_mult[symmetric] del:fps_const_mult)
    unfolding fps_const_mult_2_right
    by (simp add: ring_simps)
  also have "\<dots> = (fps_const 2 * ?i * fps_const (- ii/2)) * (?ca * ?sb + ?sa * ?cb)"
    by (simp only: mult_ac)
  also have "\<dots> = ?sa * ?cb + ?ca*?sb"
    by simp
  finally show ?thesis .
qed

lemma fps_cos_add: 
  "fps_cos (a+b) = fps_cos (a::complex) * fps_cos b - fps_sin a * fps_sin b"
proof-
  let ?ca = "fps_cos a"
  let ?cb = "fps_cos b"
  let ?sa = "fps_sin a"
  let ?sb = "fps_sin b"
  let ?i = "fps_const ii"
  have i: "?i*?i = fps_const -1" by simp
  have i': "\<And>x. ?i * (?i * x) = - x" 
    apply (simp add: mult_assoc[symmetric] i)
    by (simp add: fps_eq_iff)
  have m1: "\<And>x. x * fps_const (-1 ::complex) = - x" "\<And>x. fps_const (-1 :: complex) * x = - x"
    by (auto simp add: fps_eq_iff)

  have "fps_cos (a + b) = 
    ((?ca + ?i * ?sa) * (?cb + ?i*?sb) + (?ca - ?i*?sa) * (?cb - ?i*?sb)) *
    fps_const (1/ 2)"
    apply(simp add: fps_cos_Eii[of "a+b"] fps_divide_def minus_mult_commute)
    unfolding right_distrib minus_add_distrib
    apply (simp add: Eii_sin_cos E_minus_ii_sin_cos fps_const_inverse E_add_mult)
    by (simp add: ring_simps)
  also have "\<dots> = (?ca * ?cb + ?i*?ca * ?sb + ?i * ?sa * ?cb + (?i*?i)*?sa*?sb + ?ca*?cb - ?i*?ca * ?sb - ?i*?sa*?cb + (?i*?i)*?sa * ?sb) * fps_const (1/2)"
    apply simp
    by (simp add: ring_simps i' m1)
  also have "\<dots> = (fps_const 2 * (?ca * ?cb - ?sa * ?sb)) * fps_const (1/2)"
    apply simp
    by (simp add: ring_simps m1 fps_const_mult_2_right)
  also have "\<dots> = (fps_const 2 * fps_const (1/2)) * (?ca * ?cb - ?sa * ?sb)"
    by (simp only: mult_ac)
  also have "\<dots> = ?ca * ?cb - ?sa*?sb"
    by simp
  finally show ?thesis .
qed

end
