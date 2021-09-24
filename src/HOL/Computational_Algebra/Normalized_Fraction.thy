(*  Title:      HOL/Computational_Algebra/Normalized_Fraction.thy
    Author:     Manuel Eberl
*)

theory Normalized_Fraction
imports 
  Main 
  Euclidean_Algorithm
  Fraction_Field
begin

definition quot_to_fract :: "'a :: {idom} \<times> 'a \<Rightarrow> 'a fract" where
  "quot_to_fract = (\<lambda>(a,b). Fraction_Field.Fract a b)"

definition normalize_quot :: "'a :: {ring_gcd,idom_divide,semiring_gcd_mult_normalize} \<times> 'a \<Rightarrow> 'a \<times> 'a" where
  "normalize_quot = 
     (\<lambda>(a,b). if b = 0 then (0,1) else let d = gcd a b * unit_factor b in (a div d, b div d))" 

lemma normalize_quot_zero [simp]:
  "normalize_quot (a, 0) = (0, 1)"
  by (simp add: normalize_quot_def)

lemma normalize_quot_proj:
  "fst (normalize_quot (a, b)) = a div (gcd a b * unit_factor b)"
  "snd (normalize_quot (a, b)) = normalize b div gcd a b" if "b \<noteq> 0"
  using that by (simp_all add: normalize_quot_def Let_def mult.commute [of _ "unit_factor b"] dvd_div_mult2_eq mult_unit_dvd_iff')

definition normalized_fracts :: "('a :: {ring_gcd,idom_divide} \<times> 'a) set" where
  "normalized_fracts = {(a,b). coprime a b \<and> unit_factor b = 1}"
  
lemma not_normalized_fracts_0_denom [simp]: "(a, 0) \<notin> normalized_fracts"
  by (auto simp: normalized_fracts_def)

lemma unit_factor_snd_normalize_quot [simp]:
  "unit_factor (snd (normalize_quot x)) = 1"
  by (simp add: normalize_quot_def case_prod_unfold Let_def dvd_unit_factor_div
                mult_unit_dvd_iff unit_factor_mult unit_factor_gcd)
  
lemma snd_normalize_quot_nonzero [simp]: "snd (normalize_quot x) \<noteq> 0"
  using unit_factor_snd_normalize_quot[of x] 
  by (auto simp del: unit_factor_snd_normalize_quot)
  
lemma normalize_quot_aux:
  fixes a b
  assumes "b \<noteq> 0"
  defines "d \<equiv> gcd a b * unit_factor b"
  shows   "a = fst (normalize_quot (a,b)) * d" "b = snd (normalize_quot (a,b)) * d"
          "d dvd a" "d dvd b" "d \<noteq> 0"
proof -
  from assms show "d dvd a" "d dvd b"
    by (simp_all add: d_def mult_unit_dvd_iff)
  thus "a = fst (normalize_quot (a,b)) * d" "b = snd (normalize_quot (a,b)) * d" "d \<noteq> 0"
    by (auto simp: normalize_quot_def Let_def d_def \<open>b \<noteq> 0\<close>)
qed

lemma normalize_quotE:
  assumes "b \<noteq> 0"
  obtains d where "a = fst (normalize_quot (a,b)) * d" "b = snd (normalize_quot (a,b)) * d"
                  "d dvd a" "d dvd b" "d \<noteq> 0"
  using that[OF normalize_quot_aux[OF assms]] .
  
lemma normalize_quotE':
  assumes "snd x \<noteq> 0"
  obtains d where "fst x = fst (normalize_quot x) * d" "snd x = snd (normalize_quot x) * d"
                  "d dvd fst x" "d dvd snd x" "d \<noteq> 0"
proof -
  from normalize_quotE[OF assms, of "fst x"] obtain d where
    "fst x = fst (normalize_quot (fst x, snd x)) * d"
    "snd x = snd (normalize_quot (fst x, snd x)) * d"
    "d dvd fst x"
    "d dvd snd x"
    "d \<noteq> 0" .
  then show ?thesis unfolding prod.collapse by (intro that[of d])
qed
  
lemma coprime_normalize_quot:
  "coprime (fst (normalize_quot x)) (snd (normalize_quot x))"
  by (simp add: normalize_quot_def case_prod_unfold div_mult_unit2)
    (metis coprime_mult_self_right_iff div_gcd_coprime unit_div_mult_self unit_factor_is_unit)

lemma normalize_quot_in_normalized_fracts [simp]: "normalize_quot x \<in> normalized_fracts"
  by (simp add: normalized_fracts_def coprime_normalize_quot case_prod_unfold)

lemma normalize_quot_eq_iff:
  assumes "b \<noteq> 0" "d \<noteq> 0"
  shows   "normalize_quot (a,b) = normalize_quot (c,d) \<longleftrightarrow> a * d = b * c"
proof -
  define x y where "x = normalize_quot (a,b)" and "y = normalize_quot (c,d)" 
  from normalize_quotE[OF assms(1), of a] normalize_quotE[OF assms(2), of c]
    obtain d1 d2 
      where "a = fst x * d1" "b = snd x * d1" "c = fst y * d2" "d = snd y * d2" "d1 \<noteq> 0" "d2 \<noteq> 0"
    unfolding x_def y_def by metis
  hence "a * d = b * c \<longleftrightarrow> fst x * snd y = snd x * fst y" by simp
  also have "\<dots> \<longleftrightarrow> fst x = fst y \<and> snd x = snd y"
    by (intro coprime_crossproduct') (simp_all add: x_def y_def coprime_normalize_quot)
  also have "\<dots> \<longleftrightarrow> x = y" using prod_eqI by blast
  finally show "x = y \<longleftrightarrow> a * d = b * c" ..
qed

lemma normalize_quot_eq_iff':
  assumes "snd x \<noteq> 0" "snd y \<noteq> 0"
  shows   "normalize_quot x = normalize_quot y \<longleftrightarrow> fst x * snd y = snd x * fst y"
  using assms by (cases x, cases y, hypsubst) (subst normalize_quot_eq_iff, simp_all)

lemma normalize_quot_id: "x \<in> normalized_fracts \<Longrightarrow> normalize_quot x = x"
  by (auto simp: normalized_fracts_def normalize_quot_def case_prod_unfold)

lemma normalize_quot_idem [simp]: "normalize_quot (normalize_quot x) = normalize_quot x"
  by (rule normalize_quot_id) simp_all

lemma fractrel_iff_normalize_quot_eq:
  "fractrel x y \<longleftrightarrow> normalize_quot x = normalize_quot y \<and> snd x \<noteq> 0 \<and> snd y \<noteq> 0"
  by (cases x, cases y) (auto simp: fractrel_def normalize_quot_eq_iff)
  
lemma fractrel_normalize_quot_left:
  assumes "snd x \<noteq> 0"
  shows   "fractrel (normalize_quot x) y \<longleftrightarrow> fractrel x y"
  using assms by (subst (1 2) fractrel_iff_normalize_quot_eq) auto

lemma fractrel_normalize_quot_right:
  assumes "snd x \<noteq> 0"
  shows   "fractrel y (normalize_quot x) \<longleftrightarrow> fractrel y x"
  using assms by (subst (1 2) fractrel_iff_normalize_quot_eq) auto

  
lift_definition quot_of_fract :: 
  "'a :: {ring_gcd,idom_divide,semiring_gcd_mult_normalize} fract \<Rightarrow> 'a \<times> 'a" 
    is normalize_quot
  by (subst (asm) fractrel_iff_normalize_quot_eq) simp_all
  
lemma quot_to_fract_quot_of_fract [simp]: "quot_to_fract (quot_of_fract x) = x"
  unfolding quot_to_fract_def
proof transfer
  fix x :: "'a \<times> 'a" assume rel: "fractrel x x"
  define x' where "x' = normalize_quot x"
  obtain a b where [simp]: "x = (a, b)" by (cases x)
  from rel have "b \<noteq> 0" by simp
  from normalize_quotE[OF this, of a] obtain d
    where
      "a = fst (normalize_quot (a, b)) * d"
      "b = snd (normalize_quot (a, b)) * d"
      "d dvd a"
      "d dvd b"
      "d \<noteq> 0" .
  hence "a = fst x' * d" "b = snd x' * d" "d \<noteq> 0" "snd x' \<noteq> 0" by (simp_all add: x'_def)
  thus "fractrel (case x' of (a, b) \<Rightarrow> if b = 0 then (0, 1) else (a, b)) x"
    by (auto simp add: case_prod_unfold)
qed

lemma quot_of_fract_quot_to_fract: "quot_of_fract (quot_to_fract x) = normalize_quot x"
proof (cases "snd x = 0")
  case True
  thus ?thesis unfolding quot_to_fract_def
    by transfer (simp add: case_prod_unfold normalize_quot_def)
next
  case False
  thus ?thesis unfolding quot_to_fract_def by transfer (simp add: case_prod_unfold)
qed

lemma quot_of_fract_quot_to_fract': 
  "x \<in> normalized_fracts \<Longrightarrow> quot_of_fract (quot_to_fract x) = x"
  unfolding quot_to_fract_def by transfer (auto simp: normalize_quot_id)

lemma quot_of_fract_in_normalized_fracts [simp]: "quot_of_fract x \<in> normalized_fracts"
  by transfer simp

lemma normalize_quotI:
  assumes "a * d = b * c" "b \<noteq> 0" "(c, d) \<in> normalized_fracts"
  shows   "normalize_quot (a, b) = (c, d)"
proof -
  from assms have "normalize_quot (a, b) = normalize_quot (c, d)"
    by (subst normalize_quot_eq_iff) auto
  also have "\<dots> = (c, d)" by (intro normalize_quot_id) fact
  finally show ?thesis .
qed

lemma td_normalized_fract:
  "type_definition quot_of_fract quot_to_fract normalized_fracts"
  by standard (simp_all add: quot_of_fract_quot_to_fract')

lemma quot_of_fract_add_aux:
  assumes "snd x \<noteq> 0" "snd y \<noteq> 0" 
  shows   "(fst x * snd y + fst y * snd x) * (snd (normalize_quot x) * snd (normalize_quot y)) =
             snd x * snd y * (fst (normalize_quot x) * snd (normalize_quot y) +
             snd (normalize_quot x) * fst (normalize_quot y))"
proof -
  from normalize_quotE'[OF assms(1)] obtain d
    where d:
      "fst x = fst (normalize_quot x) * d"
      "snd x = snd (normalize_quot x) * d"
      "d dvd fst x"
      "d dvd snd x"
      "d \<noteq> 0" .
  from normalize_quotE'[OF assms(2)] obtain e
    where e:
      "fst y = fst (normalize_quot y) * e"
      "snd y = snd (normalize_quot y) * e"
      "e dvd fst y"
      "e dvd snd y"
      "e \<noteq> 0" .
  show ?thesis by (simp_all add: d e algebra_simps)
qed


locale fract_as_normalized_quot
begin
setup_lifting td_normalized_fract
end


lemma quot_of_fract_add:
  "quot_of_fract (x + y) = 
     (let (a,b) = quot_of_fract x; (c,d) = quot_of_fract y
      in  normalize_quot (a * d + b * c, b * d))"
  by transfer (insert quot_of_fract_add_aux, 
               simp_all add: Let_def case_prod_unfold normalize_quot_eq_iff)

lemma quot_of_fract_uminus:
  "quot_of_fract (-x) = (let (a,b) = quot_of_fract x in (-a, b))"
  by transfer (auto simp: case_prod_unfold Let_def normalize_quot_def dvd_neg_div mult_unit_dvd_iff)

lemma quot_of_fract_diff:
  "quot_of_fract (x - y) = 
     (let (a,b) = quot_of_fract x; (c,d) = quot_of_fract y
      in  normalize_quot (a * d - b * c, b * d))" (is "_ = ?rhs")
proof -
  have "x - y = x + -y" by simp
  also have "quot_of_fract \<dots> = ?rhs"
    by (simp only: quot_of_fract_add quot_of_fract_uminus Let_def case_prod_unfold) simp_all
  finally show ?thesis .
qed

lemma normalize_quot_mult_coprime:
  assumes "coprime a b" "coprime c d" "unit_factor b = 1" "unit_factor d = 1"
  defines "e \<equiv> fst (normalize_quot (a, d))" and "f \<equiv> snd (normalize_quot (a, d))"
     and  "g \<equiv> fst (normalize_quot (c, b))" and "h \<equiv> snd (normalize_quot (c, b))"
  shows   "normalize_quot (a * c, b * d) = (e * g, f * h)"
proof (rule normalize_quotI)
  from assms have "gcd a b = 1" "gcd c d = 1"
    by simp_all
  from assms have "b \<noteq> 0" "d \<noteq> 0" by auto
  with assms have "normalize b = b" "normalize d = d"
    by (auto intro: normalize_unit_factor_eqI)
  from normalize_quotE [OF \<open>b \<noteq> 0\<close>, of c] obtain k
    where
      "c = fst (normalize_quot (c, b)) * k"
      "b = snd (normalize_quot (c, b)) * k"
      "k dvd c" "k dvd b" "k \<noteq> 0" .
  note k = this [folded \<open>gcd a b = 1\<close> \<open>gcd c d = 1\<close> assms(3) assms(4)]
  from normalize_quotE [OF \<open>d \<noteq> 0\<close>, of a] obtain l
    where "a = fst (normalize_quot (a, d)) * l"
      "d = snd (normalize_quot (a, d)) * l"
      "l dvd a" "l dvd d" "l \<noteq> 0" .
  note l = this [folded \<open>gcd a b = 1\<close> \<open>gcd c d = 1\<close> assms(3) assms(4)]
  from k l show "a * c * (f * h) = b * d * (e * g)"
    by (metis e_def f_def g_def h_def mult.commute mult.left_commute)
  from assms have [simp]: "unit_factor f = 1" "unit_factor h = 1"
    by simp_all
  from assms have "coprime e f" "coprime g h" by (simp_all add: coprime_normalize_quot)
  with k l assms(1,2) \<open>b \<noteq> 0\<close> \<open>d \<noteq> 0\<close> \<open>unit_factor b = 1\<close> \<open>unit_factor d = 1\<close>
    \<open>normalize b = b\<close> \<open>normalize d = d\<close>
  show "(e * g, f * h) \<in> normalized_fracts"
    by (simp add: normalized_fracts_def unit_factor_mult e_def f_def g_def h_def
      coprime_normalize_quot dvd_unit_factor_div unit_factor_gcd)
      (metis coprime_mult_left_iff coprime_mult_right_iff)
qed (insert assms(3,4), auto)

lemma normalize_quot_mult:
  assumes "snd x \<noteq> 0" "snd y \<noteq> 0"
  shows   "normalize_quot (fst x * fst y, snd x * snd y) = normalize_quot 
             (fst (normalize_quot x) * fst (normalize_quot y),
              snd (normalize_quot x) * snd (normalize_quot y))"
proof -
  from normalize_quotE'[OF assms(1)] obtain d where d:
    "fst x = fst (normalize_quot x) * d"
    "snd x = snd (normalize_quot x) * d"
    "d dvd fst x"
    "d dvd snd x"
    "d \<noteq> 0" .
  from normalize_quotE'[OF assms(2)] obtain e where e:
    "fst y = fst (normalize_quot y) * e"
    "snd y = snd (normalize_quot y) * e"
    "e dvd fst y"
    "e dvd snd y"
    "e \<noteq> 0" .
  show ?thesis by (simp_all add: d e algebra_simps normalize_quot_eq_iff)
qed

lemma quot_of_fract_mult:
  "quot_of_fract (x * y) = 
     (let (a,b) = quot_of_fract x; (c,d) = quot_of_fract y;
          (e,f) = normalize_quot (a,d); (g,h) = normalize_quot (c,b)
      in  (e*g, f*h))"
  by transfer
     (simp add: split_def Let_def coprime_normalize_quot normalize_quot_mult normalize_quot_mult_coprime)
  
lemma normalize_quot_0 [simp]: 
    "normalize_quot (0, x) = (0, 1)" "normalize_quot (x, 0) = (0, 1)"
  by (simp_all add: normalize_quot_def)
  
lemma normalize_quot_eq_0_iff [simp]: "fst (normalize_quot x) = 0 \<longleftrightarrow> fst x = 0 \<or> snd x = 0"
  by (auto simp: normalize_quot_def case_prod_unfold Let_def div_mult_unit2 dvd_div_eq_0_iff)
  
lemma fst_quot_of_fract_0_imp: "fst (quot_of_fract x) = 0 \<Longrightarrow> snd (quot_of_fract x) = 1"
  by transfer auto

lemma normalize_quot_swap:
  assumes "a \<noteq> 0" "b \<noteq> 0"
  defines "a' \<equiv> fst (normalize_quot (a, b))" and "b' \<equiv> snd (normalize_quot (a, b))"
  shows   "normalize_quot (b, a) = (b' div unit_factor a', a' div unit_factor a')"
proof (rule normalize_quotI)
  from normalize_quotE[OF assms(2), of a] obtain d where
    "a = fst (normalize_quot (a, b)) * d"
    "b = snd (normalize_quot (a, b)) * d"
    "d dvd a" "d dvd b" "d \<noteq> 0" .
  note d = this [folded assms(3,4)]
  show "b * (a' div unit_factor a') = a * (b' div unit_factor a')"
    using assms(1,2) d 
    by (simp add: div_unit_factor [symmetric] unit_div_mult_swap mult_ac del: div_unit_factor)
  have "coprime a' b'" by (simp add: a'_def b'_def coprime_normalize_quot)
  thus "(b' div unit_factor a', a' div unit_factor a') \<in> normalized_fracts"
    using assms(1,2) d
    by (auto simp add: normalized_fracts_def ac_simps dvd_div_unit_iff elim: coprime_imp_coprime)
qed fact+
  
lemma quot_of_fract_inverse:
  "quot_of_fract (inverse x) = 
     (let (a,b) = quot_of_fract x; d = unit_factor a 
      in  if d = 0 then (0, 1) else (b div d, a div d))"
proof (transfer, goal_cases)
  case (1 x)
  from normalize_quot_swap[of "fst x" "snd x"] show ?case
    by (auto simp: Let_def case_prod_unfold)
qed

lemma normalize_quot_div_unit_left:
  fixes x y u
  assumes "is_unit u"
  defines "x' \<equiv> fst (normalize_quot (x, y))" and "y' \<equiv> snd (normalize_quot (x, y))"
  shows "normalize_quot (x div u, y) = (x' div u, y')"
proof (cases "y = 0")
  case False
  define v where "v = 1 div u"
  with \<open>is_unit u\<close> have "is_unit v" and u: "\<And>a. a div u = a * v"
    by simp_all
  from \<open>is_unit v\<close> have "coprime v = top"
    by (simp add: fun_eq_iff is_unit_left_imp_coprime)
  from normalize_quotE[OF False, of x] obtain d where
    "x = fst (normalize_quot (x, y)) * d"
    "y = snd (normalize_quot (x, y)) * d"
    "d dvd x" "d dvd y" "d \<noteq> 0" .
  note d = this[folded assms(2,3)]
  from assms have "coprime x' y'" "unit_factor y' = 1"
    by (simp_all add: coprime_normalize_quot)
  with d \<open>coprime v = top\<close> have "normalize_quot (x * v, y) = (x' * v, y')"
    by (auto simp: normalized_fracts_def intro: normalize_quotI)
  then show ?thesis
    by (simp add: u)
qed (simp_all add: assms)

lemma normalize_quot_div_unit_right:
  fixes x y u
  assumes "is_unit u"
  defines "x' \<equiv> fst (normalize_quot (x, y))" and "y' \<equiv> snd (normalize_quot (x, y))"
  shows "normalize_quot (x, y div u) = (x' * u, y')"
proof (cases "y = 0")
  case False
  from normalize_quotE[OF this, of x]
  obtain d where d:
    "x = fst (normalize_quot (x, y)) * d"
    "y = snd (normalize_quot (x, y)) * d"
    "d dvd x" "d dvd y" "d \<noteq> 0" .
  note d = this[folded assms(2,3)]
  from assms have "coprime x' y'" "unit_factor y' = 1" by (simp_all add: coprime_normalize_quot)
  with d \<open>is_unit u\<close> show ?thesis
    by (auto simp add: normalized_fracts_def is_unit_left_imp_coprime unit_div_eq_0_iff intro: normalize_quotI)
qed (simp_all add: assms)

lemma normalize_quot_normalize_left:
  fixes x y u
  defines "x' \<equiv> fst (normalize_quot (x, y))" and "y' \<equiv> snd (normalize_quot (x, y))"
  shows "normalize_quot (normalize x, y) = (x' div unit_factor x, y')"
  using normalize_quot_div_unit_left[of "unit_factor x" x y]
  by (cases "x = 0") (simp_all add: assms)
  
lemma normalize_quot_normalize_right:
  fixes x y u
  defines "x' \<equiv> fst (normalize_quot (x, y))" and "y' \<equiv> snd (normalize_quot (x, y))"
  shows "normalize_quot (x, normalize y) = (x' * unit_factor y, y')"
  using normalize_quot_div_unit_right[of "unit_factor y" x y]
  by (cases "y = 0") (simp_all add: assms)
  
lemma quot_of_fract_0 [simp]: "quot_of_fract 0 = (0, 1)"
  by transfer auto

lemma quot_of_fract_1 [simp]: "quot_of_fract 1 = (1, 1)"
  by transfer (rule normalize_quotI, simp_all add: normalized_fracts_def)

lemma quot_of_fract_divide:
  "quot_of_fract (x / y) = (if y = 0 then (0, 1) else
     (let (a,b) = quot_of_fract x; (c,d) = quot_of_fract y;
          (e,f) = normalize_quot (a,c); (g,h) = normalize_quot (d,b)
      in  (e * g, f * h)))" (is "_ = ?rhs")
proof (cases "y = 0")
  case False
  hence A: "fst (quot_of_fract y) \<noteq> 0" by transfer auto
  have "x / y = x * inverse y" by (simp add: divide_inverse)
  also from False A have "quot_of_fract \<dots> = ?rhs"
    by (simp only: quot_of_fract_mult quot_of_fract_inverse)
       (simp_all add: Let_def case_prod_unfold fst_quot_of_fract_0_imp
          normalize_quot_div_unit_left normalize_quot_div_unit_right 
          normalize_quot_normalize_right normalize_quot_normalize_left)
  finally show ?thesis .
qed simp_all

end
