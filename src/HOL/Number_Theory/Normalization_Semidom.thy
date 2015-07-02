theory Normalization_Semidom
imports Main
begin

context algebraic_semidom
begin

lemma is_unit_divide_mult_cancel_left:
  assumes "a \<noteq> 0" and "is_unit b"
  shows "a div (a * b) = 1 div b"
proof -
  from assms have "a div (a * b) = a div a div b"
    by (simp add: mult_unit_dvd_iff dvd_div_mult2_eq)
  with assms show ?thesis by simp
qed

lemma is_unit_divide_mult_cancel_right:
  assumes "a \<noteq> 0" and "is_unit b"
  shows "a div (b * a) = 1 div b"
  using assms is_unit_divide_mult_cancel_left [of a b] by (simp add: ac_simps)

end

class normalization_semidom = algebraic_semidom +
  fixes normalize :: "'a \<Rightarrow> 'a"
    and unit_factor :: "'a \<Rightarrow> 'a"
  assumes unit_factor_mult_normalize [simp]: "unit_factor a * normalize a = a"
  assumes normalize_0 [simp]: "normalize 0 = 0"
    and unit_factor_0 [simp]: "unit_factor 0 = 0"
  assumes is_unit_normalize:
    "is_unit a  \<Longrightarrow> normalize a = 1"
  assumes unit_factor_is_unit [iff]: 
    "a \<noteq> 0 \<Longrightarrow> is_unit (unit_factor a)"
  assumes unit_factor_mult: "unit_factor (a * b) = unit_factor a * unit_factor b"
begin

lemma unit_factor_dvd [simp]:
  "a \<noteq> 0 \<Longrightarrow> unit_factor a dvd b"
  by (rule unit_imp_dvd) simp

lemma unit_factor_self [simp]:
  "unit_factor a dvd a"
  by (cases "a = 0") simp_all 
  
lemma normalize_mult_unit_factor [simp]:
  "normalize a * unit_factor a = a"
  using unit_factor_mult_normalize [of a] by (simp add: ac_simps)

lemma normalize_eq_0_iff [simp]:
  "normalize a = 0 \<longleftrightarrow> a = 0" (is "?P \<longleftrightarrow> ?Q")
proof
  assume ?P
  moreover have "unit_factor a * normalize a = a" by simp
  ultimately show ?Q by simp 
next
  assume ?Q then show ?P by simp
qed

lemma unit_factor_eq_0_iff [simp]:
  "unit_factor a = 0 \<longleftrightarrow> a = 0" (is "?P \<longleftrightarrow> ?Q")
proof
  assume ?P
  moreover have "unit_factor a * normalize a = a" by simp
  ultimately show ?Q by simp 
next
  assume ?Q then show ?P by simp
qed

lemma is_unit_unit_factor:
  assumes "is_unit a" shows "unit_factor a = a"
proof - 
  from assms have "normalize a = 1" by (rule is_unit_normalize)
  moreover from unit_factor_mult_normalize have "unit_factor a * normalize a = a" .
  ultimately show ?thesis by simp
qed

lemma unit_factor_1 [simp]:
  "unit_factor 1 = 1"
  by (rule is_unit_unit_factor) simp

lemma normalize_1 [simp]:
  "normalize 1 = 1"
  by (rule is_unit_normalize) simp

lemma normalize_1_iff:
  "normalize a = 1 \<longleftrightarrow> is_unit a" (is "?P \<longleftrightarrow> ?Q")
proof
  assume ?Q then show ?P by (rule is_unit_normalize)
next
  assume ?P
  then have "a \<noteq> 0" by auto
  from \<open>?P\<close> have "unit_factor a * normalize a = unit_factor a * 1"
    by simp
  then have "unit_factor a = a"
    by simp
  moreover have "is_unit (unit_factor a)"
    using \<open>a \<noteq> 0\<close> by simp
  ultimately show ?Q by simp
qed
  
lemma div_normalize [simp]:
  "a div normalize a = unit_factor a"
proof (cases "a = 0")
  case True then show ?thesis by simp
next
  case False then have "normalize a \<noteq> 0" by simp 
  with nonzero_mult_divide_cancel_right
  have "unit_factor a * normalize a div normalize a = unit_factor a" by blast
  then show ?thesis by simp
qed

lemma div_unit_factor [simp]:
  "a div unit_factor a = normalize a"
proof (cases "a = 0")
  case True then show ?thesis by simp
next
  case False then have "unit_factor a \<noteq> 0" by simp 
  with nonzero_mult_divide_cancel_left
  have "unit_factor a * normalize a div unit_factor a = normalize a" by blast
  then show ?thesis by simp
qed

lemma normalize_div [simp]:
  "normalize a div a = 1 div unit_factor a"
proof (cases "a = 0")
  case True then show ?thesis by simp
next
  case False
  have "normalize a div a = normalize a div (unit_factor a * normalize a)"
    by simp
  also have "\<dots> = 1 div unit_factor a"
    using False by (subst is_unit_divide_mult_cancel_right) simp_all
  finally show ?thesis .
qed

lemma mult_one_div_unit_factor [simp]:
  "a * (1 div unit_factor b) = a div unit_factor b"
  by (cases "b = 0") simp_all

lemma normalize_mult:
  "normalize (a * b) = normalize a * normalize b"
proof (cases "a = 0 \<or> b = 0")
  case True then show ?thesis by auto
next
  case False
  from unit_factor_mult_normalize have "unit_factor (a * b) * normalize (a * b) = a * b" .
  then have "normalize (a * b) = a * b div unit_factor (a * b)" by simp
  also have "\<dots> = a * b div unit_factor (b * a)" by (simp add: ac_simps)
  also have "\<dots> = a * b div unit_factor b div unit_factor a"
    using False by (simp add: unit_factor_mult is_unit_div_mult2_eq [symmetric])
  also have "\<dots> = a * (b div unit_factor b) div unit_factor a"
    using False by (subst unit_div_mult_swap) simp_all
  also have "\<dots> = normalize a * normalize b"
    using False by (simp add: mult.commute [of a] mult.commute [of "normalize a"] unit_div_mult_swap [symmetric])
  finally show ?thesis .
qed
 
lemma unit_factor_idem [simp]:
  "unit_factor (unit_factor a) = unit_factor a"
  by (cases "a = 0") (auto intro: is_unit_unit_factor)

lemma normalize_unit_factor [simp]:
  "a \<noteq> 0 \<Longrightarrow> normalize (unit_factor a) = 1"
  by (rule is_unit_normalize) simp
  
lemma normalize_idem [simp]:
  "normalize (normalize a) = normalize a"
proof (cases "a = 0")
  case True then show ?thesis by simp
next
  case False
  have "normalize a = normalize (unit_factor a * normalize a)" by simp
  also have "\<dots> = normalize (unit_factor a) * normalize (normalize a)"
    by (simp only: normalize_mult)
  finally show ?thesis using False by simp_all
qed

lemma unit_factor_normalize [simp]:
  assumes "a \<noteq> 0"
  shows "unit_factor (normalize a) = 1"
proof -
  from assms have "normalize a \<noteq> 0" by simp
  have "unit_factor (normalize a) * normalize (normalize a) = normalize a"
    by (simp only: unit_factor_mult_normalize)
  then have "unit_factor (normalize a) * normalize a = normalize a"
    by simp
  with \<open>normalize a \<noteq> 0\<close>
  have "unit_factor (normalize a) * normalize a div normalize a = normalize a div normalize a"
    by simp
  with \<open>normalize a \<noteq> 0\<close>
  show ?thesis by simp
qed

lemma dvd_unit_factor_div:
  assumes "b dvd a"
  shows "unit_factor (a div b) = unit_factor a div unit_factor b"
proof -
  from assms have "a = a div b * b"
    by simp
  then have "unit_factor a = unit_factor (a div b * b)"
    by simp
  then show ?thesis
    by (cases "b = 0") (simp_all add: unit_factor_mult)
qed

lemma dvd_normalize_div:
  assumes "b dvd a"
  shows "normalize (a div b) = normalize a div normalize b"
proof -
  from assms have "a = a div b * b"
    by simp
  then have "normalize a = normalize (a div b * b)"
    by simp
  then show ?thesis
    by (cases "b = 0") (simp_all add: normalize_mult)
qed

lemma normalize_dvd_iff [simp]:
  "normalize a dvd b \<longleftrightarrow> a dvd b"
proof -
  have "normalize a dvd b \<longleftrightarrow> unit_factor a * normalize a dvd b"
    using mult_unit_dvd_iff [of "unit_factor a" "normalize a" b]
      by (cases "a = 0") simp_all
  then show ?thesis by simp
qed

lemma dvd_normalize_iff [simp]:
  "a dvd normalize b \<longleftrightarrow> a dvd b"
proof -
  have "a dvd normalize  b \<longleftrightarrow> a dvd normalize b * unit_factor b"
    using dvd_mult_unit_iff [of "unit_factor b" a "normalize b"]
      by (cases "b = 0") simp_all
  then show ?thesis by simp
qed

lemma associated_normalize_left [simp]:
  "associated (normalize a) b \<longleftrightarrow> associated a b"
  by (auto simp add: associated_def)

lemma associated_normalize_right [simp]:
  "associated a (normalize b) \<longleftrightarrow> associated a b"
  by (auto simp add: associated_def)

lemma associated_iff_normalize:
  "associated a b \<longleftrightarrow> normalize a = normalize b" (is "?P \<longleftrightarrow> ?Q")
proof (cases "a = 0 \<or> b = 0")
  case True then show ?thesis by auto
next
  case False
  show ?thesis
  proof
    assume ?P then show ?Q
      by (rule associated_is_unitE) (simp add: normalize_mult is_unit_normalize)
  next
    from False have *: "is_unit (unit_factor a div unit_factor b)"
      by auto
    assume ?Q then have "unit_factor a * normalize a = unit_factor a * normalize b"
      by simp
    then have "a = unit_factor a * (b div unit_factor b)"
      by simp
    with False have "a = (unit_factor a div unit_factor b) * b"
      by (simp add: unit_div_commute unit_div_mult_swap [symmetric])
    with * show ?P 
      by (rule is_unit_associatedI)
  qed
qed

lemma normalize_power:
  "normalize (a ^ n) = normalize a ^ n"
  by (induct n) (simp_all add: normalize_mult)

lemma unit_factor_power:
  "unit_factor (a ^ n) = unit_factor a ^ n"
  by (induct n) (simp_all add: unit_factor_mult)

lemma associated_eqI:
  assumes "associated a b"
  assumes "unit_factor a \<in> {0, 1}" and "unit_factor b \<in> {0, 1}"
  shows "a = b"
proof (cases "a = 0")
  case True with assms show ?thesis by simp
next
  case False with assms have "b \<noteq> 0" by auto
  with False assms have "unit_factor a = unit_factor b"
    by simp
  moreover from assms have "normalize a = normalize b"
    by (simp add: associated_iff_normalize)
  ultimately have "unit_factor a * normalize a = unit_factor b * normalize b"
    by simp
  then show ?thesis
    by simp
qed

end

instantiation nat :: normalization_semidom
begin

definition normalize_nat
  where [simp]: "normalize = (id :: nat \<Rightarrow> nat)"

definition unit_factor_nat
  where "unit_factor n = (if n = 0 then 0 else 1 :: nat)"

lemma unit_factor_simps [simp]:
  "unit_factor 0 = (0::nat)"
  "unit_factor (Suc n) = 1"
  by (simp_all add: unit_factor_nat_def)

instance
  by default (simp_all add: unit_factor_nat_def)
  
end

instantiation int :: normalization_semidom
begin

definition normalize_int
  where [simp]: "normalize = (abs :: int \<Rightarrow> int)"

definition unit_factor_int
  where [simp]: "unit_factor = (sgn :: int \<Rightarrow> int)"

instance
proof
  fix k :: int
  assume "k \<noteq> 0"
  then have "\<bar>sgn k\<bar> = 1"
    by (cases "0::int" k rule: linorder_cases) simp_all
  then show "is_unit (unit_factor k)"
    by simp
qed (simp_all add: sgn_times mult_sgn_abs)
  
end

end
