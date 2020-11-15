(*  Title:      HOL/Rat.thy
    Author:     Markus Wenzel, TU Muenchen
*)

section \<open>Rational numbers\<close>

theory Rat
  imports Archimedean_Field
begin

subsection \<open>Rational numbers as quotient\<close>

subsubsection \<open>Construction of the type of rational numbers\<close>

definition ratrel :: "(int \<times> int) \<Rightarrow> (int \<times> int) \<Rightarrow> bool"
  where "ratrel = (\<lambda>x y. snd x \<noteq> 0 \<and> snd y \<noteq> 0 \<and> fst x * snd y = fst y * snd x)"

lemma ratrel_iff [simp]: "ratrel x y \<longleftrightarrow> snd x \<noteq> 0 \<and> snd y \<noteq> 0 \<and> fst x * snd y = fst y * snd x"
  by (simp add: ratrel_def)

lemma exists_ratrel_refl: "\<exists>x. ratrel x x"
  by (auto intro!: one_neq_zero)

lemma symp_ratrel: "symp ratrel"
  by (simp add: ratrel_def symp_def)

lemma transp_ratrel: "transp ratrel"
proof (rule transpI, unfold split_paired_all)
  fix a b a' b' a'' b'' :: int
  assume *: "ratrel (a, b) (a', b')"
  assume **: "ratrel (a', b') (a'', b'')"
  have "b' * (a * b'') = b'' * (a * b')" by simp
  also from * have "a * b' = a' * b" by auto
  also have "b'' * (a' * b) = b * (a' * b'')" by simp
  also from ** have "a' * b'' = a'' * b'" by auto
  also have "b * (a'' * b') = b' * (a'' * b)" by simp
  finally have "b' * (a * b'') = b' * (a'' * b)" .
  moreover from ** have "b' \<noteq> 0" by auto
  ultimately have "a * b'' = a'' * b" by simp
  with * ** show "ratrel (a, b) (a'', b'')" by auto
qed

lemma part_equivp_ratrel: "part_equivp ratrel"
  by (rule part_equivpI [OF exists_ratrel_refl symp_ratrel transp_ratrel])

quotient_type rat = "int \<times> int" / partial: "ratrel"
  morphisms Rep_Rat Abs_Rat
  by (rule part_equivp_ratrel)

lemma Domainp_cr_rat [transfer_domain_rule]: "Domainp pcr_rat = (\<lambda>x. snd x \<noteq> 0)"
  by (simp add: rat.domain_eq)


subsubsection \<open>Representation and basic operations\<close>

lift_definition Fract :: "int \<Rightarrow> int \<Rightarrow> rat"
  is "\<lambda>a b. if b = 0 then (0, 1) else (a, b)"
  by simp

lemma eq_rat:
  "\<And>a b c d. b \<noteq> 0 \<Longrightarrow> d \<noteq> 0 \<Longrightarrow> Fract a b = Fract c d \<longleftrightarrow> a * d = c * b"
  "\<And>a. Fract a 0 = Fract 0 1"
  "\<And>a c. Fract 0 a = Fract 0 c"
  by (transfer, simp)+

lemma Rat_cases [case_names Fract, cases type: rat]:
  assumes that: "\<And>a b. q = Fract a b \<Longrightarrow> b > 0 \<Longrightarrow> coprime a b \<Longrightarrow> C"
  shows C
proof -
  obtain a b :: int where q: "q = Fract a b" and b: "b \<noteq> 0"
    by transfer simp
  let ?a = "a div gcd a b"
  let ?b = "b div gcd a b"
  from b have "?b * gcd a b = b"
    by simp
  with b have "?b \<noteq> 0"
    by fastforce
  with q b have q2: "q = Fract ?a ?b"
    by (simp add: eq_rat dvd_div_mult mult.commute [of a])
  from b have coprime: "coprime ?a ?b"
    by (auto intro: div_gcd_coprime)
  show C
  proof (cases "b > 0")
    case True
    then have "?b > 0"
      by (simp add: nonneg1_imp_zdiv_pos_iff)
    from q2 this coprime show C by (rule that)
  next
    case False
    have "q = Fract (- ?a) (- ?b)"
      unfolding q2 by transfer simp
    moreover from False b have "- ?b > 0"
      by (simp add: pos_imp_zdiv_neg_iff)
    moreover from coprime have "coprime (- ?a) (- ?b)"
      by simp
    ultimately show C
      by (rule that)
  qed
qed

lemma Rat_induct [case_names Fract, induct type: rat]:
  assumes "\<And>a b. b > 0 \<Longrightarrow> coprime a b \<Longrightarrow> P (Fract a b)"
  shows "P q"
  using assms by (cases q) simp

instantiation rat :: field
begin

lift_definition zero_rat :: "rat" is "(0, 1)"
  by simp

lift_definition one_rat :: "rat" is "(1, 1)"
  by simp

lemma Zero_rat_def: "0 = Fract 0 1"
  by transfer simp

lemma One_rat_def: "1 = Fract 1 1"
  by transfer simp

lift_definition plus_rat :: "rat \<Rightarrow> rat \<Rightarrow> rat"
  is "\<lambda>x y. (fst x * snd y + fst y * snd x, snd x * snd y)"
  by (auto simp: distrib_right) (simp add: ac_simps)

lemma add_rat [simp]:
  assumes "b \<noteq> 0" and "d \<noteq> 0"
  shows "Fract a b + Fract c d = Fract (a * d + c * b) (b * d)"
  using assms by transfer simp

lift_definition uminus_rat :: "rat \<Rightarrow> rat" is "\<lambda>x. (- fst x, snd x)"
  by simp

lemma minus_rat [simp]: "- Fract a b = Fract (- a) b"
  by transfer simp

lemma minus_rat_cancel [simp]: "Fract (- a) (- b) = Fract a b"
  by (cases "b = 0") (simp_all add: eq_rat)

definition diff_rat_def: "q - r = q + - r" for q r :: rat

lemma diff_rat [simp]:
  "b \<noteq> 0 \<Longrightarrow> d \<noteq> 0 \<Longrightarrow> Fract a b - Fract c d = Fract (a * d - c * b) (b * d)"
  by (simp add: diff_rat_def)

lift_definition times_rat :: "rat \<Rightarrow> rat \<Rightarrow> rat"
  is "\<lambda>x y. (fst x * fst y, snd x * snd y)"
  by (simp add: ac_simps)

lemma mult_rat [simp]: "Fract a b * Fract c d = Fract (a * c) (b * d)"
  by transfer simp

lemma mult_rat_cancel: "c \<noteq> 0 \<Longrightarrow> Fract (c * a) (c * b) = Fract a b"
  by transfer simp

lift_definition inverse_rat :: "rat \<Rightarrow> rat"
  is "\<lambda>x. if fst x = 0 then (0, 1) else (snd x, fst x)"
  by (auto simp add: mult.commute)

lemma inverse_rat [simp]: "inverse (Fract a b) = Fract b a"
  by transfer simp

definition divide_rat_def: "q div r = q * inverse r" for q r :: rat

lemma divide_rat [simp]: "Fract a b div Fract c d = Fract (a * d) (b * c)"
  by (simp add: divide_rat_def)

instance
proof
  fix q r s :: rat
  show "(q * r) * s = q * (r * s)"
    by transfer simp
  show "q * r = r * q"
    by transfer simp
  show "1 * q = q"
    by transfer simp
  show "(q + r) + s = q + (r + s)"
    by transfer (simp add: algebra_simps)
  show "q + r = r + q"
    by transfer simp
  show "0 + q = q"
    by transfer simp
  show "- q + q = 0"
    by transfer simp
  show "q - r = q + - r"
    by (fact diff_rat_def)
  show "(q + r) * s = q * s + r * s"
    by transfer (simp add: algebra_simps)
  show "(0::rat) \<noteq> 1"
    by transfer simp
  show "inverse q * q = 1" if "q \<noteq> 0"
    using that by transfer simp
  show "q div r = q * inverse r"
    by (fact divide_rat_def)
  show "inverse 0 = (0::rat)"
    by transfer simp
qed

end

(* We cannot state these two rules earlier because of pending sort hypotheses *)
lemma div_add_self1_no_field [simp]:
  assumes "NO_MATCH (x :: 'b :: field) b" "(b :: 'a :: euclidean_semiring_cancel) \<noteq> 0"
  shows "(b + a) div b = a div b + 1"
  using assms(2) by (fact div_add_self1)

lemma div_add_self2_no_field [simp]:
  assumes "NO_MATCH (x :: 'b :: field) b" "(b :: 'a :: euclidean_semiring_cancel) \<noteq> 0"
  shows "(a + b) div b = a div b + 1"
  using assms(2) by (fact div_add_self2)

lemma of_nat_rat: "of_nat k = Fract (of_nat k) 1"
  by (induct k) (simp_all add: Zero_rat_def One_rat_def)

lemma of_int_rat: "of_int k = Fract k 1"
  by (cases k rule: int_diff_cases) (simp add: of_nat_rat)

lemma Fract_of_nat_eq: "Fract (of_nat k) 1 = of_nat k"
  by (rule of_nat_rat [symmetric])

lemma Fract_of_int_eq: "Fract k 1 = of_int k"
  by (rule of_int_rat [symmetric])

lemma rat_number_collapse:
  "Fract 0 k = 0"
  "Fract 1 1 = 1"
  "Fract (numeral w) 1 = numeral w"
  "Fract (- numeral w) 1 = - numeral w"
  "Fract (- 1) 1 = - 1"
  "Fract k 0 = 0"
  using Fract_of_int_eq [of "numeral w"]
    and Fract_of_int_eq [of "- numeral w"]
  by (simp_all add: Zero_rat_def One_rat_def eq_rat)

lemma rat_number_expand:
  "0 = Fract 0 1"
  "1 = Fract 1 1"
  "numeral k = Fract (numeral k) 1"
  "- 1 = Fract (- 1) 1"
  "- numeral k = Fract (- numeral k) 1"
  by (simp_all add: rat_number_collapse)

lemma Rat_cases_nonzero [case_names Fract 0]:
  assumes Fract: "\<And>a b. q = Fract a b \<Longrightarrow> b > 0 \<Longrightarrow> a \<noteq> 0 \<Longrightarrow> coprime a b \<Longrightarrow> C"
    and 0: "q = 0 \<Longrightarrow> C"
  shows C
proof (cases "q = 0")
  case True
  then show C using 0 by auto
next
  case False
  then obtain a b where *: "q = Fract a b" "b > 0" "coprime a b"
    by (cases q) auto
  with False have "0 \<noteq> Fract a b"
    by simp
  with \<open>b > 0\<close> have "a \<noteq> 0"
    by (simp add: Zero_rat_def eq_rat)
  with Fract * show C by blast
qed


subsubsection \<open>Function \<open>normalize\<close>\<close>

lemma Fract_coprime: "Fract (a div gcd a b) (b div gcd a b) = Fract a b"
proof (cases "b = 0")
  case True
  then show ?thesis
    by (simp add: eq_rat)
next
  case False
  moreover have "b div gcd a b * gcd a b = b"
    by (rule dvd_div_mult_self) simp
  ultimately have "b div gcd a b * gcd a b \<noteq> 0"
    by simp
  then have "b div gcd a b \<noteq> 0"
    by fastforce
  with False show ?thesis
    by (simp add: eq_rat dvd_div_mult mult.commute [of a])
qed

definition normalize :: "int \<times> int \<Rightarrow> int \<times> int"
  where "normalize p =
   (if snd p > 0 then (let a = gcd (fst p) (snd p) in (fst p div a, snd p div a))
    else if snd p = 0 then (0, 1)
    else (let a = - gcd (fst p) (snd p) in (fst p div a, snd p div a)))"

lemma normalize_crossproduct:
  assumes "q \<noteq> 0" "s \<noteq> 0"
  assumes "normalize (p, q) = normalize (r, s)"
  shows "p * s = r * q"
proof -
  have *: "p * s = q * r"
    if "p * gcd r s = sgn (q * s) * r * gcd p q" and "q * gcd r s = sgn (q * s) * s * gcd p q"
  proof -
    from that have "(p * gcd r s) * (sgn (q * s) * s * gcd p q) =
        (q * gcd r s) * (sgn (q * s) * r * gcd p q)"
      by simp
    with assms show ?thesis
      by (auto simp add: ac_simps sgn_mult sgn_0_0)
  qed
  from assms show ?thesis
    by (auto simp: normalize_def Let_def dvd_div_div_eq_mult mult.commute sgn_mult
        split: if_splits intro: *)
qed

lemma normalize_eq: "normalize (a, b) = (p, q) \<Longrightarrow> Fract p q = Fract a b"
  by (auto simp: normalize_def Let_def Fract_coprime dvd_div_neg rat_number_collapse
      split: if_split_asm)

lemma normalize_denom_pos: "normalize r = (p, q) \<Longrightarrow> q > 0"
  by (auto simp: normalize_def Let_def dvd_div_neg pos_imp_zdiv_neg_iff nonneg1_imp_zdiv_pos_iff
      split: if_split_asm)

lemma normalize_coprime: "normalize r = (p, q) \<Longrightarrow> coprime p q"
  by (auto simp: normalize_def Let_def dvd_div_neg div_gcd_coprime split: if_split_asm)

lemma normalize_stable [simp]: "q > 0 \<Longrightarrow> coprime p q \<Longrightarrow> normalize (p, q) = (p, q)"
  by (simp add: normalize_def)

lemma normalize_denom_zero [simp]: "normalize (p, 0) = (0, 1)"
  by (simp add: normalize_def)

lemma normalize_negative [simp]: "q < 0 \<Longrightarrow> normalize (p, q) = normalize (- p, - q)"
  by (simp add: normalize_def Let_def dvd_div_neg dvd_neg_div)

text\<open>
  Decompose a fraction into normalized, i.e. coprime numerator and denominator:
\<close>

definition quotient_of :: "rat \<Rightarrow> int \<times> int"
  where "quotient_of x =
    (THE pair. x = Fract (fst pair) (snd pair) \<and> snd pair > 0 \<and> coprime (fst pair) (snd pair))"

lemma quotient_of_unique: "\<exists>!p. r = Fract (fst p) (snd p) \<and> snd p > 0 \<and> coprime (fst p) (snd p)"
proof (cases r)
  case (Fract a b)
  then have "r = Fract (fst (a, b)) (snd (a, b)) \<and>
      snd (a, b) > 0 \<and> coprime (fst (a, b)) (snd (a, b))"
    by auto
  then show ?thesis
  proof (rule ex1I)
    fix p
    assume r: "r = Fract (fst p) (snd p) \<and> snd p > 0 \<and> coprime (fst p) (snd p)"
    obtain c d where p: "p = (c, d)" by (cases p)
    with r have Fract': "r = Fract c d" "d > 0" "coprime c d"
      by simp_all
    have "(c, d) = (a, b)"
    proof (cases "a = 0")
      case True
      with Fract Fract' show ?thesis
        by (simp add: eq_rat)
    next
      case False
      with Fract Fract' have *: "c * b = a * d" and "c \<noteq> 0"
        by (auto simp add: eq_rat)
      then have "c * b > 0 \<longleftrightarrow> a * d > 0"
        by auto
      with \<open>b > 0\<close> \<open>d > 0\<close> have "a > 0 \<longleftrightarrow> c > 0"
        by (simp add: zero_less_mult_iff)
      with \<open>a \<noteq> 0\<close> \<open>c \<noteq> 0\<close> have sgn: "sgn a = sgn c"
        by (auto simp add: not_less)
      from \<open>coprime a b\<close> \<open>coprime c d\<close> have "\<bar>a\<bar> * \<bar>d\<bar> = \<bar>c\<bar> * \<bar>b\<bar> \<longleftrightarrow> \<bar>a\<bar> = \<bar>c\<bar> \<and> \<bar>d\<bar> = \<bar>b\<bar>"
        by (simp add: coprime_crossproduct_int)
      with \<open>b > 0\<close> \<open>d > 0\<close> have "\<bar>a\<bar> * d = \<bar>c\<bar> * b \<longleftrightarrow> \<bar>a\<bar> = \<bar>c\<bar> \<and> d = b"
        by simp
      then have "a * sgn a * d = c * sgn c * b \<longleftrightarrow> a * sgn a = c * sgn c \<and> d = b"
        by (simp add: abs_sgn)
      with sgn * show ?thesis
        by (auto simp add: sgn_0_0)
    qed
    with p show "p = (a, b)"
      by simp
  qed
qed

lemma quotient_of_Fract [code]: "quotient_of (Fract a b) = normalize (a, b)"
proof -
  have "Fract a b = Fract (fst (normalize (a, b))) (snd (normalize (a, b)))" (is ?Fract)
    by (rule sym) (auto intro: normalize_eq)
  moreover have "0 < snd (normalize (a, b))" (is ?denom_pos)
    by (cases "normalize (a, b)") (rule normalize_denom_pos, simp)
  moreover have "coprime (fst (normalize (a, b))) (snd (normalize (a, b)))" (is ?coprime)
    by (rule normalize_coprime) simp
  ultimately have "?Fract \<and> ?denom_pos \<and> ?coprime" by blast
  then have "(THE p. Fract a b = Fract (fst p) (snd p) \<and> 0 < snd p \<and>
    coprime (fst p) (snd p)) = normalize (a, b)"
    by (rule the1_equality [OF quotient_of_unique])
  then show ?thesis by (simp add: quotient_of_def)
qed

lemma quotient_of_number [simp]:
  "quotient_of 0 = (0, 1)"
  "quotient_of 1 = (1, 1)"
  "quotient_of (numeral k) = (numeral k, 1)"
  "quotient_of (- 1) = (- 1, 1)"
  "quotient_of (- numeral k) = (- numeral k, 1)"
  by (simp_all add: rat_number_expand quotient_of_Fract)

lemma quotient_of_eq: "quotient_of (Fract a b) = (p, q) \<Longrightarrow> Fract p q = Fract a b"
  by (simp add: quotient_of_Fract normalize_eq)

lemma quotient_of_denom_pos: "quotient_of r = (p, q) \<Longrightarrow> q > 0"
  by (cases r) (simp add: quotient_of_Fract normalize_denom_pos)

lemma quotient_of_denom_pos': "snd (quotient_of r) > 0"
  using quotient_of_denom_pos [of r] by (simp add: prod_eq_iff)

lemma quotient_of_coprime: "quotient_of r = (p, q) \<Longrightarrow> coprime p q"
  by (cases r) (simp add: quotient_of_Fract normalize_coprime)

lemma quotient_of_inject:
  assumes "quotient_of a = quotient_of b"
  shows "a = b"
proof -
  obtain p q r s where a: "a = Fract p q" and b: "b = Fract r s" and "q > 0" and "s > 0"
    by (cases a, cases b)
  with assms show ?thesis
    by (simp add: eq_rat quotient_of_Fract normalize_crossproduct)
qed

lemma quotient_of_inject_eq: "quotient_of a = quotient_of b \<longleftrightarrow> a = b"
  by (auto simp add: quotient_of_inject)


subsubsection \<open>Various\<close>

lemma Fract_of_int_quotient: "Fract k l = of_int k / of_int l"
  by (simp add: Fract_of_int_eq [symmetric])

lemma Fract_add_one: "n \<noteq> 0 \<Longrightarrow> Fract (m + n) n = Fract m n + 1"
  by (simp add: rat_number_expand)

lemma quotient_of_div:
  assumes r: "quotient_of r = (n,d)"
  shows "r = of_int n / of_int d"
proof -
  from theI'[OF quotient_of_unique[of r], unfolded r[unfolded quotient_of_def]]
  have "r = Fract n d" by simp
  then show ?thesis using Fract_of_int_quotient
    by simp
qed


subsubsection \<open>The ordered field of rational numbers\<close>

lift_definition positive :: "rat \<Rightarrow> bool"
  is "\<lambda>x. 0 < fst x * snd x"
proof clarsimp
  fix a b c d :: int
  assume "b \<noteq> 0" and "d \<noteq> 0" and "a * d = c * b"
  then have "a * d * b * d = c * b * b * d"
    by simp
  then have "a * b * d\<^sup>2 = c * d * b\<^sup>2"
    unfolding power2_eq_square by (simp add: ac_simps)
  then have "0 < a * b * d\<^sup>2 \<longleftrightarrow> 0 < c * d * b\<^sup>2"
    by simp
  then show "0 < a * b \<longleftrightarrow> 0 < c * d"
    using \<open>b \<noteq> 0\<close> and \<open>d \<noteq> 0\<close>
    by (simp add: zero_less_mult_iff)
qed

lemma positive_zero: "\<not> positive 0"
  by transfer simp

lemma positive_add: "positive x \<Longrightarrow> positive y \<Longrightarrow> positive (x + y)"
  apply transfer
     apply (auto simp add: zero_less_mult_iff add_pos_pos add_neg_neg mult_pos_neg mult_neg_pos mult_neg_neg)
  done

lemma positive_mult: "positive x \<Longrightarrow> positive y \<Longrightarrow> positive (x * y)"
  apply transfer
  by (metis fst_conv mult.commute mult_pos_neg2 snd_conv zero_less_mult_iff)

lemma positive_minus: "\<not> positive x \<Longrightarrow> x \<noteq> 0 \<Longrightarrow> positive (- x)"
  by transfer (auto simp: neq_iff zero_less_mult_iff mult_less_0_iff)

instantiation rat :: linordered_field
begin

definition "x < y \<longleftrightarrow> positive (y - x)"

definition "x \<le> y \<longleftrightarrow> x < y \<or> x = y" for x y :: rat

definition "\<bar>a\<bar> = (if a < 0 then - a else a)" for a :: rat

definition "sgn a = (if a = 0 then 0 else if 0 < a then 1 else - 1)" for a :: rat

instance
proof
  fix a b c :: rat
  show "\<bar>a\<bar> = (if a < 0 then - a else a)"
    by (rule abs_rat_def)
  show "a < b \<longleftrightarrow> a \<le> b \<and> \<not> b \<le> a"
    unfolding less_eq_rat_def less_rat_def
    using positive_add positive_zero by force
  show "a \<le> a"
    unfolding less_eq_rat_def by simp
  show "a \<le> b \<Longrightarrow> b \<le> c \<Longrightarrow> a \<le> c"
    unfolding less_eq_rat_def less_rat_def
    using positive_add by fastforce
  show "a \<le> b \<Longrightarrow> b \<le> a \<Longrightarrow> a = b"
    unfolding less_eq_rat_def less_rat_def
    using positive_add positive_zero by fastforce
  show "a \<le> b \<Longrightarrow> c + a \<le> c + b"
    unfolding less_eq_rat_def less_rat_def by auto
  show "sgn a = (if a = 0 then 0 else if 0 < a then 1 else - 1)"
    by (rule sgn_rat_def)
  show "a \<le> b \<or> b \<le> a"
    unfolding less_eq_rat_def less_rat_def
    by (auto dest!: positive_minus)
  show "a < b \<Longrightarrow> 0 < c \<Longrightarrow> c * a < c * b"
    unfolding less_rat_def
    by (metis diff_zero positive_mult right_diff_distrib')
qed

end

instantiation rat :: distrib_lattice
begin

definition "(inf :: rat \<Rightarrow> rat \<Rightarrow> rat) = min"

definition "(sup :: rat \<Rightarrow> rat \<Rightarrow> rat) = max"

instance
  by standard (auto simp add: inf_rat_def sup_rat_def max_min_distrib2)

end

lemma positive_rat: "positive (Fract a b) \<longleftrightarrow> 0 < a * b"
  by transfer simp

lemma less_rat [simp]:
  "b \<noteq> 0 \<Longrightarrow> d \<noteq> 0 \<Longrightarrow> Fract a b < Fract c d \<longleftrightarrow> (a * d) * (b * d) < (c * b) * (b * d)"
  by (simp add: less_rat_def positive_rat algebra_simps)

lemma le_rat [simp]:
  "b \<noteq> 0 \<Longrightarrow> d \<noteq> 0 \<Longrightarrow> Fract a b \<le> Fract c d \<longleftrightarrow> (a * d) * (b * d) \<le> (c * b) * (b * d)"
  by (simp add: le_less eq_rat)

lemma abs_rat [simp, code]: "\<bar>Fract a b\<bar> = Fract \<bar>a\<bar> \<bar>b\<bar>"
  by (auto simp add: abs_rat_def zabs_def Zero_rat_def not_less le_less eq_rat zero_less_mult_iff)

lemma sgn_rat [simp, code]: "sgn (Fract a b) = of_int (sgn a * sgn b)"
  unfolding Fract_of_int_eq
  by (auto simp: zsgn_def sgn_rat_def Zero_rat_def eq_rat)
    (auto simp: rat_number_collapse not_less le_less zero_less_mult_iff)

lemma Rat_induct_pos [case_names Fract, induct type: rat]:
  assumes step: "\<And>a b. 0 < b \<Longrightarrow> P (Fract a b)"
  shows "P q"
proof (cases q)
  case (Fract a b)
  have step': "P (Fract a b)" if b: "b < 0" for a b :: int
  proof -
    from b have "0 < - b"
      by simp
    then have "P (Fract (- a) (- b))"
      by (rule step)
    then show "P (Fract a b)"
      by (simp add: order_less_imp_not_eq [OF b])
  qed
  from Fract show "P q"
    by (auto simp add: linorder_neq_iff step step')
qed

lemma zero_less_Fract_iff: "0 < b \<Longrightarrow> 0 < Fract a b \<longleftrightarrow> 0 < a"
  by (simp add: Zero_rat_def zero_less_mult_iff)

lemma Fract_less_zero_iff: "0 < b \<Longrightarrow> Fract a b < 0 \<longleftrightarrow> a < 0"
  by (simp add: Zero_rat_def mult_less_0_iff)

lemma zero_le_Fract_iff: "0 < b \<Longrightarrow> 0 \<le> Fract a b \<longleftrightarrow> 0 \<le> a"
  by (simp add: Zero_rat_def zero_le_mult_iff)

lemma Fract_le_zero_iff: "0 < b \<Longrightarrow> Fract a b \<le> 0 \<longleftrightarrow> a \<le> 0"
  by (simp add: Zero_rat_def mult_le_0_iff)

lemma one_less_Fract_iff: "0 < b \<Longrightarrow> 1 < Fract a b \<longleftrightarrow> b < a"
  by (simp add: One_rat_def mult_less_cancel_right_disj)

lemma Fract_less_one_iff: "0 < b \<Longrightarrow> Fract a b < 1 \<longleftrightarrow> a < b"
  by (simp add: One_rat_def mult_less_cancel_right_disj)

lemma one_le_Fract_iff: "0 < b \<Longrightarrow> 1 \<le> Fract a b \<longleftrightarrow> b \<le> a"
  by (simp add: One_rat_def mult_le_cancel_right)

lemma Fract_le_one_iff: "0 < b \<Longrightarrow> Fract a b \<le> 1 \<longleftrightarrow> a \<le> b"
  by (simp add: One_rat_def mult_le_cancel_right)


subsubsection \<open>Rationals are an Archimedean field\<close>

lemma rat_floor_lemma: "of_int (a div b) \<le> Fract a b \<and> Fract a b < of_int (a div b + 1)"
proof -
  have "Fract a b = of_int (a div b) + Fract (a mod b) b"
    by (cases "b = 0") (simp, simp add: of_int_rat)
  moreover have "0 \<le> Fract (a mod b) b \<and> Fract (a mod b) b < 1"
    unfolding Fract_of_int_quotient
    by (rule linorder_cases [of b 0]) (simp_all add: divide_nonpos_neg)
  ultimately show ?thesis by simp
qed

instance rat :: archimedean_field
proof
  show "\<exists>z. r \<le> of_int z" for r :: rat
  proof (induct r)
    case (Fract a b)
    have "Fract a b \<le> of_int (a div b + 1)"
      using rat_floor_lemma [of a b] by simp
    then show "\<exists>z. Fract a b \<le> of_int z" ..
  qed
qed

instantiation rat :: floor_ceiling
begin

definition floor_rat :: "rat \<Rightarrow> int"
  where"\<lfloor>x\<rfloor> = (THE z. of_int z \<le> x \<and> x < of_int (z + 1))" for x :: rat

instance
proof
  show "of_int \<lfloor>x\<rfloor> \<le> x \<and> x < of_int (\<lfloor>x\<rfloor> + 1)" for x :: rat
    unfolding floor_rat_def using floor_exists1 by (rule theI')
qed

end

lemma floor_Fract [simp]: "\<lfloor>Fract a b\<rfloor> = a div b"
  by (simp add: Fract_of_int_quotient floor_divide_of_int_eq)


subsection \<open>Linear arithmetic setup\<close>

declaration \<open>
  K (Lin_Arith.add_inj_thms @{thms of_int_le_iff [THEN iffD2] of_int_eq_iff [THEN iffD2]}
    (* not needed because x < (y::int) can be rewritten as x + 1 <= y: of_int_less_iff RS iffD2 *)
  #> Lin_Arith.add_inj_const (\<^const_name>\<open>of_nat\<close>, \<^typ>\<open>nat \<Rightarrow> rat\<close>)
  #> Lin_Arith.add_inj_const (\<^const_name>\<open>of_int\<close>, \<^typ>\<open>int \<Rightarrow> rat\<close>))
\<close>


subsection \<open>Embedding from Rationals to other Fields\<close>

context field_char_0
begin

lift_definition of_rat :: "rat \<Rightarrow> 'a"
  is "\<lambda>x. of_int (fst x) / of_int (snd x)"
  by (auto simp: nonzero_divide_eq_eq nonzero_eq_divide_eq) (simp only: of_int_mult [symmetric])

end

lemma of_rat_rat: "b \<noteq> 0 \<Longrightarrow> of_rat (Fract a b) = of_int a / of_int b"
  by transfer simp

lemma of_rat_0 [simp]: "of_rat 0 = 0"
  by transfer simp

lemma of_rat_1 [simp]: "of_rat 1 = 1"
  by transfer simp

lemma of_rat_add: "of_rat (a + b) = of_rat a + of_rat b"
  by transfer (simp add: add_frac_eq)

lemma of_rat_minus: "of_rat (- a) = - of_rat a"
  by transfer simp

lemma of_rat_neg_one [simp]: "of_rat (- 1) = - 1"
  by (simp add: of_rat_minus)

lemma of_rat_diff: "of_rat (a - b) = of_rat a - of_rat b"
  using of_rat_add [of a "- b"] by (simp add: of_rat_minus)

lemma of_rat_mult: "of_rat (a * b) = of_rat a * of_rat b"
  by transfer (simp add: divide_inverse nonzero_inverse_mult_distrib ac_simps)

lemma of_rat_sum: "of_rat (\<Sum>a\<in>A. f a) = (\<Sum>a\<in>A. of_rat (f a))"
  by (induct rule: infinite_finite_induct) (auto simp: of_rat_add)

lemma of_rat_prod: "of_rat (\<Prod>a\<in>A. f a) = (\<Prod>a\<in>A. of_rat (f a))"
  by (induct rule: infinite_finite_induct) (auto simp: of_rat_mult)

lemma nonzero_of_rat_inverse: "a \<noteq> 0 \<Longrightarrow> of_rat (inverse a) = inverse (of_rat a)"
  by (rule inverse_unique [symmetric]) (simp add: of_rat_mult [symmetric])

lemma of_rat_inverse: "(of_rat (inverse a) :: 'a::field_char_0) = inverse (of_rat a)"
  by (cases "a = 0") (simp_all add: nonzero_of_rat_inverse)

lemma nonzero_of_rat_divide: "b \<noteq> 0 \<Longrightarrow> of_rat (a / b) = of_rat a / of_rat b"
  by (simp add: divide_inverse of_rat_mult nonzero_of_rat_inverse)

lemma of_rat_divide: "(of_rat (a / b) :: 'a::field_char_0) = of_rat a / of_rat b"
  by (cases "b = 0") (simp_all add: nonzero_of_rat_divide)

lemma of_rat_power: "(of_rat (a ^ n) :: 'a::field_char_0) = of_rat a ^ n"
  by (induct n) (simp_all add: of_rat_mult)

lemma of_rat_eq_iff [simp]: "of_rat a = of_rat b \<longleftrightarrow> a = b"
  apply transfer
  apply (simp add: nonzero_divide_eq_eq nonzero_eq_divide_eq flip: of_int_mult)
  done

lemma of_rat_eq_0_iff [simp]: "of_rat a = 0 \<longleftrightarrow> a = 0"
  using of_rat_eq_iff [of _ 0] by simp

lemma zero_eq_of_rat_iff [simp]: "0 = of_rat a \<longleftrightarrow> 0 = a"
  by simp

lemma of_rat_eq_1_iff [simp]: "of_rat a = 1 \<longleftrightarrow> a = 1"
  using of_rat_eq_iff [of _ 1] by simp

lemma one_eq_of_rat_iff [simp]: "1 = of_rat a \<longleftrightarrow> 1 = a"
  by simp

lemma of_rat_less: "(of_rat r :: 'a::linordered_field) < of_rat s \<longleftrightarrow> r < s"
proof (induct r, induct s)
  fix a b c d :: int
  assume not_zero: "b > 0" "d > 0"
  then have "b * d > 0" by simp
  have of_int_divide_less_eq:
    "(of_int a :: 'a) / of_int b < of_int c / of_int d \<longleftrightarrow>
      (of_int a :: 'a) * of_int d < of_int c * of_int b"
    using not_zero by (simp add: pos_less_divide_eq pos_divide_less_eq)
  show "(of_rat (Fract a b) :: 'a::linordered_field) < of_rat (Fract c d) \<longleftrightarrow>
      Fract a b < Fract c d"
    using not_zero \<open>b * d > 0\<close>
    by (simp add: of_rat_rat of_int_divide_less_eq of_int_mult [symmetric] del: of_int_mult)
qed

lemma of_rat_less_eq: "(of_rat r :: 'a::linordered_field) \<le> of_rat s \<longleftrightarrow> r \<le> s"
  unfolding le_less by (auto simp add: of_rat_less)

lemma of_rat_le_0_iff [simp]: "(of_rat r :: 'a::linordered_field) \<le> 0 \<longleftrightarrow> r \<le> 0"
  using of_rat_less_eq [of r 0, where 'a = 'a] by simp

lemma zero_le_of_rat_iff [simp]: "0 \<le> (of_rat r :: 'a::linordered_field) \<longleftrightarrow> 0 \<le> r"
  using of_rat_less_eq [of 0 r, where 'a = 'a] by simp

lemma of_rat_le_1_iff [simp]: "(of_rat r :: 'a::linordered_field) \<le> 1 \<longleftrightarrow> r \<le> 1"
  using of_rat_less_eq [of r 1] by simp

lemma one_le_of_rat_iff [simp]: "1 \<le> (of_rat r :: 'a::linordered_field) \<longleftrightarrow> 1 \<le> r"
  using of_rat_less_eq [of 1 r] by simp

lemma of_rat_less_0_iff [simp]: "(of_rat r :: 'a::linordered_field) < 0 \<longleftrightarrow> r < 0"
  using of_rat_less [of r 0, where 'a = 'a] by simp

lemma zero_less_of_rat_iff [simp]: "0 < (of_rat r :: 'a::linordered_field) \<longleftrightarrow> 0 < r"
  using of_rat_less [of 0 r, where 'a = 'a] by simp

lemma of_rat_less_1_iff [simp]: "(of_rat r :: 'a::linordered_field) < 1 \<longleftrightarrow> r < 1"
  using of_rat_less [of r 1] by simp

lemma one_less_of_rat_iff [simp]: "1 < (of_rat r :: 'a::linordered_field) \<longleftrightarrow> 1 < r"
  using of_rat_less [of 1 r] by simp

lemma of_rat_eq_id [simp]: "of_rat = id"
proof
  show "of_rat a = id a" for a
    by (induct a) (simp add: of_rat_rat Fract_of_int_eq [symmetric])
qed

lemma abs_of_rat [simp]:
  "\<bar>of_rat r\<bar> = (of_rat \<bar>r\<bar> :: 'a :: linordered_field)"
  by (cases "r \<ge> 0") (simp_all add: not_le of_rat_minus)

text \<open>Collapse nested embeddings.\<close>
lemma of_rat_of_nat_eq [simp]: "of_rat (of_nat n) = of_nat n"
  by (induct n) (simp_all add: of_rat_add)

lemma of_rat_of_int_eq [simp]: "of_rat (of_int z) = of_int z"
  by (cases z rule: int_diff_cases) (simp add: of_rat_diff)

lemma of_rat_numeral_eq [simp]: "of_rat (numeral w) = numeral w"
  using of_rat_of_int_eq [of "numeral w"] by simp

lemma of_rat_neg_numeral_eq [simp]: "of_rat (- numeral w) = - numeral w"
  using of_rat_of_int_eq [of "- numeral w"] by simp

lemma of_rat_floor [simp]:
  "\<lfloor>of_rat r\<rfloor> = \<lfloor>r\<rfloor>"
  by (cases r) (simp add: Fract_of_int_quotient of_rat_divide floor_divide_of_int_eq)

lemma of_rat_ceiling [simp]:
  "\<lceil>of_rat r\<rceil> = \<lceil>r\<rceil>"
  using of_rat_floor [of "- r"] by (simp add: of_rat_minus ceiling_def)

lemmas zero_rat = Zero_rat_def
lemmas one_rat = One_rat_def

abbreviation rat_of_nat :: "nat \<Rightarrow> rat"
  where "rat_of_nat \<equiv> of_nat"

abbreviation rat_of_int :: "int \<Rightarrow> rat"
  where "rat_of_int \<equiv> of_int"


subsection \<open>The Set of Rational Numbers\<close>

context field_char_0
begin

definition Rats :: "'a set" ("\<rat>")
  where "\<rat> = range of_rat"

end

lemma Rats_cases [cases set: Rats]:
  assumes "q \<in> \<rat>"
  obtains (of_rat) r where "q = of_rat r"
proof -
  from \<open>q \<in> \<rat>\<close> have "q \<in> range of_rat"
    by (simp only: Rats_def)
  then obtain r where "q = of_rat r" ..
  then show thesis ..
qed

lemma Rats_of_rat [simp]: "of_rat r \<in> \<rat>"
  by (simp add: Rats_def)

lemma Rats_of_int [simp]: "of_int z \<in> \<rat>"
  by (subst of_rat_of_int_eq [symmetric]) (rule Rats_of_rat)

lemma Ints_subset_Rats: "\<int> \<subseteq> \<rat>"
  using Ints_cases Rats_of_int by blast

lemma Rats_of_nat [simp]: "of_nat n \<in> \<rat>"
  by (subst of_rat_of_nat_eq [symmetric]) (rule Rats_of_rat)

lemma Nats_subset_Rats: "\<nat> \<subseteq> \<rat>"
  using Ints_subset_Rats Nats_subset_Ints by blast

lemma Rats_number_of [simp]: "numeral w \<in> \<rat>"
  by (subst of_rat_numeral_eq [symmetric]) (rule Rats_of_rat)

lemma Rats_0 [simp]: "0 \<in> \<rat>"
  unfolding Rats_def by (rule range_eqI) (rule of_rat_0 [symmetric])

lemma Rats_1 [simp]: "1 \<in> \<rat>"
  unfolding Rats_def by (rule range_eqI) (rule of_rat_1 [symmetric])

lemma Rats_add [simp]: "a \<in> \<rat> \<Longrightarrow> b \<in> \<rat> \<Longrightarrow> a + b \<in> \<rat>"
  by (metis Rats_cases Rats_of_rat of_rat_add)

lemma Rats_minus_iff [simp]: "- a \<in> \<rat> \<longleftrightarrow> a \<in> \<rat>"
  by (metis Rats_cases Rats_of_rat add.inverse_inverse of_rat_minus)

lemma Rats_diff [simp]: "a \<in> \<rat> \<Longrightarrow> b \<in> \<rat> \<Longrightarrow> a - b \<in> \<rat>"
  by (metis Rats_add Rats_minus_iff diff_conv_add_uminus)

lemma Rats_mult [simp]: "a \<in> \<rat> \<Longrightarrow> b \<in> \<rat> \<Longrightarrow> a * b \<in> \<rat>"
  by (metis Rats_cases Rats_of_rat of_rat_mult)

lemma Rats_inverse [simp]: "a \<in> \<rat> \<Longrightarrow> inverse a \<in> \<rat>"
  for a :: "'a::field_char_0"
  by (metis Rats_cases Rats_of_rat of_rat_inverse)

lemma Rats_divide [simp]: "a \<in> \<rat> \<Longrightarrow> b \<in> \<rat> \<Longrightarrow> a / b \<in> \<rat>"
  for a b :: "'a::field_char_0"
  by (simp add: divide_inverse)

lemma Rats_power [simp]: "a \<in> \<rat> \<Longrightarrow> a ^ n \<in> \<rat>"
  for a :: "'a::field_char_0"
  by (metis Rats_cases Rats_of_rat of_rat_power)

lemma Rats_induct [case_names of_rat, induct set: Rats]: "q \<in> \<rat> \<Longrightarrow> (\<And>r. P (of_rat r)) \<Longrightarrow> P q"
  by (rule Rats_cases) auto

lemma Rats_infinite: "\<not> finite \<rat>"
  by (auto dest!: finite_imageD simp: inj_on_def infinite_UNIV_char_0 Rats_def)


subsection \<open>Implementation of rational numbers as pairs of integers\<close>

text \<open>Formal constructor\<close>

definition Frct :: "int \<times> int \<Rightarrow> rat"
  where [simp]: "Frct p = Fract (fst p) (snd p)"

lemma [code abstype]: "Frct (quotient_of q) = q"
  by (cases q) (auto intro: quotient_of_eq)


text \<open>Numerals\<close>

declare quotient_of_Fract [code abstract]

definition of_int :: "int \<Rightarrow> rat"
  where [code_abbrev]: "of_int = Int.of_int"

hide_const (open) of_int

lemma quotient_of_int [code abstract]: "quotient_of (Rat.of_int a) = (a, 1)"
  by (simp add: of_int_def of_int_rat quotient_of_Fract)

lemma [code_unfold]: "numeral k = Rat.of_int (numeral k)"
  by (simp add: Rat.of_int_def)

lemma [code_unfold]: "- numeral k = Rat.of_int (- numeral k)"
  by (simp add: Rat.of_int_def)

lemma Frct_code_post [code_post]:
  "Frct (0, a) = 0"
  "Frct (a, 0) = 0"
  "Frct (1, 1) = 1"
  "Frct (numeral k, 1) = numeral k"
  "Frct (1, numeral k) = 1 / numeral k"
  "Frct (numeral k, numeral l) = numeral k / numeral l"
  "Frct (- a, b) = - Frct (a, b)"
  "Frct (a, - b) = - Frct (a, b)"
  "- (- Frct q) = Frct q"
  by (simp_all add: Fract_of_int_quotient)


text \<open>Operations\<close>

lemma rat_zero_code [code abstract]: "quotient_of 0 = (0, 1)"
  by (simp add: Zero_rat_def quotient_of_Fract normalize_def)

lemma rat_one_code [code abstract]: "quotient_of 1 = (1, 1)"
  by (simp add: One_rat_def quotient_of_Fract normalize_def)

lemma rat_plus_code [code abstract]:
  "quotient_of (p + q) = (let (a, c) = quotient_of p; (b, d) = quotient_of q
     in normalize (a * d + b * c, c * d))"
  by (cases p, cases q) (simp add: quotient_of_Fract)

lemma rat_uminus_code [code abstract]:
  "quotient_of (- p) = (let (a, b) = quotient_of p in (- a, b))"
  by (cases p) (simp add: quotient_of_Fract)

lemma rat_minus_code [code abstract]:
  "quotient_of (p - q) =
    (let (a, c) = quotient_of p; (b, d) = quotient_of q
     in normalize (a * d - b * c, c * d))"
  by (cases p, cases q) (simp add: quotient_of_Fract)

lemma rat_times_code [code abstract]:
  "quotient_of (p * q) =
    (let (a, c) = quotient_of p; (b, d) = quotient_of q
     in normalize (a * b, c * d))"
  by (cases p, cases q) (simp add: quotient_of_Fract)

lemma rat_inverse_code [code abstract]:
  "quotient_of (inverse p) =
    (let (a, b) = quotient_of p
     in if a = 0 then (0, 1) else (sgn a * b, \<bar>a\<bar>))"
proof (cases p)
  case (Fract a b)
  then show ?thesis
    by (cases "0::int" a rule: linorder_cases) (simp_all add: quotient_of_Fract ac_simps)
qed

lemma rat_divide_code [code abstract]:
  "quotient_of (p / q) =
    (let (a, c) = quotient_of p; (b, d) = quotient_of q
     in normalize (a * d, c * b))"
  by (cases p, cases q) (simp add: quotient_of_Fract)

lemma rat_abs_code [code abstract]:
  "quotient_of \<bar>p\<bar> = (let (a, b) = quotient_of p in (\<bar>a\<bar>, b))"
  by (cases p) (simp add: quotient_of_Fract)
  
lemma rat_sgn_code [code abstract]: "quotient_of (sgn p) = (sgn (fst (quotient_of p)), 1)"
proof (cases p)
  case (Fract a b)
  then show ?thesis
    by (cases "0::int" a rule: linorder_cases) (simp_all add: quotient_of_Fract)
qed

lemma rat_floor_code [code]: "\<lfloor>p\<rfloor> = (let (a, b) = quotient_of p in a div b)"
  by (cases p) (simp add: quotient_of_Fract floor_Fract)

instantiation rat :: equal
begin

definition [code]: "HOL.equal a b \<longleftrightarrow> quotient_of a = quotient_of b"

instance
  by standard (simp add: equal_rat_def quotient_of_inject_eq)

lemma rat_eq_refl [code nbe]: "HOL.equal (r::rat) r \<longleftrightarrow> True"
  by (rule equal_refl)

end

lemma rat_less_eq_code [code]:
  "p \<le> q \<longleftrightarrow> (let (a, c) = quotient_of p; (b, d) = quotient_of q in a * d \<le> c * b)"
  by (cases p, cases q) (simp add: quotient_of_Fract mult.commute)

lemma rat_less_code [code]:
  "p < q \<longleftrightarrow> (let (a, c) = quotient_of p; (b, d) = quotient_of q in a * d < c * b)"
  by (cases p, cases q) (simp add: quotient_of_Fract mult.commute)

lemma [code]: "of_rat p = (let (a, b) = quotient_of p in of_int a / of_int b)"
  by (cases p) (simp add: quotient_of_Fract of_rat_rat)


text \<open>Quickcheck\<close>

context
  includes term_syntax
begin

definition
  valterm_fract :: "int \<times> (unit \<Rightarrow> Code_Evaluation.term) \<Rightarrow>
    int \<times> (unit \<Rightarrow> Code_Evaluation.term) \<Rightarrow>
    rat \<times> (unit \<Rightarrow> Code_Evaluation.term)"
  where [code_unfold]: "valterm_fract k l = Code_Evaluation.valtermify Fract {\<cdot>} k {\<cdot>} l"

end

instantiation rat :: random
begin

context
  includes state_combinator_syntax
begin

definition
  "Quickcheck_Random.random i =
    Quickcheck_Random.random i \<circ>\<rightarrow> (\<lambda>num. Random.range i \<circ>\<rightarrow> (\<lambda>denom. Pair
      (let j = int_of_integer (integer_of_natural (denom + 1))
       in valterm_fract num (j, \<lambda>u. Code_Evaluation.term_of j))))"

instance ..

end

end

instantiation rat :: exhaustive
begin

definition
  "exhaustive_rat f d =
    Quickcheck_Exhaustive.exhaustive
      (\<lambda>l. Quickcheck_Exhaustive.exhaustive
        (\<lambda>k. f (Fract k (int_of_integer (integer_of_natural l) + 1))) d) d"

instance ..

end

instantiation rat :: full_exhaustive
begin

definition
  "full_exhaustive_rat f d =
    Quickcheck_Exhaustive.full_exhaustive
      (\<lambda>(l, _). Quickcheck_Exhaustive.full_exhaustive
        (\<lambda>k. f
          (let j = int_of_integer (integer_of_natural l) + 1
           in valterm_fract k (j, \<lambda>_. Code_Evaluation.term_of j))) d) d"

instance ..

end

instance rat :: partial_term_of ..

lemma [code]:
  "partial_term_of (ty :: rat itself) (Quickcheck_Narrowing.Narrowing_variable p tt) \<equiv>
    Code_Evaluation.Free (STR ''_'') (Typerep.Typerep (STR ''Rat.rat'') [])"
  "partial_term_of (ty :: rat itself) (Quickcheck_Narrowing.Narrowing_constructor 0 [l, k]) \<equiv>
    Code_Evaluation.App
      (Code_Evaluation.Const (STR ''Rat.Frct'')
        (Typerep.Typerep (STR ''fun'')
          [Typerep.Typerep (STR ''Product_Type.prod'')
           [Typerep.Typerep (STR ''Int.int'') [], Typerep.Typerep (STR ''Int.int'') []],
           Typerep.Typerep (STR ''Rat.rat'') []]))
      (Code_Evaluation.App
        (Code_Evaluation.App
          (Code_Evaluation.Const (STR ''Product_Type.Pair'')
            (Typerep.Typerep (STR ''fun'')
              [Typerep.Typerep (STR ''Int.int'') [],
               Typerep.Typerep (STR ''fun'')
                [Typerep.Typerep (STR ''Int.int'') [],
                 Typerep.Typerep (STR ''Product_Type.prod'')
                 [Typerep.Typerep (STR ''Int.int'') [], Typerep.Typerep (STR ''Int.int'') []]]]))
          (partial_term_of (TYPE(int)) l)) (partial_term_of (TYPE(int)) k))"
  by (rule partial_term_of_anything)+

instantiation rat :: narrowing
begin

definition
  "narrowing =
    Quickcheck_Narrowing.apply
      (Quickcheck_Narrowing.apply
        (Quickcheck_Narrowing.cons (\<lambda>nom denom. Fract nom denom)) narrowing) narrowing"

instance ..

end


subsection \<open>Setup for Nitpick\<close>

declaration \<open>
  Nitpick_HOL.register_frac_type \<^type_name>\<open>rat\<close>
    [(\<^const_name>\<open>Abs_Rat\<close>, \<^const_name>\<open>Nitpick.Abs_Frac\<close>),
     (\<^const_name>\<open>zero_rat_inst.zero_rat\<close>, \<^const_name>\<open>Nitpick.zero_frac\<close>),
     (\<^const_name>\<open>one_rat_inst.one_rat\<close>, \<^const_name>\<open>Nitpick.one_frac\<close>),
     (\<^const_name>\<open>plus_rat_inst.plus_rat\<close>, \<^const_name>\<open>Nitpick.plus_frac\<close>),
     (\<^const_name>\<open>times_rat_inst.times_rat\<close>, \<^const_name>\<open>Nitpick.times_frac\<close>),
     (\<^const_name>\<open>uminus_rat_inst.uminus_rat\<close>, \<^const_name>\<open>Nitpick.uminus_frac\<close>),
     (\<^const_name>\<open>inverse_rat_inst.inverse_rat\<close>, \<^const_name>\<open>Nitpick.inverse_frac\<close>),
     (\<^const_name>\<open>ord_rat_inst.less_rat\<close>, \<^const_name>\<open>Nitpick.less_frac\<close>),
     (\<^const_name>\<open>ord_rat_inst.less_eq_rat\<close>, \<^const_name>\<open>Nitpick.less_eq_frac\<close>),
     (\<^const_name>\<open>field_char_0_class.of_rat\<close>, \<^const_name>\<open>Nitpick.of_frac\<close>)]
\<close>

lemmas [nitpick_unfold] =
  inverse_rat_inst.inverse_rat
  one_rat_inst.one_rat ord_rat_inst.less_rat
  ord_rat_inst.less_eq_rat plus_rat_inst.plus_rat times_rat_inst.times_rat
  uminus_rat_inst.uminus_rat zero_rat_inst.zero_rat


subsection \<open>Float syntax\<close>

syntax "_Float" :: "float_const \<Rightarrow> 'a"    ("_")

parse_translation \<open>
  let
    fun mk_frac str =
      let
        val {mant = i, exp = n} = Lexicon.read_float str;
        val exp = Syntax.const \<^const_syntax>\<open>Power.power\<close>;
        val ten = Numeral.mk_number_syntax 10;
        val exp10 = if n = 1 then ten else exp $ ten $ Numeral.mk_number_syntax n;
      in Syntax.const \<^const_syntax>\<open>Fields.inverse_divide\<close> $ Numeral.mk_number_syntax i $ exp10 end;

    fun float_tr [(c as Const (\<^syntax_const>\<open>_constrain\<close>, _)) $ t $ u] = c $ float_tr [t] $ u
      | float_tr [t as Const (str, _)] = mk_frac str
      | float_tr ts = raise TERM ("float_tr", ts);
  in [(\<^syntax_const>\<open>_Float\<close>, K float_tr)] end
\<close>

text\<open>Test:\<close>
lemma "123.456 = -111.111 + 200 + 30 + 4 + 5/10 + 6/100 + (7/1000::rat)"
  by simp


subsection \<open>Hiding implementation details\<close>

hide_const (open) normalize positive

lifting_update rat.lifting
lifting_forget rat.lifting

end
