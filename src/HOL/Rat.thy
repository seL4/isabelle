(*  Title:  HOL/Rat.thy
    Author: Markus Wenzel, TU Muenchen
*)

header {* Rational numbers *}

theory Rat
imports GCD Archimedean_Field
uses ("Tools/float_syntax.ML")
begin

subsection {* Rational numbers as quotient *}

subsubsection {* Construction of the type of rational numbers *}

definition
  ratrel :: "((int \<times> int) \<times> (int \<times> int)) set" where
  "ratrel = {(x, y). snd x \<noteq> 0 \<and> snd y \<noteq> 0 \<and> fst x * snd y = fst y * snd x}"

lemma ratrel_iff [simp]:
  "(x, y) \<in> ratrel \<longleftrightarrow> snd x \<noteq> 0 \<and> snd y \<noteq> 0 \<and> fst x * snd y = fst y * snd x"
  by (simp add: ratrel_def)

lemma refl_on_ratrel: "refl_on {x. snd x \<noteq> 0} ratrel"
  by (auto simp add: refl_on_def ratrel_def)

lemma sym_ratrel: "sym ratrel"
  by (simp add: ratrel_def sym_def)

lemma trans_ratrel: "trans ratrel"
proof (rule transI, unfold split_paired_all)
  fix a b a' b' a'' b'' :: int
  assume A: "((a, b), (a', b')) \<in> ratrel"
  assume B: "((a', b'), (a'', b'')) \<in> ratrel"
  have "b' * (a * b'') = b'' * (a * b')" by simp
  also from A have "a * b' = a' * b" by auto
  also have "b'' * (a' * b) = b * (a' * b'')" by simp
  also from B have "a' * b'' = a'' * b'" by auto
  also have "b * (a'' * b') = b' * (a'' * b)" by simp
  finally have "b' * (a * b'') = b' * (a'' * b)" .
  moreover from B have "b' \<noteq> 0" by auto
  ultimately have "a * b'' = a'' * b" by simp
  with A B show "((a, b), (a'', b'')) \<in> ratrel" by auto
qed
  
lemma equiv_ratrel: "equiv {x. snd x \<noteq> 0} ratrel"
  by (rule equivI [OF refl_on_ratrel sym_ratrel trans_ratrel])

lemmas UN_ratrel = UN_equiv_class [OF equiv_ratrel]
lemmas UN_ratrel2 = UN_equiv_class2 [OF equiv_ratrel equiv_ratrel]

lemma equiv_ratrel_iff [iff]: 
  assumes "snd x \<noteq> 0" and "snd y \<noteq> 0"
  shows "ratrel `` {x} = ratrel `` {y} \<longleftrightarrow> (x, y) \<in> ratrel"
  by (rule eq_equiv_class_iff, rule equiv_ratrel) (auto simp add: assms)

definition "Rat = {x. snd x \<noteq> 0} // ratrel"

typedef (open) rat = Rat
  morphisms Rep_Rat Abs_Rat
  unfolding Rat_def
proof
  have "(0::int, 1::int) \<in> {x. snd x \<noteq> 0}" by simp
  then show "ratrel `` {(0, 1)} \<in> {x. snd x \<noteq> 0} // ratrel" by (rule quotientI)
qed

lemma ratrel_in_Rat [simp]: "snd x \<noteq> 0 \<Longrightarrow> ratrel `` {x} \<in> Rat"
  by (simp add: Rat_def quotientI)

declare Abs_Rat_inject [simp] Abs_Rat_inverse [simp]


subsubsection {* Representation and basic operations *}

definition
  Fract :: "int \<Rightarrow> int \<Rightarrow> rat" where
  "Fract a b = Abs_Rat (ratrel `` {if b = 0 then (0, 1) else (a, b)})"

lemma eq_rat:
  shows "\<And>a b c d. b \<noteq> 0 \<Longrightarrow> d \<noteq> 0 \<Longrightarrow> Fract a b = Fract c d \<longleftrightarrow> a * d = c * b"
  and "\<And>a. Fract a 0 = Fract 0 1"
  and "\<And>a c. Fract 0 a = Fract 0 c"
  by (simp_all add: Fract_def)

lemma Rat_cases [case_names Fract, cases type: rat]:
  assumes "\<And>a b. q = Fract a b \<Longrightarrow> b > 0 \<Longrightarrow> coprime a b \<Longrightarrow> C"
  shows C
proof -
  obtain a b :: int where "q = Fract a b" and "b \<noteq> 0"
    by (cases q) (clarsimp simp add: Fract_def Rat_def quotient_def)
  let ?a = "a div gcd a b"
  let ?b = "b div gcd a b"
  from `b \<noteq> 0` have "?b * gcd a b = b"
    by (simp add: dvd_div_mult_self)
  with `b \<noteq> 0` have "?b \<noteq> 0" by auto
  from `q = Fract a b` `b \<noteq> 0` `?b \<noteq> 0` have q: "q = Fract ?a ?b"
    by (simp add: eq_rat dvd_div_mult mult_commute [of a])
  from `b \<noteq> 0` have coprime: "coprime ?a ?b"
    by (auto intro: div_gcd_coprime_int)
  show C proof (cases "b > 0")
    case True
    note assms
    moreover note q
    moreover from True have "?b > 0" by (simp add: nonneg1_imp_zdiv_pos_iff)
    moreover note coprime
    ultimately show C .
  next
    case False
    note assms
    moreover from q have "q = Fract (- ?a) (- ?b)" by (simp add: Fract_def)
    moreover from False `b \<noteq> 0` have "- ?b > 0" by (simp add: pos_imp_zdiv_neg_iff)
    moreover from coprime have "coprime (- ?a) (- ?b)" by simp
    ultimately show C .
  qed
qed

lemma Rat_induct [case_names Fract, induct type: rat]:
  assumes "\<And>a b. b > 0 \<Longrightarrow> coprime a b \<Longrightarrow> P (Fract a b)"
  shows "P q"
  using assms by (cases q) simp

instantiation rat :: comm_ring_1
begin

definition
  Zero_rat_def: "0 = Fract 0 1"

definition
  One_rat_def: "1 = Fract 1 1"

definition
  add_rat_def:
  "q + r = Abs_Rat (\<Union>x \<in> Rep_Rat q. \<Union>y \<in> Rep_Rat r.
    ratrel `` {(fst x * snd y + fst y * snd x, snd x * snd y)})"

lemma add_rat [simp]:
  assumes "b \<noteq> 0" and "d \<noteq> 0"
  shows "Fract a b + Fract c d = Fract (a * d + c * b) (b * d)"
proof -
  have "(\<lambda>x y. ratrel``{(fst x * snd y + fst y * snd x, snd x * snd y)})
    respects2 ratrel"
  by (rule equiv_ratrel [THEN congruent2_commuteI]) (simp_all add: left_distrib)
  with assms show ?thesis by (simp add: Fract_def add_rat_def UN_ratrel2)
qed

definition
  minus_rat_def:
  "- q = Abs_Rat (\<Union>x \<in> Rep_Rat q. ratrel `` {(- fst x, snd x)})"

lemma minus_rat [simp]: "- Fract a b = Fract (- a) b"
proof -
  have "(\<lambda>x. ratrel `` {(- fst x, snd x)}) respects ratrel"
    by (simp add: congruent_def split_paired_all)
  then show ?thesis by (simp add: Fract_def minus_rat_def UN_ratrel)
qed

lemma minus_rat_cancel [simp]: "Fract (- a) (- b) = Fract a b"
  by (cases "b = 0") (simp_all add: eq_rat)

definition
  diff_rat_def: "q - r = q + - (r::rat)"

lemma diff_rat [simp]:
  assumes "b \<noteq> 0" and "d \<noteq> 0"
  shows "Fract a b - Fract c d = Fract (a * d - c * b) (b * d)"
  using assms by (simp add: diff_rat_def)

definition
  mult_rat_def:
  "q * r = Abs_Rat (\<Union>x \<in> Rep_Rat q. \<Union>y \<in> Rep_Rat r.
    ratrel``{(fst x * fst y, snd x * snd y)})"

lemma mult_rat [simp]: "Fract a b * Fract c d = Fract (a * c) (b * d)"
proof -
  have "(\<lambda>x y. ratrel `` {(fst x * fst y, snd x * snd y)}) respects2 ratrel"
    by (rule equiv_ratrel [THEN congruent2_commuteI]) simp_all
  then show ?thesis by (simp add: Fract_def mult_rat_def UN_ratrel2)
qed

lemma mult_rat_cancel:
  assumes "c \<noteq> 0"
  shows "Fract (c * a) (c * b) = Fract a b"
proof -
  from assms have "Fract c c = Fract 1 1" by (simp add: Fract_def)
  then show ?thesis by (simp add: mult_rat [symmetric])
qed

instance proof
  fix q r s :: rat show "(q * r) * s = q * (r * s)" 
    by (cases q, cases r, cases s) (simp add: eq_rat)
next
  fix q r :: rat show "q * r = r * q"
    by (cases q, cases r) (simp add: eq_rat)
next
  fix q :: rat show "1 * q = q"
    by (cases q) (simp add: One_rat_def eq_rat)
next
  fix q r s :: rat show "(q + r) + s = q + (r + s)"
    by (cases q, cases r, cases s) (simp add: eq_rat algebra_simps)
next
  fix q r :: rat show "q + r = r + q"
    by (cases q, cases r) (simp add: eq_rat)
next
  fix q :: rat show "0 + q = q"
    by (cases q) (simp add: Zero_rat_def eq_rat)
next
  fix q :: rat show "- q + q = 0"
    by (cases q) (simp add: Zero_rat_def eq_rat)
next
  fix q r :: rat show "q - r = q + - r"
    by (cases q, cases r) (simp add: eq_rat)
next
  fix q r s :: rat show "(q + r) * s = q * s + r * s"
    by (cases q, cases r, cases s) (simp add: eq_rat algebra_simps)
next
  show "(0::rat) \<noteq> 1" by (simp add: Zero_rat_def One_rat_def eq_rat)
qed

end

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
  "Fract (neg_numeral w) 1 = neg_numeral w"
  "Fract k 0 = 0"
  using Fract_of_int_eq [of "numeral w"]
  using Fract_of_int_eq [of "neg_numeral w"]
  by (simp_all add: Zero_rat_def One_rat_def eq_rat)

lemma rat_number_expand:
  "0 = Fract 0 1"
  "1 = Fract 1 1"
  "numeral k = Fract (numeral k) 1"
  "neg_numeral k = Fract (neg_numeral k) 1"
  by (simp_all add: rat_number_collapse)

lemma Rat_cases_nonzero [case_names Fract 0]:
  assumes Fract: "\<And>a b. q = Fract a b \<Longrightarrow> b > 0 \<Longrightarrow> a \<noteq> 0 \<Longrightarrow> coprime a b \<Longrightarrow> C"
  assumes 0: "q = 0 \<Longrightarrow> C"
  shows C
proof (cases "q = 0")
  case True then show C using 0 by auto
next
  case False
  then obtain a b where "q = Fract a b" and "b > 0" and "coprime a b" by (cases q) auto
  moreover with False have "0 \<noteq> Fract a b" by simp
  with `b > 0` have "a \<noteq> 0" by (simp add: Zero_rat_def eq_rat)
  with Fract `q = Fract a b` `b > 0` `coprime a b` show C by blast
qed

subsubsection {* Function @{text normalize} *}

lemma Fract_coprime: "Fract (a div gcd a b) (b div gcd a b) = Fract a b"
proof (cases "b = 0")
  case True then show ?thesis by (simp add: eq_rat)
next
  case False
  moreover have "b div gcd a b * gcd a b = b"
    by (rule dvd_div_mult_self) simp
  ultimately have "b div gcd a b \<noteq> 0" by auto
  with False show ?thesis by (simp add: eq_rat dvd_div_mult mult_commute [of a])
qed

definition normalize :: "int \<times> int \<Rightarrow> int \<times> int" where
  "normalize p = (if snd p > 0 then (let a = gcd (fst p) (snd p) in (fst p div a, snd p div a))
    else if snd p = 0 then (0, 1)
    else (let a = - gcd (fst p) (snd p) in (fst p div a, snd p div a)))"

lemma normalize_crossproduct:
  assumes "q \<noteq> 0" "s \<noteq> 0"
  assumes "normalize (p, q) = normalize (r, s)"
  shows "p * s = r * q"
proof -
  have aux: "p * gcd r s = sgn (q * s) * r * gcd p q \<Longrightarrow> q * gcd r s = sgn (q * s) * s * gcd p q \<Longrightarrow> p * s = q * r"
  proof -
    assume "p * gcd r s = sgn (q * s) * r * gcd p q" and "q * gcd r s = sgn (q * s) * s * gcd p q"
    then have "(p * gcd r s) * (sgn (q * s) * s * gcd p q) = (q * gcd r s) * (sgn (q * s) * r * gcd p q)" by simp
    with assms show "p * s = q * r" by (auto simp add: mult_ac sgn_times sgn_0_0)
  qed
  from assms show ?thesis
    by (auto simp add: normalize_def Let_def dvd_div_div_eq_mult mult_commute sgn_times split: if_splits intro: aux)
qed

lemma normalize_eq: "normalize (a, b) = (p, q) \<Longrightarrow> Fract p q = Fract a b"
  by (auto simp add: normalize_def Let_def Fract_coprime dvd_div_neg rat_number_collapse
    split:split_if_asm)

lemma normalize_denom_pos: "normalize r = (p, q) \<Longrightarrow> q > 0"
  by (auto simp add: normalize_def Let_def dvd_div_neg pos_imp_zdiv_neg_iff nonneg1_imp_zdiv_pos_iff
    split:split_if_asm)

lemma normalize_coprime: "normalize r = (p, q) \<Longrightarrow> coprime p q"
  by (auto simp add: normalize_def Let_def dvd_div_neg div_gcd_coprime_int
    split:split_if_asm)

lemma normalize_stable [simp]:
  "q > 0 \<Longrightarrow> coprime p q \<Longrightarrow> normalize (p, q) = (p, q)"
  by (simp add: normalize_def)

lemma normalize_denom_zero [simp]:
  "normalize (p, 0) = (0, 1)"
  by (simp add: normalize_def)

lemma normalize_negative [simp]:
  "q < 0 \<Longrightarrow> normalize (p, q) = normalize (- p, - q)"
  by (simp add: normalize_def Let_def dvd_div_neg dvd_neg_div)

text{*
  Decompose a fraction into normalized, i.e. coprime numerator and denominator:
*}

definition quotient_of :: "rat \<Rightarrow> int \<times> int" where
  "quotient_of x = (THE pair. x = Fract (fst pair) (snd pair) &
                   snd pair > 0 & coprime (fst pair) (snd pair))"

lemma quotient_of_unique:
  "\<exists>!p. r = Fract (fst p) (snd p) \<and> snd p > 0 \<and> coprime (fst p) (snd p)"
proof (cases r)
  case (Fract a b)
  then have "r = Fract (fst (a, b)) (snd (a, b)) \<and> snd (a, b) > 0 \<and> coprime (fst (a, b)) (snd (a, b))" by auto
  then show ?thesis proof (rule ex1I)
    fix p
    obtain c d :: int where p: "p = (c, d)" by (cases p)
    assume "r = Fract (fst p) (snd p) \<and> snd p > 0 \<and> coprime (fst p) (snd p)"
    with p have Fract': "r = Fract c d" "d > 0" "coprime c d" by simp_all
    have "c = a \<and> d = b"
    proof (cases "a = 0")
      case True with Fract Fract' show ?thesis by (simp add: eq_rat)
    next
      case False
      with Fract Fract' have *: "c * b = a * d" and "c \<noteq> 0" by (auto simp add: eq_rat)
      then have "c * b > 0 \<longleftrightarrow> a * d > 0" by auto
      with `b > 0` `d > 0` have "a > 0 \<longleftrightarrow> c > 0" by (simp add: zero_less_mult_iff)
      with `a \<noteq> 0` `c \<noteq> 0` have sgn: "sgn a = sgn c" by (auto simp add: not_less)
      from `coprime a b` `coprime c d` have "\<bar>a\<bar> * \<bar>d\<bar> = \<bar>c\<bar> * \<bar>b\<bar> \<longleftrightarrow> \<bar>a\<bar> = \<bar>c\<bar> \<and> \<bar>d\<bar> = \<bar>b\<bar>"
        by (simp add: coprime_crossproduct_int)
      with `b > 0` `d > 0` have "\<bar>a\<bar> * d = \<bar>c\<bar> * b \<longleftrightarrow> \<bar>a\<bar> = \<bar>c\<bar> \<and> d = b" by simp
      then have "a * sgn a * d = c * sgn c * b \<longleftrightarrow> a * sgn a = c * sgn c \<and> d = b" by (simp add: abs_sgn)
      with sgn * show ?thesis by (auto simp add: sgn_0_0)
    qed
    with p show "p = (a, b)" by simp
  qed
qed

lemma quotient_of_Fract [code]:
  "quotient_of (Fract a b) = normalize (a, b)"
proof -
  have "Fract a b = Fract (fst (normalize (a, b))) (snd (normalize (a, b)))" (is ?Fract)
    by (rule sym) (auto intro: normalize_eq)
  moreover have "0 < snd (normalize (a, b))" (is ?denom_pos) 
    by (cases "normalize (a, b)") (rule normalize_denom_pos, simp)
  moreover have "coprime (fst (normalize (a, b))) (snd (normalize (a, b)))" (is ?coprime)
    by (rule normalize_coprime) simp
  ultimately have "?Fract \<and> ?denom_pos \<and> ?coprime" by blast
  with quotient_of_unique have
    "(THE p. Fract a b = Fract (fst p) (snd p) \<and> 0 < snd p \<and> coprime (fst p) (snd p)) = normalize (a, b)"
    by (rule the1_equality)
  then show ?thesis by (simp add: quotient_of_def)
qed

lemma quotient_of_number [simp]:
  "quotient_of 0 = (0, 1)"
  "quotient_of 1 = (1, 1)"
  "quotient_of (numeral k) = (numeral k, 1)"
  "quotient_of (neg_numeral k) = (neg_numeral k, 1)"
  by (simp_all add: rat_number_expand quotient_of_Fract)

lemma quotient_of_eq: "quotient_of (Fract a b) = (p, q) \<Longrightarrow> Fract p q = Fract a b"
  by (simp add: quotient_of_Fract normalize_eq)

lemma quotient_of_denom_pos: "quotient_of r = (p, q) \<Longrightarrow> q > 0"
  by (cases r) (simp add: quotient_of_Fract normalize_denom_pos)

lemma quotient_of_coprime: "quotient_of r = (p, q) \<Longrightarrow> coprime p q"
  by (cases r) (simp add: quotient_of_Fract normalize_coprime)

lemma quotient_of_inject:
  assumes "quotient_of a = quotient_of b"
  shows "a = b"
proof -
  obtain p q r s where a: "a = Fract p q"
    and b: "b = Fract r s"
    and "q > 0" and "s > 0" by (cases a, cases b)
  with assms show ?thesis by (simp add: eq_rat quotient_of_Fract normalize_crossproduct)
qed

lemma quotient_of_inject_eq:
  "quotient_of a = quotient_of b \<longleftrightarrow> a = b"
  by (auto simp add: quotient_of_inject)


subsubsection {* The field of rational numbers *}

instantiation rat :: field_inverse_zero
begin

definition
  inverse_rat_def:
  "inverse q = Abs_Rat (\<Union>x \<in> Rep_Rat q.
     ratrel `` {if fst x = 0 then (0, 1) else (snd x, fst x)})"

lemma inverse_rat [simp]: "inverse (Fract a b) = Fract b a"
proof -
  have "(\<lambda>x. ratrel `` {if fst x = 0 then (0, 1) else (snd x, fst x)}) respects ratrel"
    by (auto simp add: congruent_def mult_commute)
  then show ?thesis by (simp add: Fract_def inverse_rat_def UN_ratrel)
qed

definition
  divide_rat_def: "q / r = q * inverse (r::rat)"

lemma divide_rat [simp]: "Fract a b / Fract c d = Fract (a * d) (b * c)"
  by (simp add: divide_rat_def)

instance proof
  fix q :: rat
  assume "q \<noteq> 0"
  then show "inverse q * q = 1" by (cases q rule: Rat_cases_nonzero)
   (simp_all add: rat_number_expand eq_rat)
next
  fix q r :: rat
  show "q / r = q * inverse r" by (simp add: divide_rat_def)
next
  show "inverse 0 = (0::rat)" by (simp add: rat_number_expand, simp add: rat_number_collapse)
qed

end


subsubsection {* Various *}

lemma Fract_of_int_quotient: "Fract k l = of_int k / of_int l"
  by (simp add: Fract_of_int_eq [symmetric])

lemma Fract_add_one: "n \<noteq> 0 ==> Fract (m + n) n = Fract m n + 1"
  by (simp add: rat_number_expand)


subsubsection {* The ordered field of rational numbers *}

instantiation rat :: linorder
begin

definition
  le_rat_def:
   "q \<le> r \<longleftrightarrow> the_elem (\<Union>x \<in> Rep_Rat q. \<Union>y \<in> Rep_Rat r.
      {(fst x * snd y) * (snd x * snd y) \<le> (fst y * snd x) * (snd x * snd y)})"

lemma le_rat [simp]:
  assumes "b \<noteq> 0" and "d \<noteq> 0"
  shows "Fract a b \<le> Fract c d \<longleftrightarrow> (a * d) * (b * d) \<le> (c * b) * (b * d)"
proof -
  have "(\<lambda>x y. {(fst x * snd y) * (snd x * snd y) \<le> (fst y * snd x) * (snd x * snd y)})
    respects2 ratrel"
  proof (clarsimp simp add: congruent2_def)
    fix a b a' b' c d c' d'::int
    assume neq: "b \<noteq> 0"  "b' \<noteq> 0"  "d \<noteq> 0"  "d' \<noteq> 0"
    assume eq1: "a * b' = a' * b"
    assume eq2: "c * d' = c' * d"

    let ?le = "\<lambda>a b c d. ((a * d) * (b * d) \<le> (c * b) * (b * d))"
    {
      fix a b c d x :: int assume x: "x \<noteq> 0"
      have "?le a b c d = ?le (a * x) (b * x) c d"
      proof -
        from x have "0 < x * x" by (auto simp add: zero_less_mult_iff)
        hence "?le a b c d =
            ((a * d) * (b * d) * (x * x) \<le> (c * b) * (b * d) * (x * x))"
          by (simp add: mult_le_cancel_right)
        also have "... = ?le (a * x) (b * x) c d"
          by (simp add: mult_ac)
        finally show ?thesis .
      qed
    } note le_factor = this

    let ?D = "b * d" and ?D' = "b' * d'"
    from neq have D: "?D \<noteq> 0" by simp
    from neq have "?D' \<noteq> 0" by simp
    hence "?le a b c d = ?le (a * ?D') (b * ?D') c d"
      by (rule le_factor)
    also have "... = ((a * b') * ?D * ?D' * d * d' \<le> (c * d') * ?D * ?D' * b * b')" 
      by (simp add: mult_ac)
    also have "... = ((a' * b) * ?D * ?D' * d * d' \<le> (c' * d) * ?D * ?D' * b * b')"
      by (simp only: eq1 eq2)
    also have "... = ?le (a' * ?D) (b' * ?D) c' d'"
      by (simp add: mult_ac)
    also from D have "... = ?le a' b' c' d'"
      by (rule le_factor [symmetric])
    finally show "?le a b c d = ?le a' b' c' d'" .
  qed
  with assms show ?thesis by (simp add: Fract_def le_rat_def UN_ratrel2)
qed

definition
  less_rat_def: "z < (w::rat) \<longleftrightarrow> z \<le> w \<and> z \<noteq> w"

lemma less_rat [simp]:
  assumes "b \<noteq> 0" and "d \<noteq> 0"
  shows "Fract a b < Fract c d \<longleftrightarrow> (a * d) * (b * d) < (c * b) * (b * d)"
  using assms by (simp add: less_rat_def eq_rat order_less_le)

instance proof
  fix q r s :: rat
  {
    assume "q \<le> r" and "r \<le> s"
    then show "q \<le> s" 
    proof (induct q, induct r, induct s)
      fix a b c d e f :: int
      assume neq: "b > 0"  "d > 0"  "f > 0"
      assume 1: "Fract a b \<le> Fract c d" and 2: "Fract c d \<le> Fract e f"
      show "Fract a b \<le> Fract e f"
      proof -
        from neq obtain bb: "0 < b * b" and dd: "0 < d * d" and ff: "0 < f * f"
          by (auto simp add: zero_less_mult_iff linorder_neq_iff)
        have "(a * d) * (b * d) * (f * f) \<le> (c * b) * (b * d) * (f * f)"
        proof -
          from neq 1 have "(a * d) * (b * d) \<le> (c * b) * (b * d)"
            by simp
          with ff show ?thesis by (simp add: mult_le_cancel_right)
        qed
        also have "... = (c * f) * (d * f) * (b * b)" by algebra
        also have "... \<le> (e * d) * (d * f) * (b * b)"
        proof -
          from neq 2 have "(c * f) * (d * f) \<le> (e * d) * (d * f)"
            by simp
          with bb show ?thesis by (simp add: mult_le_cancel_right)
        qed
        finally have "(a * f) * (b * f) * (d * d) \<le> e * b * (b * f) * (d * d)"
          by (simp only: mult_ac)
        with dd have "(a * f) * (b * f) \<le> (e * b) * (b * f)"
          by (simp add: mult_le_cancel_right)
        with neq show ?thesis by simp
      qed
    qed
  next
    assume "q \<le> r" and "r \<le> q"
    then show "q = r"
    proof (induct q, induct r)
      fix a b c d :: int
      assume neq: "b > 0"  "d > 0"
      assume 1: "Fract a b \<le> Fract c d" and 2: "Fract c d \<le> Fract a b"
      show "Fract a b = Fract c d"
      proof -
        from neq 1 have "(a * d) * (b * d) \<le> (c * b) * (b * d)"
          by simp
        also have "... \<le> (a * d) * (b * d)"
        proof -
          from neq 2 have "(c * b) * (d * b) \<le> (a * d) * (d * b)"
            by simp
          thus ?thesis by (simp only: mult_ac)
        qed
        finally have "(a * d) * (b * d) = (c * b) * (b * d)" .
        moreover from neq have "b * d \<noteq> 0" by simp
        ultimately have "a * d = c * b" by simp
        with neq show ?thesis by (simp add: eq_rat)
      qed
    qed
  next
    show "q \<le> q"
      by (induct q) simp
    show "(q < r) = (q \<le> r \<and> \<not> r \<le> q)"
      by (induct q, induct r) (auto simp add: le_less mult_commute)
    show "q \<le> r \<or> r \<le> q"
      by (induct q, induct r)
         (simp add: mult_commute, rule linorder_linear)
  }
qed

end

instantiation rat :: "{distrib_lattice, abs_if, sgn_if}"
begin

definition
  abs_rat_def: "\<bar>q\<bar> = (if q < 0 then -q else (q::rat))"

lemma abs_rat [simp, code]: "\<bar>Fract a b\<bar> = Fract \<bar>a\<bar> \<bar>b\<bar>"
  by (auto simp add: abs_rat_def zabs_def Zero_rat_def not_less le_less eq_rat zero_less_mult_iff)

definition
  sgn_rat_def: "sgn (q::rat) = (if q = 0 then 0 else if 0 < q then 1 else - 1)"

lemma sgn_rat [simp, code]: "sgn (Fract a b) = of_int (sgn a * sgn b)"
  unfolding Fract_of_int_eq
  by (auto simp: zsgn_def sgn_rat_def Zero_rat_def eq_rat)
    (auto simp: rat_number_collapse not_less le_less zero_less_mult_iff)

definition
  "(inf \<Colon> rat \<Rightarrow> rat \<Rightarrow> rat) = min"

definition
  "(sup \<Colon> rat \<Rightarrow> rat \<Rightarrow> rat) = max"

instance by intro_classes
  (auto simp add: abs_rat_def sgn_rat_def min_max.sup_inf_distrib1 inf_rat_def sup_rat_def)

end

instance rat :: linordered_field_inverse_zero
proof
  fix q r s :: rat
  show "q \<le> r ==> s + q \<le> s + r"
  proof (induct q, induct r, induct s)
    fix a b c d e f :: int
    assume neq: "b > 0"  "d > 0"  "f > 0"
    assume le: "Fract a b \<le> Fract c d"
    show "Fract e f + Fract a b \<le> Fract e f + Fract c d"
    proof -
      let ?F = "f * f" from neq have F: "0 < ?F"
        by (auto simp add: zero_less_mult_iff)
      from neq le have "(a * d) * (b * d) \<le> (c * b) * (b * d)"
        by simp
      with F have "(a * d) * (b * d) * ?F * ?F \<le> (c * b) * (b * d) * ?F * ?F"
        by (simp add: mult_le_cancel_right)
      with neq show ?thesis by (simp add: mult_ac int_distrib)
    qed
  qed
  show "q < r ==> 0 < s ==> s * q < s * r"
  proof (induct q, induct r, induct s)
    fix a b c d e f :: int
    assume neq: "b > 0"  "d > 0"  "f > 0"
    assume le: "Fract a b < Fract c d"
    assume gt: "0 < Fract e f"
    show "Fract e f * Fract a b < Fract e f * Fract c d"
    proof -
      let ?E = "e * f" and ?F = "f * f"
      from neq gt have "0 < ?E"
        by (auto simp add: Zero_rat_def order_less_le eq_rat)
      moreover from neq have "0 < ?F"
        by (auto simp add: zero_less_mult_iff)
      moreover from neq le have "(a * d) * (b * d) < (c * b) * (b * d)"
        by simp
      ultimately have "(a * d) * (b * d) * ?E * ?F < (c * b) * (b * d) * ?E * ?F"
        by (simp add: mult_less_cancel_right)
      with neq show ?thesis
        by (simp add: mult_ac)
    qed
  qed
qed auto

lemma Rat_induct_pos [case_names Fract, induct type: rat]:
  assumes step: "\<And>a b. 0 < b \<Longrightarrow> P (Fract a b)"
  shows "P q"
proof (cases q)
  have step': "\<And>a b. b < 0 \<Longrightarrow> P (Fract a b)"
  proof -
    fix a::int and b::int
    assume b: "b < 0"
    hence "0 < -b" by simp
    hence "P (Fract (-a) (-b))" by (rule step)
    thus "P (Fract a b)" by (simp add: order_less_imp_not_eq [OF b])
  qed
  case (Fract a b)
  thus "P q" by (force simp add: linorder_neq_iff step step')
qed

lemma zero_less_Fract_iff:
  "0 < b \<Longrightarrow> 0 < Fract a b \<longleftrightarrow> 0 < a"
  by (simp add: Zero_rat_def zero_less_mult_iff)

lemma Fract_less_zero_iff:
  "0 < b \<Longrightarrow> Fract a b < 0 \<longleftrightarrow> a < 0"
  by (simp add: Zero_rat_def mult_less_0_iff)

lemma zero_le_Fract_iff:
  "0 < b \<Longrightarrow> 0 \<le> Fract a b \<longleftrightarrow> 0 \<le> a"
  by (simp add: Zero_rat_def zero_le_mult_iff)

lemma Fract_le_zero_iff:
  "0 < b \<Longrightarrow> Fract a b \<le> 0 \<longleftrightarrow> a \<le> 0"
  by (simp add: Zero_rat_def mult_le_0_iff)

lemma one_less_Fract_iff:
  "0 < b \<Longrightarrow> 1 < Fract a b \<longleftrightarrow> b < a"
  by (simp add: One_rat_def mult_less_cancel_right_disj)

lemma Fract_less_one_iff:
  "0 < b \<Longrightarrow> Fract a b < 1 \<longleftrightarrow> a < b"
  by (simp add: One_rat_def mult_less_cancel_right_disj)

lemma one_le_Fract_iff:
  "0 < b \<Longrightarrow> 1 \<le> Fract a b \<longleftrightarrow> b \<le> a"
  by (simp add: One_rat_def mult_le_cancel_right)

lemma Fract_le_one_iff:
  "0 < b \<Longrightarrow> Fract a b \<le> 1 \<longleftrightarrow> a \<le> b"
  by (simp add: One_rat_def mult_le_cancel_right)


subsubsection {* Rationals are an Archimedean field *}

lemma rat_floor_lemma:
  shows "of_int (a div b) \<le> Fract a b \<and> Fract a b < of_int (a div b + 1)"
proof -
  have "Fract a b = of_int (a div b) + Fract (a mod b) b"
    by (cases "b = 0", simp, simp add: of_int_rat)
  moreover have "0 \<le> Fract (a mod b) b \<and> Fract (a mod b) b < 1"
    unfolding Fract_of_int_quotient
    by (rule linorder_cases [of b 0]) (simp add: divide_nonpos_neg, simp, simp add: divide_nonneg_pos)
  ultimately show ?thesis by simp
qed

instance rat :: archimedean_field
proof
  fix r :: rat
  show "\<exists>z. r \<le> of_int z"
  proof (induct r)
    case (Fract a b)
    have "Fract a b \<le> of_int (a div b + 1)"
      using rat_floor_lemma [of a b] by simp
    then show "\<exists>z. Fract a b \<le> of_int z" ..
  qed
qed

instantiation rat :: floor_ceiling
begin

definition [code del]:
  "floor (x::rat) = (THE z. of_int z \<le> x \<and> x < of_int (z + 1))"

instance proof
  fix x :: rat
  show "of_int (floor x) \<le> x \<and> x < of_int (floor x + 1)"
    unfolding floor_rat_def using floor_exists1 by (rule theI')
qed

end

lemma floor_Fract: "floor (Fract a b) = a div b"
  using rat_floor_lemma [of a b]
  by (simp add: floor_unique)


subsection {* Linear arithmetic setup *}

declaration {*
  K (Lin_Arith.add_inj_thms [@{thm of_nat_le_iff} RS iffD2, @{thm of_nat_eq_iff} RS iffD2]
    (* not needed because x < (y::nat) can be rewritten as Suc x <= y: of_nat_less_iff RS iffD2 *)
  #> Lin_Arith.add_inj_thms [@{thm of_int_le_iff} RS iffD2, @{thm of_int_eq_iff} RS iffD2]
    (* not needed because x < (y::int) can be rewritten as x + 1 <= y: of_int_less_iff RS iffD2 *)
  #> Lin_Arith.add_simps [@{thm neg_less_iff_less},
      @{thm True_implies_equals},
      read_instantiate @{context} [(("a", 0), "(numeral ?v)")] @{thm right_distrib},
      read_instantiate @{context} [(("a", 0), "(neg_numeral ?v)")] @{thm right_distrib},
      @{thm divide_1}, @{thm divide_zero_left},
      @{thm times_divide_eq_right}, @{thm times_divide_eq_left},
      @{thm minus_divide_left} RS sym, @{thm minus_divide_right} RS sym,
      @{thm of_int_minus}, @{thm of_int_diff},
      @{thm of_int_of_nat_eq}]
  #> Lin_Arith.add_simprocs Numeral_Simprocs.field_cancel_numeral_factors
  #> Lin_Arith.add_inj_const (@{const_name of_nat}, @{typ "nat => rat"})
  #> Lin_Arith.add_inj_const (@{const_name of_int}, @{typ "int => rat"}))
*}


subsection {* Embedding from Rationals to other Fields *}

class field_char_0 = field + ring_char_0

subclass (in linordered_field) field_char_0 ..

context field_char_0
begin

definition of_rat :: "rat \<Rightarrow> 'a" where
  "of_rat q = the_elem (\<Union>(a,b) \<in> Rep_Rat q. {of_int a / of_int b})"

end

lemma of_rat_congruent:
  "(\<lambda>(a, b). {of_int a / of_int b :: 'a::field_char_0}) respects ratrel"
apply (rule congruentI)
apply (clarsimp simp add: nonzero_divide_eq_eq nonzero_eq_divide_eq)
apply (simp only: of_int_mult [symmetric])
done

lemma of_rat_rat: "b \<noteq> 0 \<Longrightarrow> of_rat (Fract a b) = of_int a / of_int b"
  unfolding Fract_def of_rat_def by (simp add: UN_ratrel of_rat_congruent)

lemma of_rat_0 [simp]: "of_rat 0 = 0"
by (simp add: Zero_rat_def of_rat_rat)

lemma of_rat_1 [simp]: "of_rat 1 = 1"
by (simp add: One_rat_def of_rat_rat)

lemma of_rat_add: "of_rat (a + b) = of_rat a + of_rat b"
by (induct a, induct b, simp add: of_rat_rat add_frac_eq)

lemma of_rat_minus: "of_rat (- a) = - of_rat a"
by (induct a, simp add: of_rat_rat)

lemma of_rat_diff: "of_rat (a - b) = of_rat a - of_rat b"
by (simp only: diff_minus of_rat_add of_rat_minus)

lemma of_rat_mult: "of_rat (a * b) = of_rat a * of_rat b"
apply (induct a, induct b, simp add: of_rat_rat)
apply (simp add: divide_inverse nonzero_inverse_mult_distrib mult_ac)
done

lemma nonzero_of_rat_inverse:
  "a \<noteq> 0 \<Longrightarrow> of_rat (inverse a) = inverse (of_rat a)"
apply (rule inverse_unique [symmetric])
apply (simp add: of_rat_mult [symmetric])
done

lemma of_rat_inverse:
  "(of_rat (inverse a)::'a::{field_char_0, field_inverse_zero}) =
   inverse (of_rat a)"
by (cases "a = 0", simp_all add: nonzero_of_rat_inverse)

lemma nonzero_of_rat_divide:
  "b \<noteq> 0 \<Longrightarrow> of_rat (a / b) = of_rat a / of_rat b"
by (simp add: divide_inverse of_rat_mult nonzero_of_rat_inverse)

lemma of_rat_divide:
  "(of_rat (a / b)::'a::{field_char_0, field_inverse_zero})
   = of_rat a / of_rat b"
by (cases "b = 0") (simp_all add: nonzero_of_rat_divide)

lemma of_rat_power:
  "(of_rat (a ^ n)::'a::field_char_0) = of_rat a ^ n"
by (induct n) (simp_all add: of_rat_mult)

lemma of_rat_eq_iff [simp]: "(of_rat a = of_rat b) = (a = b)"
apply (induct a, induct b)
apply (simp add: of_rat_rat eq_rat)
apply (simp add: nonzero_divide_eq_eq nonzero_eq_divide_eq)
apply (simp only: of_int_mult [symmetric] of_int_eq_iff)
done

lemma of_rat_less:
  "(of_rat r :: 'a::linordered_field) < of_rat s \<longleftrightarrow> r < s"
proof (induct r, induct s)
  fix a b c d :: int
  assume not_zero: "b > 0" "d > 0"
  then have "b * d > 0" by (rule mult_pos_pos)
  have of_int_divide_less_eq:
    "(of_int a :: 'a) / of_int b < of_int c / of_int d
      \<longleftrightarrow> (of_int a :: 'a) * of_int d < of_int c * of_int b"
    using not_zero by (simp add: pos_less_divide_eq pos_divide_less_eq)
  show "(of_rat (Fract a b) :: 'a::linordered_field) < of_rat (Fract c d)
    \<longleftrightarrow> Fract a b < Fract c d"
    using not_zero `b * d > 0`
    by (simp add: of_rat_rat of_int_divide_less_eq of_int_mult [symmetric] del: of_int_mult)
qed

lemma of_rat_less_eq:
  "(of_rat r :: 'a::linordered_field) \<le> of_rat s \<longleftrightarrow> r \<le> s"
  unfolding le_less by (auto simp add: of_rat_less)

lemmas of_rat_eq_0_iff [simp] = of_rat_eq_iff [of _ 0, simplified]

lemma of_rat_eq_id [simp]: "of_rat = id"
proof
  fix a
  show "of_rat a = id a"
  by (induct a)
     (simp add: of_rat_rat Fract_of_int_eq [symmetric])
qed

text{*Collapse nested embeddings*}
lemma of_rat_of_nat_eq [simp]: "of_rat (of_nat n) = of_nat n"
by (induct n) (simp_all add: of_rat_add)

lemma of_rat_of_int_eq [simp]: "of_rat (of_int z) = of_int z"
by (cases z rule: int_diff_cases) (simp add: of_rat_diff)

lemma of_rat_numeral_eq [simp]:
  "of_rat (numeral w) = numeral w"
using of_rat_of_int_eq [of "numeral w"] by simp

lemma of_rat_neg_numeral_eq [simp]:
  "of_rat (neg_numeral w) = neg_numeral w"
using of_rat_of_int_eq [of "neg_numeral w"] by simp

lemmas zero_rat = Zero_rat_def
lemmas one_rat = One_rat_def

abbreviation
  rat_of_nat :: "nat \<Rightarrow> rat"
where
  "rat_of_nat \<equiv> of_nat"

abbreviation
  rat_of_int :: "int \<Rightarrow> rat"
where
  "rat_of_int \<equiv> of_int"

subsection {* The Set of Rational Numbers *}

context field_char_0
begin

definition
  Rats  :: "'a set" where
  "Rats = range of_rat"

notation (xsymbols)
  Rats  ("\<rat>")

end

lemma Rats_of_rat [simp]: "of_rat r \<in> Rats"
by (simp add: Rats_def)

lemma Rats_of_int [simp]: "of_int z \<in> Rats"
by (subst of_rat_of_int_eq [symmetric], rule Rats_of_rat)

lemma Rats_of_nat [simp]: "of_nat n \<in> Rats"
by (subst of_rat_of_nat_eq [symmetric], rule Rats_of_rat)

lemma Rats_number_of [simp]: "numeral w \<in> Rats"
by (subst of_rat_numeral_eq [symmetric], rule Rats_of_rat)

lemma Rats_neg_number_of [simp]: "neg_numeral w \<in> Rats"
by (subst of_rat_neg_numeral_eq [symmetric], rule Rats_of_rat)

lemma Rats_0 [simp]: "0 \<in> Rats"
apply (unfold Rats_def)
apply (rule range_eqI)
apply (rule of_rat_0 [symmetric])
done

lemma Rats_1 [simp]: "1 \<in> Rats"
apply (unfold Rats_def)
apply (rule range_eqI)
apply (rule of_rat_1 [symmetric])
done

lemma Rats_add [simp]: "\<lbrakk>a \<in> Rats; b \<in> Rats\<rbrakk> \<Longrightarrow> a + b \<in> Rats"
apply (auto simp add: Rats_def)
apply (rule range_eqI)
apply (rule of_rat_add [symmetric])
done

lemma Rats_minus [simp]: "a \<in> Rats \<Longrightarrow> - a \<in> Rats"
apply (auto simp add: Rats_def)
apply (rule range_eqI)
apply (rule of_rat_minus [symmetric])
done

lemma Rats_diff [simp]: "\<lbrakk>a \<in> Rats; b \<in> Rats\<rbrakk> \<Longrightarrow> a - b \<in> Rats"
apply (auto simp add: Rats_def)
apply (rule range_eqI)
apply (rule of_rat_diff [symmetric])
done

lemma Rats_mult [simp]: "\<lbrakk>a \<in> Rats; b \<in> Rats\<rbrakk> \<Longrightarrow> a * b \<in> Rats"
apply (auto simp add: Rats_def)
apply (rule range_eqI)
apply (rule of_rat_mult [symmetric])
done

lemma nonzero_Rats_inverse:
  fixes a :: "'a::field_char_0"
  shows "\<lbrakk>a \<in> Rats; a \<noteq> 0\<rbrakk> \<Longrightarrow> inverse a \<in> Rats"
apply (auto simp add: Rats_def)
apply (rule range_eqI)
apply (erule nonzero_of_rat_inverse [symmetric])
done

lemma Rats_inverse [simp]:
  fixes a :: "'a::{field_char_0, field_inverse_zero}"
  shows "a \<in> Rats \<Longrightarrow> inverse a \<in> Rats"
apply (auto simp add: Rats_def)
apply (rule range_eqI)
apply (rule of_rat_inverse [symmetric])
done

lemma nonzero_Rats_divide:
  fixes a b :: "'a::field_char_0"
  shows "\<lbrakk>a \<in> Rats; b \<in> Rats; b \<noteq> 0\<rbrakk> \<Longrightarrow> a / b \<in> Rats"
apply (auto simp add: Rats_def)
apply (rule range_eqI)
apply (erule nonzero_of_rat_divide [symmetric])
done

lemma Rats_divide [simp]:
  fixes a b :: "'a::{field_char_0, field_inverse_zero}"
  shows "\<lbrakk>a \<in> Rats; b \<in> Rats\<rbrakk> \<Longrightarrow> a / b \<in> Rats"
apply (auto simp add: Rats_def)
apply (rule range_eqI)
apply (rule of_rat_divide [symmetric])
done

lemma Rats_power [simp]:
  fixes a :: "'a::field_char_0"
  shows "a \<in> Rats \<Longrightarrow> a ^ n \<in> Rats"
apply (auto simp add: Rats_def)
apply (rule range_eqI)
apply (rule of_rat_power [symmetric])
done

lemma Rats_cases [cases set: Rats]:
  assumes "q \<in> \<rat>"
  obtains (of_rat) r where "q = of_rat r"
  unfolding Rats_def
proof -
  from `q \<in> \<rat>` have "q \<in> range of_rat" unfolding Rats_def .
  then obtain r where "q = of_rat r" ..
  then show thesis ..
qed

lemma Rats_induct [case_names of_rat, induct set: Rats]:
  "q \<in> \<rat> \<Longrightarrow> (\<And>r. P (of_rat r)) \<Longrightarrow> P q"
  by (rule Rats_cases) auto


subsection {* Implementation of rational numbers as pairs of integers *}

text {* Formal constructor *}

definition Frct :: "int \<times> int \<Rightarrow> rat" where
  [simp]: "Frct p = Fract (fst p) (snd p)"

lemma [code abstype]:
  "Frct (quotient_of q) = q"
  by (cases q) (auto intro: quotient_of_eq)


text {* Numerals *}

declare quotient_of_Fract [code abstract]

definition of_int :: "int \<Rightarrow> rat"
where
  [code_abbrev]: "of_int = Int.of_int"
hide_const (open) of_int

lemma quotient_of_int [code abstract]:
  "quotient_of (Rat.of_int a) = (a, 1)"
  by (simp add: of_int_def of_int_rat quotient_of_Fract)

lemma [code_unfold]:
  "numeral k = Rat.of_int (numeral k)"
  by (simp add: Rat.of_int_def)

lemma [code_unfold]:
  "neg_numeral k = Rat.of_int (neg_numeral k)"
  by (simp add: Rat.of_int_def)

lemma Frct_code_post [code_post]:
  "Frct (0, a) = 0"
  "Frct (a, 0) = 0"
  "Frct (1, 1) = 1"
  "Frct (numeral k, 1) = numeral k"
  "Frct (neg_numeral k, 1) = neg_numeral k"
  "Frct (1, numeral k) = 1 / numeral k"
  "Frct (1, neg_numeral k) = 1 / neg_numeral k"
  "Frct (numeral k, numeral l) = numeral k / numeral l"
  "Frct (numeral k, neg_numeral l) = numeral k / neg_numeral l"
  "Frct (neg_numeral k, numeral l) = neg_numeral k / numeral l"
  "Frct (neg_numeral k, neg_numeral l) = neg_numeral k / neg_numeral l"
  by (simp_all add: Fract_of_int_quotient)


text {* Operations *}

lemma rat_zero_code [code abstract]:
  "quotient_of 0 = (0, 1)"
  by (simp add: Zero_rat_def quotient_of_Fract normalize_def)

lemma rat_one_code [code abstract]:
  "quotient_of 1 = (1, 1)"
  by (simp add: One_rat_def quotient_of_Fract normalize_def)

lemma rat_plus_code [code abstract]:
  "quotient_of (p + q) = (let (a, c) = quotient_of p; (b, d) = quotient_of q
     in normalize (a * d + b * c, c * d))"
  by (cases p, cases q) (simp add: quotient_of_Fract)

lemma rat_uminus_code [code abstract]:
  "quotient_of (- p) = (let (a, b) = quotient_of p in (- a, b))"
  by (cases p) (simp add: quotient_of_Fract)

lemma rat_minus_code [code abstract]:
  "quotient_of (p - q) = (let (a, c) = quotient_of p; (b, d) = quotient_of q
     in normalize (a * d - b * c, c * d))"
  by (cases p, cases q) (simp add: quotient_of_Fract)

lemma rat_times_code [code abstract]:
  "quotient_of (p * q) = (let (a, c) = quotient_of p; (b, d) = quotient_of q
     in normalize (a * b, c * d))"
  by (cases p, cases q) (simp add: quotient_of_Fract)

lemma rat_inverse_code [code abstract]:
  "quotient_of (inverse p) = (let (a, b) = quotient_of p
    in if a = 0 then (0, 1) else (sgn a * b, \<bar>a\<bar>))"
proof (cases p)
  case (Fract a b) then show ?thesis
    by (cases "0::int" a rule: linorder_cases) (simp_all add: quotient_of_Fract gcd_int.commute)
qed

lemma rat_divide_code [code abstract]:
  "quotient_of (p / q) = (let (a, c) = quotient_of p; (b, d) = quotient_of q
     in normalize (a * d, c * b))"
  by (cases p, cases q) (simp add: quotient_of_Fract)

lemma rat_abs_code [code abstract]:
  "quotient_of \<bar>p\<bar> = (let (a, b) = quotient_of p in (\<bar>a\<bar>, b))"
  by (cases p) (simp add: quotient_of_Fract)

lemma rat_sgn_code [code abstract]:
  "quotient_of (sgn p) = (sgn (fst (quotient_of p)), 1)"
proof (cases p)
  case (Fract a b) then show ?thesis
  by (cases "0::int" a rule: linorder_cases) (simp_all add: quotient_of_Fract)
qed

lemma rat_floor_code [code]:
  "floor p = (let (a, b) = quotient_of p in a div b)"
by (cases p) (simp add: quotient_of_Fract floor_Fract)

instantiation rat :: equal
begin

definition [code]:
  "HOL.equal a b \<longleftrightarrow> quotient_of a = quotient_of b"

instance proof
qed (simp add: equal_rat_def quotient_of_inject_eq)

lemma rat_eq_refl [code nbe]:
  "HOL.equal (r::rat) r \<longleftrightarrow> True"
  by (rule equal_refl)

end

lemma rat_less_eq_code [code]:
  "p \<le> q \<longleftrightarrow> (let (a, c) = quotient_of p; (b, d) = quotient_of q in a * d \<le> c * b)"
  by (cases p, cases q) (simp add: quotient_of_Fract mult.commute)

lemma rat_less_code [code]:
  "p < q \<longleftrightarrow> (let (a, c) = quotient_of p; (b, d) = quotient_of q in a * d < c * b)"
  by (cases p, cases q) (simp add: quotient_of_Fract mult.commute)

lemma [code]:
  "of_rat p = (let (a, b) = quotient_of p in of_int a / of_int b)"
  by (cases p) (simp add: quotient_of_Fract of_rat_rat)


text {* Quickcheck *}

definition (in term_syntax)
  valterm_fract :: "int \<times> (unit \<Rightarrow> Code_Evaluation.term) \<Rightarrow> int \<times> (unit \<Rightarrow> Code_Evaluation.term) \<Rightarrow> rat \<times> (unit \<Rightarrow> Code_Evaluation.term)" where
  [code_unfold]: "valterm_fract k l = Code_Evaluation.valtermify Fract {\<cdot>} k {\<cdot>} l"

notation fcomp (infixl "\<circ>>" 60)
notation scomp (infixl "\<circ>\<rightarrow>" 60)

instantiation rat :: random
begin

definition
  "Quickcheck.random i = Quickcheck.random i \<circ>\<rightarrow> (\<lambda>num. Random.range i \<circ>\<rightarrow> (\<lambda>denom. Pair (
     let j = Code_Numeral.int_of (denom + 1)
     in valterm_fract num (j, \<lambda>u. Code_Evaluation.term_of j))))"

instance ..

end

no_notation fcomp (infixl "\<circ>>" 60)
no_notation scomp (infixl "\<circ>\<rightarrow>" 60)

instantiation rat :: exhaustive
begin

definition
  "exhaustive_rat f d = Quickcheck_Exhaustive.exhaustive (%l. Quickcheck_Exhaustive.exhaustive (%k. f (Fract k (Code_Numeral.int_of l + 1))) d) d"

instance ..

end

instantiation rat :: full_exhaustive
begin

definition
  "full_exhaustive_rat f d = Quickcheck_Exhaustive.full_exhaustive (%(l, _). Quickcheck_Exhaustive.full_exhaustive (%k.
     f (let j = Code_Numeral.int_of l + 1
        in valterm_fract k (j, %_. Code_Evaluation.term_of j))) d) d"

instance ..

end

instantiation rat :: partial_term_of
begin

instance ..

end

lemma [code]:
  "partial_term_of (ty :: rat itself) (Quickcheck_Narrowing.Narrowing_variable p tt) == Code_Evaluation.Free (STR ''_'') (Typerep.Typerep (STR ''Rat.rat'') [])"
  "partial_term_of (ty :: rat itself) (Quickcheck_Narrowing.Narrowing_constructor 0 [l, k]) ==
     Code_Evaluation.App (Code_Evaluation.Const (STR ''Rat.Frct'')
     (Typerep.Typerep (STR ''fun'') [Typerep.Typerep (STR ''Product_Type.prod'') [Typerep.Typerep (STR ''Int.int'') [], Typerep.Typerep (STR ''Int.int'') []],
        Typerep.Typerep (STR ''Rat.rat'') []])) (Code_Evaluation.App (Code_Evaluation.App (Code_Evaluation.Const (STR ''Product_Type.Pair'') (Typerep.Typerep (STR ''fun'') [Typerep.Typerep (STR ''Int.int'') [], Typerep.Typerep (STR ''fun'') [Typerep.Typerep (STR ''Int.int'') [], Typerep.Typerep (STR ''Product_Type.prod'') [Typerep.Typerep (STR ''Int.int'') [], Typerep.Typerep (STR ''Int.int'') []]]])) (partial_term_of (TYPE(int)) l)) (partial_term_of (TYPE(int)) k))"
by (rule partial_term_of_anything)+

instantiation rat :: narrowing
begin

definition
  "narrowing = Quickcheck_Narrowing.apply (Quickcheck_Narrowing.apply
    (Quickcheck_Narrowing.cons (%nom denom. Fract nom denom)) narrowing) narrowing"

instance ..

end


subsection {* Setup for Nitpick *}

declaration {*
  Nitpick_HOL.register_frac_type @{type_name rat}
   [(@{const_name zero_rat_inst.zero_rat}, @{const_name Nitpick.zero_frac}),
    (@{const_name one_rat_inst.one_rat}, @{const_name Nitpick.one_frac}),
    (@{const_name plus_rat_inst.plus_rat}, @{const_name Nitpick.plus_frac}),
    (@{const_name times_rat_inst.times_rat}, @{const_name Nitpick.times_frac}),
    (@{const_name uminus_rat_inst.uminus_rat}, @{const_name Nitpick.uminus_frac}),
    (@{const_name inverse_rat_inst.inverse_rat}, @{const_name Nitpick.inverse_frac}),
    (@{const_name ord_rat_inst.less_rat}, @{const_name Nitpick.less_frac}),
    (@{const_name ord_rat_inst.less_eq_rat}, @{const_name Nitpick.less_eq_frac}),
    (@{const_name field_char_0_class.of_rat}, @{const_name Nitpick.of_frac})]
*}

lemmas [nitpick_unfold] = inverse_rat_inst.inverse_rat
  one_rat_inst.one_rat ord_rat_inst.less_rat
  ord_rat_inst.less_eq_rat plus_rat_inst.plus_rat times_rat_inst.times_rat
  uminus_rat_inst.uminus_rat zero_rat_inst.zero_rat

subsection{* Float syntax *}

syntax "_Float" :: "float_const \<Rightarrow> 'a"    ("_")

use "Tools/float_syntax.ML"
setup Float_Syntax.setup

text{* Test: *}
lemma "123.456 = -111.111 + 200 + 30 + 4 + 5/10 + 6/100 + (7/1000::rat)"
by simp


hide_const (open) normalize

end
