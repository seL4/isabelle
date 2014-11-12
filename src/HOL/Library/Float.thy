(*  Title:      HOL/Library/Float.thy
    Author:     Johannes Hölzl, Fabian Immler
    Copyright   2012  TU München
*)

section {* Floating-Point Numbers *}

theory Float
imports Complex_Main Lattice_Algebras
begin

definition "float = {m * 2 powr e | (m :: int) (e :: int). True}"

typedef float = float
  morphisms real_of_float float_of
  unfolding float_def by auto

instantiation float :: real_of
begin

definition real_float :: "float \<Rightarrow> real" where
  real_of_float_def[code_unfold]: "real \<equiv> real_of_float"

instance ..
end

lemma type_definition_float': "type_definition real float_of float"
  using type_definition_float unfolding real_of_float_def .

setup_lifting (no_code) type_definition_float'

lemmas float_of_inject[simp]

declare [[coercion "real :: float \<Rightarrow> real"]]

lemma real_of_float_eq:
  fixes f1 f2 :: float shows "f1 = f2 \<longleftrightarrow> real f1 = real f2"
  unfolding real_of_float_def real_of_float_inject ..

lemma float_of_real[simp]: "float_of (real x) = x"
  unfolding real_of_float_def by (rule real_of_float_inverse)

lemma real_float[simp]: "x \<in> float \<Longrightarrow> real (float_of x) = x"
  unfolding real_of_float_def by (rule float_of_inverse)

subsection {* Real operations preserving the representation as floating point number *}

lemma floatI: fixes m e :: int shows "m * 2 powr e = x \<Longrightarrow> x \<in> float"
  by (auto simp: float_def)

lemma zero_float[simp]: "0 \<in> float" by (auto simp: float_def)
lemma one_float[simp]: "1 \<in> float" by (intro floatI[of 1 0]) simp
lemma numeral_float[simp]: "numeral i \<in> float" by (intro floatI[of "numeral i" 0]) simp
lemma neg_numeral_float[simp]: "- numeral i \<in> float" by (intro floatI[of "- numeral i" 0]) simp
lemma real_of_int_float[simp]: "real (x :: int) \<in> float" by (intro floatI[of x 0]) simp
lemma real_of_nat_float[simp]: "real (x :: nat) \<in> float" by (intro floatI[of x 0]) simp
lemma two_powr_int_float[simp]: "2 powr (real (i::int)) \<in> float" by (intro floatI[of 1 i]) simp
lemma two_powr_nat_float[simp]: "2 powr (real (i::nat)) \<in> float" by (intro floatI[of 1 i]) simp
lemma two_powr_minus_int_float[simp]: "2 powr - (real (i::int)) \<in> float" by (intro floatI[of 1 "-i"]) simp
lemma two_powr_minus_nat_float[simp]: "2 powr - (real (i::nat)) \<in> float" by (intro floatI[of 1 "-i"]) simp
lemma two_powr_numeral_float[simp]: "2 powr numeral i \<in> float" by (intro floatI[of 1 "numeral i"]) simp
lemma two_powr_neg_numeral_float[simp]: "2 powr - numeral i \<in> float" by (intro floatI[of 1 "- numeral i"]) simp
lemma two_pow_float[simp]: "2 ^ n \<in> float" by (intro floatI[of 1 "n"]) (simp add: powr_realpow)
lemma real_of_float_float[simp]: "real (f::float) \<in> float" by (cases f) simp

lemma plus_float[simp]: "r \<in> float \<Longrightarrow> p \<in> float \<Longrightarrow> r + p \<in> float"
  unfolding float_def
proof (safe, simp)
  fix e1 m1 e2 m2 :: int
  { fix e1 m1 e2 m2 :: int assume "e1 \<le> e2"
    then have "m1 * 2 powr e1 + m2 * 2 powr e2 = (m1 + m2 * 2 ^ nat (e2 - e1)) * 2 powr e1"
      by (simp add: powr_realpow[symmetric] powr_divide2[symmetric] field_simps)
    then have "\<exists>(m::int) (e::int). m1 * 2 powr e1 + m2 * 2 powr e2 = m * 2 powr e"
      by blast }
  note * = this
  show "\<exists>(m::int) (e::int). m1 * 2 powr e1 + m2 * 2 powr e2 = m * 2 powr e"
  proof (cases e1 e2 rule: linorder_le_cases)
    assume "e2 \<le> e1" from *[OF this, of m2 m1] show ?thesis by (simp add: ac_simps)
  qed (rule *)
qed

lemma uminus_float[simp]: "x \<in> float \<Longrightarrow> -x \<in> float"
  apply (auto simp: float_def)
  apply hypsubst_thin
  apply (rule_tac x="-x" in exI)
  apply (rule_tac x="xa" in exI)
  apply (simp add: field_simps)
  done

lemma times_float[simp]: "x \<in> float \<Longrightarrow> y \<in> float \<Longrightarrow> x * y \<in> float"
  apply (auto simp: float_def)
  apply hypsubst_thin
  apply (rule_tac x="x * xa" in exI)
  apply (rule_tac x="xb + xc" in exI)
  apply (simp add: powr_add)
  done

lemma minus_float[simp]: "x \<in> float \<Longrightarrow> y \<in> float \<Longrightarrow> x - y \<in> float"
  using plus_float [of x "- y"] by simp

lemma abs_float[simp]: "x \<in> float \<Longrightarrow> abs x \<in> float"
  by (cases x rule: linorder_cases[of 0]) auto

lemma sgn_of_float[simp]: "x \<in> float \<Longrightarrow> sgn x \<in> float"
  by (cases x rule: linorder_cases[of 0]) (auto intro!: uminus_float)

lemma div_power_2_float[simp]: "x \<in> float \<Longrightarrow> x / 2^d \<in> float"
  apply (auto simp add: float_def)
  apply hypsubst_thin
  apply (rule_tac x="x" in exI)
  apply (rule_tac x="xa - d" in exI)
  apply (simp add: powr_realpow[symmetric] field_simps powr_add[symmetric])
  done

lemma div_power_2_int_float[simp]: "x \<in> float \<Longrightarrow> x / (2::int)^d \<in> float"
  apply (auto simp add: float_def)
  apply hypsubst_thin
  apply (rule_tac x="x" in exI)
  apply (rule_tac x="xa - d" in exI)
  apply (simp add: powr_realpow[symmetric] field_simps powr_add[symmetric])
  done

lemma div_numeral_Bit0_float[simp]:
  assumes x: "x / numeral n \<in> float" shows "x / (numeral (Num.Bit0 n)) \<in> float"
proof -
  have "(x / numeral n) / 2^1 \<in> float"
    by (intro x div_power_2_float)
  also have "(x / numeral n) / 2^1 = x / (numeral (Num.Bit0 n))"
    by (induct n) auto
  finally show ?thesis .
qed

lemma div_neg_numeral_Bit0_float[simp]:
  assumes x: "x / numeral n \<in> float" shows "x / (- numeral (Num.Bit0 n)) \<in> float"
proof -
  have "- (x / numeral (Num.Bit0 n)) \<in> float" using x by simp
  also have "- (x / numeral (Num.Bit0 n)) = x / - numeral (Num.Bit0 n)"
    by simp
  finally show ?thesis .
qed

lemma power_float[simp]: assumes "a \<in> float" shows "a ^ b \<in> float"
proof -
  from assms obtain m e::int where "a = m * 2 powr e"
    by (auto simp: float_def)
  thus ?thesis
    by (auto intro!: floatI[where m="m^b" and e = "e*b"]
      simp: power_mult_distrib powr_realpow[symmetric] powr_powr)
qed

lift_definition Float :: "int \<Rightarrow> int \<Rightarrow> float" is "\<lambda>(m::int) (e::int). m * 2 powr e" by simp
declare Float.rep_eq[simp]

lemma compute_real_of_float[code]:
  "real_of_float (Float m e) = (if e \<ge> 0 then m * 2 ^ nat e else m / 2 ^ (nat (-e)))"
by (simp add: real_of_float_def[symmetric] powr_int)

code_datatype Float

subsection {* Arithmetic operations on floating point numbers *}

instantiation float :: "{ring_1, linorder, linordered_ring, linordered_idom, numeral, equal}"
begin

lift_definition zero_float :: float is 0 by simp
declare zero_float.rep_eq[simp]
lift_definition one_float :: float is 1 by simp
declare one_float.rep_eq[simp]
lift_definition plus_float :: "float \<Rightarrow> float \<Rightarrow> float" is "op +" by simp
declare plus_float.rep_eq[simp]
lift_definition times_float :: "float \<Rightarrow> float \<Rightarrow> float" is "op *" by simp
declare times_float.rep_eq[simp]
lift_definition minus_float :: "float \<Rightarrow> float \<Rightarrow> float" is "op -" by simp
declare minus_float.rep_eq[simp]
lift_definition uminus_float :: "float \<Rightarrow> float" is "uminus" by simp
declare uminus_float.rep_eq[simp]

lift_definition abs_float :: "float \<Rightarrow> float" is abs by simp
declare abs_float.rep_eq[simp]
lift_definition sgn_float :: "float \<Rightarrow> float" is sgn by simp
declare sgn_float.rep_eq[simp]

lift_definition equal_float :: "float \<Rightarrow> float \<Rightarrow> bool" is "op = :: real \<Rightarrow> real \<Rightarrow> bool" .

lift_definition less_eq_float :: "float \<Rightarrow> float \<Rightarrow> bool" is "op \<le>" .
declare less_eq_float.rep_eq[simp]
lift_definition less_float :: "float \<Rightarrow> float \<Rightarrow> bool" is "op <" .
declare less_float.rep_eq[simp]

instance
  proof qed (transfer, fastforce simp add: field_simps intro: mult_left_mono mult_right_mono)+
end

lemma Float_0_eq_0[simp]: "Float 0 e = 0"
  by transfer simp

lemma real_of_float_power[simp]: fixes f::float shows "real (f^n) = real f^n"
  by (induct n) simp_all

lemma fixes x y::float
  shows real_of_float_min: "real (min x y) = min (real x) (real y)"
    and real_of_float_max: "real (max x y) = max (real x) (real y)"
  by (simp_all add: min_def max_def)

instance float :: unbounded_dense_linorder
proof
  fix a b :: float
  show "\<exists>c. a < c"
    apply (intro exI[of _ "a + 1"])
    apply transfer
    apply simp
    done
  show "\<exists>c. c < a"
    apply (intro exI[of _ "a - 1"])
    apply transfer
    apply simp
    done
  assume "a < b"
  then show "\<exists>c. a < c \<and> c < b"
    apply (intro exI[of _ "(a + b) * Float 1 (- 1)"])
    apply transfer
    apply (simp add: powr_minus)
    done
qed

instantiation float :: lattice_ab_group_add
begin

definition inf_float::"float\<Rightarrow>float\<Rightarrow>float"
where "inf_float a b = min a b"

definition sup_float::"float\<Rightarrow>float\<Rightarrow>float"
where "sup_float a b = max a b"

instance
  by default
     (transfer, simp_all add: inf_float_def sup_float_def real_of_float_min real_of_float_max)+
end

lemma float_numeral[simp]: "real (numeral x :: float) = numeral x"
  apply (induct x)
  apply simp
  apply (simp_all only: numeral_Bit0 numeral_Bit1 real_of_float_eq real_float
                  plus_float.rep_eq one_float.rep_eq plus_float numeral_float one_float)
  done

lemma transfer_numeral [transfer_rule]:
  "rel_fun (op =) pcr_float (numeral :: _ \<Rightarrow> real) (numeral :: _ \<Rightarrow> float)"
  unfolding rel_fun_def float.pcr_cr_eq  cr_float_def by simp

lemma float_neg_numeral[simp]: "real (- numeral x :: float) = - numeral x"
  by simp

lemma transfer_neg_numeral [transfer_rule]:
  "rel_fun (op =) pcr_float (- numeral :: _ \<Rightarrow> real) (- numeral :: _ \<Rightarrow> float)"
  unfolding rel_fun_def float.pcr_cr_eq cr_float_def by simp

lemma
  shows float_of_numeral[simp]: "numeral k = float_of (numeral k)"
    and float_of_neg_numeral[simp]: "- numeral k = float_of (- numeral k)"
  unfolding real_of_float_eq by simp_all

subsection {* Represent floats as unique mantissa and exponent *}

lemma int_induct_abs[case_names less]:
  fixes j :: int
  assumes H: "\<And>n. (\<And>i. \<bar>i\<bar> < \<bar>n\<bar> \<Longrightarrow> P i) \<Longrightarrow> P n"
  shows "P j"
proof (induct "nat \<bar>j\<bar>" arbitrary: j rule: less_induct)
  case less show ?case by (rule H[OF less]) simp
qed

lemma int_cancel_factors:
  fixes n :: int assumes "1 < r" shows "n = 0 \<or> (\<exists>k i. n = k * r ^ i \<and> \<not> r dvd k)"
proof (induct n rule: int_induct_abs)
  case (less n)
  { fix m assume n: "n \<noteq> 0" "n = m * r"
    then have "\<bar>m \<bar> < \<bar>n\<bar>"
      by (metis abs_dvd_iff abs_ge_self assms comm_semiring_1_class.normalizing_semiring_rules(7)
                dvd_imp_le_int dvd_refl dvd_triv_right linorder_neq_iff linorder_not_le
                mult_eq_0_iff zdvd_mult_cancel1)
    from less[OF this] n have "\<exists>k i. n = k * r ^ Suc i \<and> \<not> r dvd k" by auto }
  then show ?case
    by (metis comm_semiring_1_class.normalizing_semiring_rules(12,7) dvdE power_0)
qed

lemma mult_powr_eq_mult_powr_iff_asym:
  fixes m1 m2 e1 e2 :: int
  assumes m1: "\<not> 2 dvd m1" and "e1 \<le> e2"
  shows "m1 * 2 powr e1 = m2 * 2 powr e2 \<longleftrightarrow> m1 = m2 \<and> e1 = e2"
proof
  have "m1 \<noteq> 0" using m1 unfolding dvd_def by auto
  assume eq: "m1 * 2 powr e1 = m2 * 2 powr e2"
  with `e1 \<le> e2` have "m1 = m2 * 2 powr nat (e2 - e1)"
    by (simp add: powr_divide2[symmetric] field_simps)
  also have "\<dots> = m2 * 2^nat (e2 - e1)"
    by (simp add: powr_realpow)
  finally have m1_eq: "m1 = m2 * 2^nat (e2 - e1)"
    unfolding real_of_int_inject .
  with m1 have "m1 = m2"
    by (cases "nat (e2 - e1)") (auto simp add: dvd_def)
  then show "m1 = m2 \<and> e1 = e2"
    using eq `m1 \<noteq> 0` by (simp add: powr_inj)
qed simp

lemma mult_powr_eq_mult_powr_iff:
  fixes m1 m2 e1 e2 :: int
  shows "\<not> 2 dvd m1 \<Longrightarrow> \<not> 2 dvd m2 \<Longrightarrow> m1 * 2 powr e1 = m2 * 2 powr e2 \<longleftrightarrow> m1 = m2 \<and> e1 = e2"
  using mult_powr_eq_mult_powr_iff_asym[of m1 e1 e2 m2]
  using mult_powr_eq_mult_powr_iff_asym[of m2 e2 e1 m1]
  by (cases e1 e2 rule: linorder_le_cases) auto

lemma floatE_normed:
  assumes x: "x \<in> float"
  obtains (zero) "x = 0"
   | (powr) m e :: int where "x = m * 2 powr e" "\<not> 2 dvd m" "x \<noteq> 0"
proof atomize_elim
  { assume "x \<noteq> 0"
    from x obtain m e :: int where x: "x = m * 2 powr e" by (auto simp: float_def)
    with `x \<noteq> 0` int_cancel_factors[of 2 m] obtain k i where "m = k * 2 ^ i" "\<not> 2 dvd k"
      by auto
    with `\<not> 2 dvd k` x have "\<exists>(m::int) (e::int). x = m * 2 powr e \<and> \<not> (2::int) dvd m"
      by (rule_tac exI[of _ "k"], rule_tac exI[of _ "e + int i"])
         (simp add: powr_add powr_realpow) }
  then show "x = 0 \<or> (\<exists>(m::int) (e::int). x = m * 2 powr e \<and> \<not> (2::int) dvd m \<and> x \<noteq> 0)"
    by blast
qed

lemma float_normed_cases:
  fixes f :: float
  obtains (zero) "f = 0"
   | (powr) m e :: int where "real f = m * 2 powr e" "\<not> 2 dvd m" "f \<noteq> 0"
proof (atomize_elim, induct f)
  case (float_of y) then show ?case
    by (cases rule: floatE_normed) (auto simp: zero_float_def)
qed

definition mantissa :: "float \<Rightarrow> int" where
  "mantissa f = fst (SOME p::int \<times> int. (f = 0 \<and> fst p = 0 \<and> snd p = 0)
   \<or> (f \<noteq> 0 \<and> real f = real (fst p) * 2 powr real (snd p) \<and> \<not> 2 dvd fst p))"

definition exponent :: "float \<Rightarrow> int" where
  "exponent f = snd (SOME p::int \<times> int. (f = 0 \<and> fst p = 0 \<and> snd p = 0)
   \<or> (f \<noteq> 0 \<and> real f = real (fst p) * 2 powr real (snd p) \<and> \<not> 2 dvd fst p))"

lemma
  shows exponent_0[simp]: "exponent (float_of 0) = 0" (is ?E)
    and mantissa_0[simp]: "mantissa (float_of 0) = 0" (is ?M)
proof -
  have "\<And>p::int \<times> int. fst p = 0 \<and> snd p = 0 \<longleftrightarrow> p = (0, 0)" by auto
  then show ?E ?M
    by (auto simp add: mantissa_def exponent_def zero_float_def)
qed

lemma
  shows mantissa_exponent: "real f = mantissa f * 2 powr exponent f" (is ?E)
    and mantissa_not_dvd: "f \<noteq> (float_of 0) \<Longrightarrow> \<not> 2 dvd mantissa f" (is "_ \<Longrightarrow> ?D")
proof cases
  assume [simp]: "f \<noteq> (float_of 0)"
  have "f = mantissa f * 2 powr exponent f \<and> \<not> 2 dvd mantissa f"
  proof (cases f rule: float_normed_cases)
    case (powr m e)
    then have "\<exists>p::int \<times> int. (f = 0 \<and> fst p = 0 \<and> snd p = 0)
     \<or> (f \<noteq> 0 \<and> real f = real (fst p) * 2 powr real (snd p) \<and> \<not> 2 dvd fst p)"
      by auto
    then show ?thesis
      unfolding exponent_def mantissa_def
      by (rule someI2_ex) (simp add: zero_float_def)
  qed (simp add: zero_float_def)
  then show ?E ?D by auto
qed simp

lemma mantissa_noteq_0: "f \<noteq> float_of 0 \<Longrightarrow> mantissa f \<noteq> 0"
  using mantissa_not_dvd[of f] by auto

lemma
  fixes m e :: int
  defines "f \<equiv> float_of (m * 2 powr e)"
  assumes dvd: "\<not> 2 dvd m"
  shows mantissa_float: "mantissa f = m" (is "?M")
    and exponent_float: "m \<noteq> 0 \<Longrightarrow> exponent f = e" (is "_ \<Longrightarrow> ?E")
proof cases
  assume "m = 0" with dvd show "mantissa f = m" by auto
next
  assume "m \<noteq> 0"
  then have f_not_0: "f \<noteq> float_of 0" by (simp add: f_def)
  from mantissa_exponent[of f]
  have "m * 2 powr e = mantissa f * 2 powr exponent f"
    by (auto simp add: f_def)
  then show "?M" "?E"
    using mantissa_not_dvd[OF f_not_0] dvd
    by (auto simp: mult_powr_eq_mult_powr_iff)
qed

subsection {* Compute arithmetic operations *}

lemma Float_mantissa_exponent: "Float (mantissa f) (exponent f) = f"
  unfolding real_of_float_eq mantissa_exponent[of f] by simp

lemma Float_cases[case_names Float, cases type: float]:
  fixes f :: float
  obtains (Float) m e :: int where "f = Float m e"
  using Float_mantissa_exponent[symmetric]
  by (atomize_elim) auto

lemma denormalize_shift:
  assumes f_def: "f \<equiv> Float m e" and not_0: "f \<noteq> float_of 0"
  obtains i where "m = mantissa f * 2 ^ i" "e = exponent f - i"
proof
  from mantissa_exponent[of f] f_def
  have "m * 2 powr e = mantissa f * 2 powr exponent f"
    by simp
  then have eq: "m = mantissa f * 2 powr (exponent f - e)"
    by (simp add: powr_divide2[symmetric] field_simps)
  moreover
  have "e \<le> exponent f"
  proof (rule ccontr)
    assume "\<not> e \<le> exponent f"
    then have pos: "exponent f < e" by simp
    then have "2 powr (exponent f - e) = 2 powr - real (e - exponent f)"
      by simp
    also have "\<dots> = 1 / 2^nat (e - exponent f)"
      using pos by (simp add: powr_realpow[symmetric] powr_divide2[symmetric])
    finally have "m * 2^nat (e - exponent f) = real (mantissa f)"
      using eq by simp
    then have "mantissa f = m * 2^nat (e - exponent f)"
      unfolding real_of_int_inject by simp
    with `exponent f < e` have "2 dvd mantissa f"
      apply (intro dvdI[where k="m * 2^(nat (e-exponent f)) div 2"])
      apply (cases "nat (e - exponent f)")
      apply auto
      done
    then show False using mantissa_not_dvd[OF not_0] by simp
  qed
  ultimately have "real m = mantissa f * 2^nat (exponent f - e)"
    by (simp add: powr_realpow[symmetric])
  with `e \<le> exponent f`
  show "m = mantissa f * 2 ^ nat (exponent f - e)" "e = exponent f - nat (exponent f - e)"
    unfolding real_of_int_inject by auto
qed

lemma compute_float_zero[code_unfold, code]: "0 = Float 0 0"
  by transfer simp
hide_fact (open) compute_float_zero

lemma compute_float_one[code_unfold, code]: "1 = Float 1 0"
  by transfer simp
hide_fact (open) compute_float_one

lift_definition normfloat :: "float \<Rightarrow> float" is "\<lambda>x. x" .
lemma normloat_id[simp]: "normfloat x = x" by transfer rule

lemma compute_normfloat[code]: "normfloat (Float m e) =
  (if m mod 2 = 0 \<and> m \<noteq> 0 then normfloat (Float (m div 2) (e + 1))
                           else if m = 0 then 0 else Float m e)"
  by transfer (auto simp add: powr_add zmod_eq_0_iff)
hide_fact (open) compute_normfloat

lemma compute_float_numeral[code_abbrev]: "Float (numeral k) 0 = numeral k"
  by transfer simp
hide_fact (open) compute_float_numeral

lemma compute_float_neg_numeral[code_abbrev]: "Float (- numeral k) 0 = - numeral k"
  by transfer simp
hide_fact (open) compute_float_neg_numeral

lemma compute_float_uminus[code]: "- Float m1 e1 = Float (- m1) e1"
  by transfer simp
hide_fact (open) compute_float_uminus

lemma compute_float_times[code]: "Float m1 e1 * Float m2 e2 = Float (m1 * m2) (e1 + e2)"
  by transfer (simp add: field_simps powr_add)
hide_fact (open) compute_float_times

lemma compute_float_plus[code]: "Float m1 e1 + Float m2 e2 =
  (if m1 = 0 then Float m2 e2 else if m2 = 0 then Float m1 e1 else
  if e1 \<le> e2 then Float (m1 + m2 * 2^nat (e2 - e1)) e1
              else Float (m2 + m1 * 2^nat (e1 - e2)) e2)"
  by transfer (simp add: field_simps powr_realpow[symmetric] powr_divide2[symmetric])
hide_fact (open) compute_float_plus

lemma compute_float_minus[code]: fixes f g::float shows "f - g = f + (-g)"
  by simp
hide_fact (open) compute_float_minus

lemma compute_float_sgn[code]: "sgn (Float m1 e1) = (if 0 < m1 then 1 else if m1 < 0 then -1 else 0)"
  by transfer (simp add: sgn_times)
hide_fact (open) compute_float_sgn

lift_definition is_float_pos :: "float \<Rightarrow> bool" is "op < 0 :: real \<Rightarrow> bool" .

lemma compute_is_float_pos[code]: "is_float_pos (Float m e) \<longleftrightarrow> 0 < m"
  by transfer (auto simp add: zero_less_mult_iff not_le[symmetric, of _ 0])
hide_fact (open) compute_is_float_pos

lemma compute_float_less[code]: "a < b \<longleftrightarrow> is_float_pos (b - a)"
  by transfer (simp add: field_simps)
hide_fact (open) compute_float_less

lift_definition is_float_nonneg :: "float \<Rightarrow> bool" is "op \<le> 0 :: real \<Rightarrow> bool" .

lemma compute_is_float_nonneg[code]: "is_float_nonneg (Float m e) \<longleftrightarrow> 0 \<le> m"
  by transfer (auto simp add: zero_le_mult_iff not_less[symmetric, of _ 0])
hide_fact (open) compute_is_float_nonneg

lemma compute_float_le[code]: "a \<le> b \<longleftrightarrow> is_float_nonneg (b - a)"
  by transfer (simp add: field_simps)
hide_fact (open) compute_float_le

lift_definition is_float_zero :: "float \<Rightarrow> bool"  is "op = 0 :: real \<Rightarrow> bool" .

lemma compute_is_float_zero[code]: "is_float_zero (Float m e) \<longleftrightarrow> 0 = m"
  by transfer (auto simp add: is_float_zero_def)
hide_fact (open) compute_is_float_zero

lemma compute_float_abs[code]: "abs (Float m e) = Float (abs m) e"
  by transfer (simp add: abs_mult)
hide_fact (open) compute_float_abs

lemma compute_float_eq[code]: "equal_class.equal f g = is_float_zero (f - g)"
  by transfer simp
hide_fact (open) compute_float_eq


subsection {* Lemmas for types @{typ real}, @{typ nat}, @{typ int}*}

lemmas real_of_ints =
  real_of_int_zero
  real_of_one
  real_of_int_add
  real_of_int_minus
  real_of_int_diff
  real_of_int_mult
  real_of_int_power
  real_numeral
lemmas real_of_nats =
  real_of_nat_zero
  real_of_nat_one
  real_of_nat_1
  real_of_nat_add
  real_of_nat_mult
  real_of_nat_power

lemmas int_of_reals = real_of_ints[symmetric]
lemmas nat_of_reals = real_of_nats[symmetric]

lemma two_real_int: "(2::real) = real (2::int)" by simp
lemma two_real_nat: "(2::real) = real (2::nat)" by simp


subsection {* Rounding Real Numbers *}

definition round_down :: "int \<Rightarrow> real \<Rightarrow> real" where
  "round_down prec x = floor (x * 2 powr prec) * 2 powr -prec"

definition round_up :: "int \<Rightarrow> real \<Rightarrow> real" where
  "round_up prec x = ceiling (x * 2 powr prec) * 2 powr -prec"

lemma round_down_float[simp]: "round_down prec x \<in> float"
  unfolding round_down_def
  by (auto intro!: times_float simp: real_of_int_minus[symmetric] simp del: real_of_int_minus)

lemma round_up_float[simp]: "round_up prec x \<in> float"
  unfolding round_up_def
  by (auto intro!: times_float simp: real_of_int_minus[symmetric] simp del: real_of_int_minus)

lemma round_up: "x \<le> round_up prec x"
  by (simp add: powr_minus_divide le_divide_eq round_up_def)

lemma round_down: "round_down prec x \<le> x"
  by (simp add: powr_minus_divide divide_le_eq round_down_def)

lemma round_up_0[simp]: "round_up p 0 = 0"
  unfolding round_up_def by simp

lemma round_down_0[simp]: "round_down p 0 = 0"
  unfolding round_down_def by simp

lemma round_up_diff_round_down:
  "round_up prec x - round_down prec x \<le> 2 powr -prec"
proof -
  have "round_up prec x - round_down prec x =
    (ceiling (x * 2 powr prec) - floor (x * 2 powr prec)) * 2 powr -prec"
    by (simp add: round_up_def round_down_def field_simps)
  also have "\<dots> \<le> 1 * 2 powr -prec"
    by (rule mult_mono)
       (auto simp del: real_of_int_diff
             simp: real_of_int_diff[symmetric] real_of_int_le_one_cancel_iff ceiling_diff_floor_le_1)
  finally show ?thesis by simp
qed

lemma round_down_shift: "round_down p (x * 2 powr k) = 2 powr k * round_down (p + k) x"
  unfolding round_down_def
  by (simp add: powr_add powr_mult field_simps powr_divide2[symmetric])
    (simp add: powr_add[symmetric])

lemma round_up_shift: "round_up p (x * 2 powr k) = 2 powr k * round_up (p + k) x"
  unfolding round_up_def
  by (simp add: powr_add powr_mult field_simps powr_divide2[symmetric])
    (simp add: powr_add[symmetric])

lemma round_up_uminus_eq: "round_up p (-x) = - round_down p x"
  and round_down_uminus_eq: "round_down p (-x) = - round_up p x"
  by (auto simp: round_up_def round_down_def ceiling_def)

lemma round_up_mono: "x \<le> y \<Longrightarrow> round_up p x \<le> round_up p y"
  by (auto intro!: ceiling_mono simp: round_up_def)

lemma round_up_le1:
  assumes "x \<le> 1" "prec \<ge> 0"
  shows "round_up prec x \<le> 1"
proof -
  have "real \<lceil>x * 2 powr prec\<rceil> \<le> real \<lceil>2 powr real prec\<rceil>"
    using assms by (auto intro!: ceiling_mono)
  also have "\<dots> = 2 powr prec" using assms by (auto simp: powr_int intro!: exI[where x="2^nat prec"])
  finally show ?thesis
    by (simp add: round_up_def) (simp add: powr_minus inverse_eq_divide)
qed

lemma round_up_less1:
  assumes "x < 1 / 2" "p > 0"
  shows "round_up p x < 1"
proof -
  have powr1: "2 powr p = 2 ^ nat p"
    using `p > 0` by (simp add: powr_realpow[symmetric])
  have "x * 2 powr p < 1 / 2 * 2 powr p"
    using assms by simp
  also have "\<dots> = 2 powr (p - 1)"
    by (simp add: algebra_simps powr_mult_base)
  also have "\<dots> = 2 ^ nat (p - 1)"
    using `p > 0` by (simp add: powr_realpow[symmetric])
  also have "\<dots> \<le> 2 ^ nat p - 1"
    using `p > 0`
    unfolding int_of_reals real_of_int_le_iff
    by simp
  finally show ?thesis
    apply (simp add: round_up_def field_simps powr_minus powr1)
    unfolding int_of_reals real_of_int_less_iff
    apply (simp add: ceiling_less_eq)
    done
qed

lemma round_down_ge1:
  assumes x: "x \<ge> 1"
  assumes prec: "p \<ge> - log 2 x"
  shows "1 \<le> round_down p x"
proof cases
  assume nonneg: "0 \<le> p"
  have "2 powr p = real \<lfloor>2 powr real p\<rfloor>"
    using nonneg by (auto simp: powr_int)
  also have "\<dots> \<le> real \<lfloor>x * 2 powr p\<rfloor>"
    using assms by (auto intro!: floor_mono)
  finally show ?thesis
    by (simp add: round_down_def) (simp add: powr_minus inverse_eq_divide)
next
  assume neg: "\<not> 0 \<le> p"
  have "x = 2 powr (log 2 x)"
    using x by simp
  also have "2 powr (log 2 x) \<ge> 2 powr - p"
    using prec by auto
  finally have x_le: "x \<ge> 2 powr -p" .

  from neg have "2 powr real p \<le> 2 powr 0"
    by (intro powr_mono) auto
  also have "\<dots> \<le> \<lfloor>2 powr 0\<rfloor>" by simp
  also have "\<dots> \<le> \<lfloor>x * 2 powr real p\<rfloor>" unfolding real_of_int_le_iff
    using x x_le by (intro floor_mono) (simp add: powr_minus_divide field_simps)
  finally show ?thesis
    using prec x
    by (simp add: round_down_def powr_minus_divide pos_le_divide_eq)
qed

lemma round_up_le0: "x \<le> 0 \<Longrightarrow> round_up p x \<le> 0"
  unfolding round_up_def
  by (auto simp: field_simps mult_le_0_iff zero_le_mult_iff)


subsection {* Rounding Floats *}

definition div_twopow::"int \<Rightarrow> nat \<Rightarrow> int" where [simp]: "div_twopow x n = x div (2 ^ n)"

definition mod_twopow::"int \<Rightarrow> nat \<Rightarrow> int" where [simp]: "mod_twopow x n = x mod (2 ^ n)"

lemma compute_div_twopow[code]:
  "div_twopow x n = (if x = 0 \<or> x = -1 \<or> n = 0 then x else div_twopow (x div 2) (n - 1))"
  by (cases n) (auto simp: zdiv_zmult2_eq div_eq_minus1)

lemma compute_mod_twopow[code]:
  "mod_twopow x n = (if n = 0 then 0 else x mod 2 + 2 * mod_twopow (x div 2) (n - 1))"
  by (cases n) (auto simp: zmod_zmult2_eq)

lift_definition float_up :: "int \<Rightarrow> float \<Rightarrow> float" is round_up by simp
declare float_up.rep_eq[simp]

lemma round_up_correct:
  shows "round_up e f - f \<in> {0..2 powr -e}"
unfolding atLeastAtMost_iff
proof
  have "round_up e f - f \<le> round_up e f - round_down e f" using round_down by simp
  also have "\<dots> \<le> 2 powr -e" using round_up_diff_round_down by simp
  finally show "round_up e f - f \<le> 2 powr real (- e)"
    by simp
qed (simp add: algebra_simps round_up)

lemma float_up_correct:
  shows "real (float_up e f) - real f \<in> {0..2 powr -e}"
  by transfer (rule round_up_correct)

lift_definition float_down :: "int \<Rightarrow> float \<Rightarrow> float" is round_down by simp
declare float_down.rep_eq[simp]

lemma round_down_correct:
  shows "f - (round_down e f) \<in> {0..2 powr -e}"
unfolding atLeastAtMost_iff
proof
  have "f - round_down e f \<le> round_up e f - round_down e f" using round_up by simp
  also have "\<dots> \<le> 2 powr -e" using round_up_diff_round_down by simp
  finally show "f - round_down e f \<le> 2 powr real (- e)"
    by simp
qed (simp add: algebra_simps round_down)

lemma float_down_correct:
  shows "real f - real (float_down e f) \<in> {0..2 powr -e}"
  by transfer (rule round_down_correct)

lemma compute_float_down[code]:
  "float_down p (Float m e) =
    (if p + e < 0 then Float (div_twopow m (nat (-(p + e)))) (-p) else Float m e)"
proof cases
  assume "p + e < 0"
  hence "real ((2::int) ^ nat (-(p + e))) = 2 powr (-(p + e))"
    using powr_realpow[of 2 "nat (-(p + e))"] by simp
  also have "... = 1 / 2 powr p / 2 powr e"
    unfolding powr_minus_divide real_of_int_minus by (simp add: powr_add)
  finally show ?thesis
    using `p + e < 0`
    by transfer (simp add: ac_simps round_down_def floor_divide_eq_div[symmetric])
next
  assume "\<not> p + e < 0"
  then have r: "real e + real p = real (nat (e + p))" by simp
  have r: "\<lfloor>(m * 2 powr e) * 2 powr real p\<rfloor> = (m * 2 powr e) * 2 powr real p"
    by (auto intro: exI[where x="m*2^nat (e+p)"]
             simp add: ac_simps powr_add[symmetric] r powr_realpow)
  with `\<not> p + e < 0` show ?thesis
    by transfer (auto simp add: round_down_def field_simps powr_add powr_minus)
qed
hide_fact (open) compute_float_down

lemma abs_round_down_le: "\<bar>f - (round_down e f)\<bar> \<le> 2 powr -e"
  using round_down_correct[of f e] by simp

lemma abs_round_up_le: "\<bar>f - (round_up e f)\<bar> \<le> 2 powr -e"
  using round_up_correct[of e f] by simp

lemma round_down_nonneg: "0 \<le> s \<Longrightarrow> 0 \<le> round_down p s"
  by (auto simp: round_down_def)

lemma ceil_divide_floor_conv:
assumes "b \<noteq> 0"
shows "\<lceil>real a / real b\<rceil> = (if b dvd a then a div b else \<lfloor>real a / real b\<rfloor> + 1)"
proof cases
  assume "\<not> b dvd a"
  hence "a mod b \<noteq> 0" by auto
  hence ne: "real (a mod b) / real b \<noteq> 0" using `b \<noteq> 0` by auto
  have "\<lceil>real a / real b\<rceil> = \<lfloor>real a / real b\<rfloor> + 1"
  apply (rule ceiling_eq) apply (auto simp: floor_divide_eq_div[symmetric])
  proof -
    have "real \<lfloor>real a / real b\<rfloor> \<le> real a / real b" by simp
    moreover have "real \<lfloor>real a / real b\<rfloor> \<noteq> real a / real b"
    apply (subst (2) real_of_int_div_aux) unfolding floor_divide_eq_div using ne `b \<noteq> 0` by auto
    ultimately show "real \<lfloor>real a / real b\<rfloor> < real a / real b" by arith
  qed
  thus ?thesis using `\<not> b dvd a` by simp
qed (simp add: ceiling_def real_of_int_minus[symmetric] divide_minus_left[symmetric]
  floor_divide_eq_div dvd_neg_div del: divide_minus_left real_of_int_minus)

lemma compute_float_up[code]:
  "float_up p x = - float_down p (-x)"
  by transfer (simp add: round_down_uminus_eq)
hide_fact (open) compute_float_up


subsection {* Compute bitlen of integers *}

definition bitlen :: "int \<Rightarrow> int" where
  "bitlen a = (if a > 0 then \<lfloor>log 2 a\<rfloor> + 1 else 0)"

lemma bitlen_nonneg: "0 \<le> bitlen x"
proof -
  {
    assume "0 > x"
    have "-1 = log 2 (inverse 2)" by (subst log_inverse) simp_all
    also have "... < log 2 (-x)" using `0 > x` by auto
    finally have "-1 < log 2 (-x)" .
  } thus "0 \<le> bitlen x" unfolding bitlen_def by (auto intro!: add_nonneg_nonneg)
qed

lemma bitlen_bounds:
  assumes "x > 0"
  shows "2 ^ nat (bitlen x - 1) \<le> x \<and> x < 2 ^ nat (bitlen x)"
proof
  have "(2::real) ^ nat \<lfloor>log 2 (real x)\<rfloor> = 2 powr real (floor (log 2 (real x)))"
    using powr_realpow[symmetric, of 2 "nat \<lfloor>log 2 (real x)\<rfloor>"] `x > 0`
    using real_nat_eq_real[of "floor (log 2 (real x))"]
    by simp
  also have "... \<le> 2 powr log 2 (real x)"
    by simp
  also have "... = real x"
    using `0 < x` by simp
  finally have "2 ^ nat \<lfloor>log 2 (real x)\<rfloor> \<le> real x" by simp
  thus "2 ^ nat (bitlen x - 1) \<le> x" using `x > 0`
    by (simp add: bitlen_def)
next
  have "x \<le> 2 powr (log 2 x)" using `x > 0` by simp
  also have "... < 2 ^ nat (\<lfloor>log 2 (real x)\<rfloor> + 1)"
    apply (simp add: powr_realpow[symmetric])
    using `x > 0` by simp
  finally show "x < 2 ^ nat (bitlen x)" using `x > 0`
    by (simp add: bitlen_def ac_simps int_of_reals del: real_of_ints)
qed

lemma bitlen_pow2[simp]:
  assumes "b > 0"
  shows "bitlen (b * 2 ^ c) = bitlen b + c"
proof -
  from assms have "b * 2 ^ c > 0" by auto
  thus ?thesis
    using floor_add[of "log 2 b" c] assms
    by (auto simp add: log_mult log_nat_power bitlen_def)
qed

lemma bitlen_Float:
  fixes m e
  defines "f \<equiv> Float m e"
  shows "bitlen (\<bar>mantissa f\<bar>) + exponent f = (if m = 0 then 0 else bitlen \<bar>m\<bar> + e)"
proof (cases "m = 0")
  case True
  then show ?thesis by (simp add: f_def bitlen_def Float_def)
next
  case False
  hence "f \<noteq> float_of 0"
    unfolding real_of_float_eq by (simp add: f_def)
  hence "mantissa f \<noteq> 0"
    by (simp add: mantissa_noteq_0)
  moreover
  obtain i where "m = mantissa f * 2 ^ i" "e = exponent f - int i"
    by (rule f_def[THEN denormalize_shift, OF `f \<noteq> float_of 0`])
  ultimately show ?thesis by (simp add: abs_mult)
qed

lemma compute_bitlen[code]:
  shows "bitlen x = (if x > 0 then bitlen (x div 2) + 1 else 0)"
proof -
  { assume "2 \<le> x"
    then have "\<lfloor>log 2 (x div 2)\<rfloor> + 1 = \<lfloor>log 2 (x - x mod 2)\<rfloor>"
      by (simp add: log_mult zmod_zdiv_equality')
    also have "\<dots> = \<lfloor>log 2 (real x)\<rfloor>"
    proof cases
      assume "x mod 2 = 0" then show ?thesis by simp
    next
      def n \<equiv> "\<lfloor>log 2 (real x)\<rfloor>"
      then have "0 \<le> n"
        using `2 \<le> x` by simp
      assume "x mod 2 \<noteq> 0"
      with `2 \<le> x` have "x mod 2 = 1" "\<not> 2 dvd x" by (auto simp add: dvd_eq_mod_eq_0)
      with `2 \<le> x` have "x \<noteq> 2^nat n" by (cases "nat n") auto
      moreover
      { have "real (2^nat n :: int) = 2 powr (nat n)"
          by (simp add: powr_realpow)
        also have "\<dots> \<le> 2 powr (log 2 x)"
          using `2 \<le> x` by (simp add: n_def del: powr_log_cancel)
        finally have "2^nat n \<le> x" using `2 \<le> x` by simp }
      ultimately have "2^nat n \<le> x - 1" by simp
      then have "2^nat n \<le> real (x - 1)"
        unfolding real_of_int_le_iff[symmetric] by simp
      { have "n = \<lfloor>log 2 (2^nat n)\<rfloor>"
          using `0 \<le> n` by (simp add: log_nat_power)
        also have "\<dots> \<le> \<lfloor>log 2 (x - 1)\<rfloor>"
          using `2^nat n \<le> real (x - 1)` `0 \<le> n` `2 \<le> x` by (auto intro: floor_mono)
        finally have "n \<le> \<lfloor>log 2 (x - 1)\<rfloor>" . }
      moreover have "\<lfloor>log 2 (x - 1)\<rfloor> \<le> n"
        using `2 \<le> x` by (auto simp add: n_def intro!: floor_mono)
      ultimately show "\<lfloor>log 2 (x - x mod 2)\<rfloor> = \<lfloor>log 2 x\<rfloor>"
        unfolding n_def `x mod 2 = 1` by auto
    qed
    finally have "\<lfloor>log 2 (x div 2)\<rfloor> + 1 = \<lfloor>log 2 x\<rfloor>" . }
  moreover
  { assume "x < 2" "0 < x"
    then have "x = 1" by simp
    then have "\<lfloor>log 2 (real x)\<rfloor> = 0" by simp }
  ultimately show ?thesis
    unfolding bitlen_def
    by (auto simp: pos_imp_zdiv_pos_iff not_le)
qed
hide_fact (open) compute_bitlen

lemma float_gt1_scale: assumes "1 \<le> Float m e"
  shows "0 \<le> e + (bitlen m - 1)"
proof -
  have "0 < Float m e" using assms by auto
  hence "0 < m" using powr_gt_zero[of 2 e]
    by (auto simp: zero_less_mult_iff)
  hence "m \<noteq> 0" by auto
  show ?thesis
  proof (cases "0 \<le> e")
    case True thus ?thesis using `0 < m`  by (simp add: bitlen_def)
  next
    have "(1::int) < 2" by simp
    case False let ?S = "2^(nat (-e))"
    have "inverse (2 ^ nat (- e)) = 2 powr e" using assms False powr_realpow[of 2 "nat (-e)"]
      by (auto simp: powr_minus field_simps)
    hence "1 \<le> real m * inverse ?S" using assms False powr_realpow[of 2 "nat (-e)"]
      by (auto simp: powr_minus)
    hence "1 * ?S \<le> real m * inverse ?S * ?S" by (rule mult_right_mono, auto)
    hence "?S \<le> real m" unfolding mult.assoc by auto
    hence "?S \<le> m" unfolding real_of_int_le_iff[symmetric] by auto
    from this bitlen_bounds[OF `0 < m`, THEN conjunct2]
    have "nat (-e) < (nat (bitlen m))" unfolding power_strict_increasing_iff[OF `1 < 2`, symmetric]
      by (rule order_le_less_trans)
    hence "-e < bitlen m" using False by auto
    thus ?thesis by auto
  qed
qed

lemma bitlen_div:
  assumes "0 < m"
  shows "1 \<le> real m / 2^nat (bitlen m - 1)" and "real m / 2^nat (bitlen m - 1) < 2"
proof -
  let ?B = "2^nat(bitlen m - 1)"

  have "?B \<le> m" using bitlen_bounds[OF `0 <m`] ..
  hence "1 * ?B \<le> real m" unfolding real_of_int_le_iff[symmetric] by auto
  thus "1 \<le> real m / ?B" by auto

  have "m \<noteq> 0" using assms by auto
  have "0 \<le> bitlen m - 1" using `0 < m` by (auto simp: bitlen_def)

  have "m < 2^nat(bitlen m)" using bitlen_bounds[OF `0 <m`] ..
  also have "\<dots> = 2^nat(bitlen m - 1 + 1)" using `0 < m` by (auto simp: bitlen_def)
  also have "\<dots> = ?B * 2" unfolding nat_add_distrib[OF `0 \<le> bitlen m - 1` zero_le_one] by auto
  finally have "real m < 2 * ?B" unfolding real_of_int_less_iff[symmetric] by auto
  hence "real m / ?B < 2 * ?B / ?B" by (rule divide_strict_right_mono, auto)
  thus "real m / ?B < 2" by auto
qed

subsection {* Truncating Real Numbers*}

definition truncate_down::"nat \<Rightarrow> real \<Rightarrow> real" where
  "truncate_down prec x = round_down (prec - \<lfloor>log 2 \<bar>x\<bar>\<rfloor> - 1) x"

lemma truncate_down: "truncate_down prec x \<le> x"
  using round_down by (simp add: truncate_down_def)

lemma truncate_down_le: "x \<le> y \<Longrightarrow> truncate_down prec x \<le> y"
  by (rule order_trans[OF truncate_down])

lemma truncate_down_zero[simp]: "truncate_down prec 0 = 0"
  by (simp add: truncate_down_def)

lemma truncate_down_float[simp]: "truncate_down p x \<in> float"
  by (auto simp: truncate_down_def)

definition truncate_up::"nat \<Rightarrow> real \<Rightarrow> real" where
  "truncate_up prec x = round_up (prec - \<lfloor>log 2 \<bar>x\<bar>\<rfloor> - 1) x"

lemma truncate_up: "x \<le> truncate_up prec x"
  using round_up by (simp add: truncate_up_def)

lemma truncate_up_le: "x \<le> y \<Longrightarrow> x \<le> truncate_up prec y"
  by (rule order_trans[OF _ truncate_up])

lemma truncate_up_zero[simp]: "truncate_up prec 0 = 0"
  by (simp add: truncate_up_def)

lemma truncate_up_uminus_eq: "truncate_up prec (-x) = - truncate_down prec x"
  and truncate_down_uminus_eq: "truncate_down prec (-x) = - truncate_up prec x"
  by (auto simp: truncate_up_def round_up_def truncate_down_def round_down_def ceiling_def)

lemma truncate_up_float[simp]: "truncate_up p x \<in> float"
  by (auto simp: truncate_up_def)

lemma mult_powr_eq: "0 < b \<Longrightarrow> b \<noteq> 1 \<Longrightarrow> 0 < x \<Longrightarrow> x * b powr y = b powr (y + log b x)"
  by (simp_all add: powr_add)

lemma truncate_down_pos:
  assumes "x > 0" "p > 0"
  shows "truncate_down p x > 0"
proof -
  have "0 \<le> log 2 x - real \<lfloor>log 2 x\<rfloor>"
    by (simp add: algebra_simps)
  from this assms
  show ?thesis
    by (auto simp: truncate_down_def round_down_def mult_powr_eq
      intro!: ge_one_powr_ge_zero mult_pos_pos)
qed

lemma truncate_down_nonneg: "0 \<le> y \<Longrightarrow> 0 \<le> truncate_down prec y"
  by (auto simp: truncate_down_def round_down_def)

lemma truncate_down_ge1: "1 \<le> x \<Longrightarrow> 1 \<le> p \<Longrightarrow> 1 \<le> truncate_down p x"
  by (auto simp: truncate_down_def algebra_simps intro!: round_down_ge1 add_mono)

lemma truncate_up_nonpos: "x \<le> 0 \<Longrightarrow> truncate_up prec x \<le> 0"
  by (auto simp: truncate_up_def round_up_def intro!: mult_nonpos_nonneg)

lemma truncate_up_le1:
  assumes "x \<le> 1" "1 \<le> p" shows "truncate_up p x \<le> 1"
proof -
  {
    assume "x \<le> 0"
    with truncate_up_nonpos[OF this, of p] have ?thesis by simp
  } moreover {
    assume "x > 0"
    hence le: "\<lfloor>log 2 \<bar>x\<bar>\<rfloor> \<le> 0"
      using assms by (auto simp: log_less_iff)
    from assms have "1 \<le> int p" by simp
    from add_mono[OF this le]
    have ?thesis using assms
      by (simp add: truncate_up_def round_up_le1 add_mono)
  } ultimately show ?thesis by arith
qed

subsection {* Truncating Floats*}

lift_definition float_round_up :: "nat \<Rightarrow> float \<Rightarrow> float" is truncate_up
  by (simp add: truncate_up_def)

lemma float_round_up: "real x \<le> real (float_round_up prec x)"
  using truncate_up by transfer simp

lemma float_round_up_zero[simp]: "float_round_up prec 0 = 0"
  by transfer simp

lift_definition float_round_down :: "nat \<Rightarrow> float \<Rightarrow> float" is truncate_down
  by (simp add: truncate_down_def)

lemma float_round_down: "real (float_round_down prec x) \<le> real x"
  using truncate_down by transfer simp

lemma float_round_down_zero[simp]: "float_round_down prec 0 = 0"
  by transfer simp

lemmas float_round_up_le = order_trans[OF _ float_round_up]
  and float_round_down_le = order_trans[OF float_round_down]

lemma minus_float_round_up_eq: "- float_round_up prec x = float_round_down prec (- x)"
  and minus_float_round_down_eq: "- float_round_down prec x = float_round_up prec (- x)"
  by (transfer, simp add: truncate_down_uminus_eq truncate_up_uminus_eq)+

lemma compute_float_round_down[code]:
  "float_round_down prec (Float m e) = (let d = bitlen (abs m) - int prec in
    if 0 < d then Float (div_twopow m (nat d)) (e + d)
             else Float m e)"
  using Float.compute_float_down[of "prec - bitlen \<bar>m\<bar> - e" m e, symmetric]
  by transfer (simp add: field_simps abs_mult log_mult bitlen_def truncate_down_def
    cong del: if_weak_cong)
hide_fact (open) compute_float_round_down

lemma compute_float_round_up[code]:
  "float_round_up prec x = - float_round_down prec (-x)"
  by transfer (simp add: truncate_down_uminus_eq)
hide_fact (open) compute_float_round_up


subsection {* Approximation of positive rationals *}

lemma div_mult_twopow_eq: fixes a b::nat shows "a div ((2::nat) ^ n) div b = a div (b * 2 ^ n)"
  by (cases "b=0") (simp_all add: div_mult2_eq[symmetric] ac_simps)

lemma real_div_nat_eq_floor_of_divide:
  fixes a b::nat
  shows "a div b = real (floor (a/b))"
by (metis floor_divide_eq_div real_of_int_of_nat_eq zdiv_int)

definition "rat_precision prec x y = int prec - (bitlen x - bitlen y)"

lift_definition lapprox_posrat :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> float"
  is "\<lambda>prec (x::nat) (y::nat). round_down (rat_precision prec x y) (x / y)" by simp

lemma compute_lapprox_posrat[code]:
  fixes prec x y
  shows "lapprox_posrat prec x y =
   (let
       l = rat_precision prec x y;
       d = if 0 \<le> l then x * 2^nat l div y else x div 2^nat (- l) div y
    in normfloat (Float d (- l)))"
    unfolding div_mult_twopow_eq
    by transfer
       (simp add: round_down_def powr_int real_div_nat_eq_floor_of_divide field_simps Let_def
             del: two_powr_minus_int_float)
hide_fact (open) compute_lapprox_posrat

lift_definition rapprox_posrat :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> float"
  is "\<lambda>prec (x::nat) (y::nat). round_up (rat_precision prec x y) (x / y)" by simp

lemma compute_rapprox_posrat[code]:
  fixes prec x y
  notes divmod_int_mod_div[simp]
  defines "l \<equiv> rat_precision prec x y"
  shows "rapprox_posrat prec x y = (let
     l = l ;
     X = if 0 \<le> l then (x * 2^nat l, y) else (x, y * 2^nat(-l)) ;
     (d, m) = divmod_int (fst X) (snd X)
   in normfloat (Float (d + (if m = 0 \<or> y = 0 then 0 else 1)) (- l)))"
proof (cases "y = 0")
  assume "y = 0" thus ?thesis by transfer simp
next
  assume "y \<noteq> 0"
  show ?thesis
  proof (cases "0 \<le> l")
    assume "0 \<le> l"
    def x' \<equiv> "x * 2 ^ nat l"
    have "int x * 2 ^ nat l = x'" by (simp add: x'_def int_mult int_power)
    moreover have "real x * 2 powr real l = real x'"
      by (simp add: powr_realpow[symmetric] `0 \<le> l` x'_def)
    ultimately show ?thesis
      using ceil_divide_floor_conv[of y x'] powr_realpow[of 2 "nat l"] `0 \<le> l` `y \<noteq> 0`
        l_def[symmetric, THEN meta_eq_to_obj_eq]
      by transfer (auto simp add: floor_divide_eq_div [symmetric] round_up_def)
   next
    assume "\<not> 0 \<le> l"
    def y' \<equiv> "y * 2 ^ nat (- l)"
    from `y \<noteq> 0` have "y' \<noteq> 0" by (simp add: y'_def)
    have "int y * 2 ^ nat (- l) = y'" by (simp add: y'_def int_mult int_power)
    moreover have "real x * real (2::int) powr real l / real y = x / real y'"
      using `\<not> 0 \<le> l`
      by (simp add: powr_realpow[symmetric] powr_minus y'_def field_simps)
    ultimately show ?thesis
      using ceil_divide_floor_conv[of y' x] `\<not> 0 \<le> l` `y' \<noteq> 0` `y \<noteq> 0`
        l_def[symmetric, THEN meta_eq_to_obj_eq]
      by transfer
         (auto simp add: round_up_def ceil_divide_floor_conv floor_divide_eq_div [symmetric])
  qed
qed
hide_fact (open) compute_rapprox_posrat

lemma rat_precision_pos:
  assumes "0 \<le> x" and "0 < y" and "2 * x < y" and "0 < n"
  shows "rat_precision n (int x) (int y) > 0"
proof -
  { assume "0 < x" hence "log 2 x + 1 = log 2 (2 * x)" by (simp add: log_mult) }
  hence "bitlen (int x) < bitlen (int y)" using assms
    by (simp add: bitlen_def del: floor_add_one)
      (auto intro!: floor_mono simp add: floor_add_one[symmetric] simp del: floor_add floor_add_one)
  thus ?thesis
    using assms by (auto intro!: pos_add_strict simp add: field_simps rat_precision_def)
qed

lemma rapprox_posrat_less1:
  shows "0 \<le> x \<Longrightarrow> 0 < y \<Longrightarrow> 2 * x < y \<Longrightarrow> 0 < n \<Longrightarrow> real (rapprox_posrat n x y) < 1"
  by transfer (simp add: rat_precision_pos round_up_less1)

lift_definition lapprox_rat :: "nat \<Rightarrow> int \<Rightarrow> int \<Rightarrow> float" is
  "\<lambda>prec (x::int) (y::int). round_down (rat_precision prec \<bar>x\<bar> \<bar>y\<bar>) (x / y)" by simp

lemma compute_lapprox_rat[code]:
  "lapprox_rat prec x y =
    (if y = 0 then 0
    else if 0 \<le> x then
      (if 0 < y then lapprox_posrat prec (nat x) (nat y)
      else - (rapprox_posrat prec (nat x) (nat (-y))))
      else (if 0 < y
        then - (rapprox_posrat prec (nat (-x)) (nat y))
        else lapprox_posrat prec (nat (-x)) (nat (-y))))"
  by transfer (auto simp: round_up_def round_down_def ceiling_def ac_simps)
hide_fact (open) compute_lapprox_rat

lift_definition rapprox_rat :: "nat \<Rightarrow> int \<Rightarrow> int \<Rightarrow> float" is
  "\<lambda>prec (x::int) (y::int). round_up (rat_precision prec \<bar>x\<bar> \<bar>y\<bar>) (x / y)" by simp

lemma "rapprox_rat = rapprox_posrat"
  by transfer auto

lemma "lapprox_rat = lapprox_posrat"
  by transfer auto

lemma compute_rapprox_rat[code]:
  "rapprox_rat prec x y = - lapprox_rat prec (-x) y"
  by transfer (simp add: round_down_uminus_eq)
hide_fact (open) compute_rapprox_rat

subsection {* Division *}

definition "real_divl prec a b = round_down (int prec + \<lfloor> log 2 \<bar>b\<bar> \<rfloor> - \<lfloor> log 2 \<bar>a\<bar> \<rfloor>) (a / b)"

definition "real_divr prec a b = round_up (int prec + \<lfloor> log 2 \<bar>b\<bar> \<rfloor> - \<lfloor> log 2 \<bar>a\<bar> \<rfloor>) (a / b)"

lift_definition float_divl :: "nat \<Rightarrow> float \<Rightarrow> float \<Rightarrow> float" is real_divl
  by (simp add: real_divl_def)

lemma compute_float_divl[code]:
  "float_divl prec (Float m1 s1) (Float m2 s2) = lapprox_rat prec m1 m2 * Float 1 (s1 - s2)"
proof cases
  let ?f1 = "real m1 * 2 powr real s1" and ?f2 = "real m2 * 2 powr real s2"
  let ?m = "real m1 / real m2" and ?s = "2 powr real (s1 - s2)"
  assume not_0: "m1 \<noteq> 0 \<and> m2 \<noteq> 0"
  then have eq2: "(int prec + \<lfloor>log 2 \<bar>?f2\<bar>\<rfloor> - \<lfloor>log 2 \<bar>?f1\<bar>\<rfloor>) = rat_precision prec \<bar>m1\<bar> \<bar>m2\<bar> + (s2 - s1)"
    by (simp add: abs_mult log_mult rat_precision_def bitlen_def)
  have eq1: "real m1 * 2 powr real s1 / (real m2 * 2 powr real s2) = ?m * ?s"
    by (simp add: field_simps powr_divide2[symmetric])

  show ?thesis
    using not_0
    by (transfer fixing: m1 s1 m2 s2 prec) (unfold eq1 eq2 round_down_shift real_divl_def,
      simp add: field_simps)
qed (transfer, auto simp: real_divl_def)
hide_fact (open) compute_float_divl

lift_definition float_divr :: "nat \<Rightarrow> float \<Rightarrow> float \<Rightarrow> float" is real_divr
  by (simp add: real_divr_def)

lemma compute_float_divr[code]:
  "float_divr prec x y = - float_divl prec (-x) y"
  by transfer (simp add: real_divr_def real_divl_def round_down_uminus_eq)
hide_fact (open) compute_float_divr


subsection {* Approximate Power *}

lemma div2_less_self[termination_simp]: fixes n::nat shows "odd n \<Longrightarrow> n div 2 < n"
  by (simp add: odd_pos)

fun power_down :: "nat \<Rightarrow> real \<Rightarrow> nat \<Rightarrow> real" where
  "power_down p x 0 = 1"
| "power_down p x (Suc n) =
    (if odd n then truncate_down (Suc p) ((power_down p x (Suc n div 2))\<^sup>2) else truncate_down (Suc p) (x * power_down p x n))"

fun power_up :: "nat \<Rightarrow> real \<Rightarrow> nat \<Rightarrow> real" where
  "power_up p x 0 = 1"
| "power_up p x (Suc n) =
    (if odd n then truncate_up p ((power_up p x (Suc n div 2))\<^sup>2) else truncate_up p (x * power_up p x n))"

lift_definition power_up_fl :: "nat \<Rightarrow> float \<Rightarrow> nat \<Rightarrow> float" is power_up
  by (induct_tac rule: power_up.induct) simp_all

lift_definition power_down_fl :: "nat \<Rightarrow> float \<Rightarrow> nat \<Rightarrow> float" is power_down
  by (induct_tac rule: power_down.induct) simp_all

lemma power_float_transfer[transfer_rule]:
  "(rel_fun pcr_float (rel_fun op = pcr_float)) op ^ op ^"
  unfolding power_def
  by transfer_prover

lemma compute_power_up_fl[code]:
  "power_up_fl p x 0 = 1"
  "power_up_fl p x (Suc n) =
    (if odd n then float_round_up p ((power_up_fl p x (Suc n div 2))\<^sup>2) else float_round_up p (x * power_up_fl p x n))"
  and compute_power_down_fl[code]:
  "power_down_fl p x 0 = 1"
  "power_down_fl p x (Suc n) =
    (if odd n then float_round_down (Suc p) ((power_down_fl p x (Suc n div 2))\<^sup>2) else float_round_down (Suc p) (x * power_down_fl p x n))"
  unfolding atomize_conj
  by transfer simp

lemma power_down_pos: "0 < x \<Longrightarrow> 0 < power_down p x n"
  by (induct p x n rule: power_down.induct)
    (auto simp del: odd_Suc_div_two intro!: truncate_down_pos)

lemma power_down_nonneg: "0 \<le> x \<Longrightarrow> 0 \<le> power_down p x n"
  by (induct p x n rule: power_down.induct)
    (auto simp del: odd_Suc_div_two intro!: truncate_down_nonneg mult_nonneg_nonneg)

lemma power_down: "0 \<le> x \<Longrightarrow> power_down p x n \<le> x ^ n"
proof (induct p x n rule: power_down.induct)
  case (2 p x n)
  {
    assume "odd n"
    hence "(power_down p x (Suc n div 2)) ^ 2 \<le> (x ^ (Suc n div 2)) ^ 2"
      using 2
      by (auto intro: power_mono power_down_nonneg simp del: odd_Suc_div_two)
    also have "\<dots> = x ^ (Suc n div 2 * 2)"
      by (simp add: power_mult[symmetric])
    also have "Suc n div 2 * 2 = Suc n"
      using `odd n` by presburger
    finally have ?case
      using `odd n`
      by (auto intro!: truncate_down_le simp del: odd_Suc_div_two)
  } thus ?case
    by (auto intro!: truncate_down_le mult_left_mono 2 mult_nonneg_nonneg power_down_nonneg)
qed simp

lemma power_up: "0 \<le> x \<Longrightarrow> x ^ n \<le> power_up p x n"
proof (induct p x n rule: power_up.induct)
  case (2 p x n)
  {
    assume "odd n"
    hence "Suc n = Suc n div 2 * 2"
      using `odd n` even_Suc by presburger
    hence "x ^ Suc n \<le> (x ^ (Suc n div 2))\<^sup>2"
      by (simp add: power_mult[symmetric])
    also have "\<dots> \<le> (power_up p x (Suc n div 2))\<^sup>2"
      using 2 `odd n`
      by (auto intro: power_mono simp del: odd_Suc_div_two )
    finally have ?case
      using `odd n`
      by (auto intro!: truncate_up_le simp del: odd_Suc_div_two )
  } thus ?case
    by (auto intro!: truncate_up_le mult_left_mono 2)
qed simp

lemmas power_up_le = order_trans[OF _ power_up]
  and power_up_less = less_le_trans[OF _ power_up]
  and power_down_le = order_trans[OF power_down]

lemma power_down_fl: "0 \<le> x \<Longrightarrow> power_down_fl p x n \<le> x ^ n"
  by transfer (rule power_down)

lemma power_up_fl: "0 \<le> x \<Longrightarrow> x ^ n \<le> power_up_fl p x n"
  by transfer (rule power_up)

lemma real_power_up_fl: "real (power_up_fl p x n) = power_up p x n"
  by transfer simp

lemma real_power_down_fl: "real (power_down_fl p x n) = power_down p x n"
  by transfer simp


subsection {* Approximate Addition *}

definition "plus_down prec x y = truncate_down prec (x + y)"

definition "plus_up prec x y = truncate_up prec (x + y)"

lemma float_plus_down_float[intro, simp]: "x \<in> float \<Longrightarrow> y \<in> float \<Longrightarrow> plus_down p x y \<in> float"
  by (simp add: plus_down_def)

lemma float_plus_up_float[intro, simp]: "x \<in> float \<Longrightarrow> y \<in> float \<Longrightarrow> plus_up p x y \<in> float"
  by (simp add: plus_up_def)

lift_definition float_plus_down::"nat \<Rightarrow> float \<Rightarrow> float \<Rightarrow> float" is plus_down ..

lift_definition float_plus_up::"nat \<Rightarrow> float \<Rightarrow> float \<Rightarrow> float" is plus_up ..

lemma plus_down: "plus_down prec x y \<le> x + y"
  and plus_up: "x + y \<le> plus_up prec x y"
  by (auto simp: plus_down_def truncate_down plus_up_def truncate_up)

lemma float_plus_down: "real (float_plus_down prec x y) \<le> x + y"
  and float_plus_up: "x + y \<le> real (float_plus_up prec x y)"
  by (transfer, rule plus_down plus_up)+

lemmas plus_down_le = order_trans[OF plus_down]
  and plus_up_le = order_trans[OF _ plus_up]
  and float_plus_down_le = order_trans[OF float_plus_down]
  and float_plus_up_le = order_trans[OF _ float_plus_up]

lemma compute_plus_up[code]: "plus_up p x y = - plus_down p (-x) (-y)"
  using truncate_down_uminus_eq[of p "x + y"]
  by (auto simp: plus_down_def plus_up_def)

lemma
  truncate_down_log2_eqI:
  assumes "\<lfloor>log 2 \<bar>x\<bar>\<rfloor> = \<lfloor>log 2 \<bar>y\<bar>\<rfloor>"
  assumes "\<lfloor>x * 2 powr (p - \<lfloor>log 2 \<bar>x\<bar>\<rfloor> - 1)\<rfloor> = \<lfloor>y * 2 powr (p - \<lfloor>log 2 \<bar>x\<bar>\<rfloor> - 1)\<rfloor>"
  shows "truncate_down p x = truncate_down p y"
  using assms by (auto simp: truncate_down_def round_down_def)

lemma bitlen_eq_zero_iff: "bitlen x = 0 \<longleftrightarrow> x \<le> 0"
  by (clarsimp simp add: bitlen_def)
    (metis Float.compute_bitlen add.commute bitlen_def bitlen_nonneg less_add_same_cancel2 not_less
      zero_less_one)

lemma
  sum_neq_zeroI:
  fixes a k::real
  shows "abs a \<ge> k \<Longrightarrow> abs b < k \<Longrightarrow> a + b \<noteq> 0"
    and "abs a > k \<Longrightarrow> abs b \<le> k \<Longrightarrow> a + b \<noteq> 0"
  by auto

lemma
  abs_real_le_2_powr_bitlen[simp]:
  "\<bar>real m2\<bar> < 2 powr real (bitlen \<bar>m2\<bar>)"
proof cases
  assume "m2 \<noteq> 0"
  hence "\<bar>m2\<bar> < 2 ^ nat (bitlen \<bar>m2\<bar>)"
    using bitlen_bounds[of "\<bar>m2\<bar>"]
    by (auto simp: powr_add bitlen_nonneg)
  thus ?thesis
    by (simp add: powr_int bitlen_nonneg real_of_int_less_iff[symmetric])
qed simp

lemma floor_sum_times_2_powr_sgn_eq:
  fixes ai p q::int
  and a b::real
  assumes "a * 2 powr p = ai"
  assumes b_le_1: "abs (b * 2 powr (p + 1)) \<le> 1"
  assumes leqp: "q \<le> p"
  shows "\<lfloor>(a + b) * 2 powr q\<rfloor> = \<lfloor>(2 * ai + sgn b) * 2 powr (q - p - 1)\<rfloor>"
proof -
  {
    assume "b = 0"
    hence ?thesis
      by (simp add: assms(1)[symmetric] powr_add[symmetric] algebra_simps powr_mult_base)
  } moreover {
    assume "b > 0"
    hence "b * 2 powr p < abs (b * 2 powr (p + 1))" by simp
    also note b_le_1
    finally have b_less_1: "b * 2 powr real p < 1" .

    from b_less_1 `b > 0` have floor_eq: "\<lfloor>b * 2 powr real p\<rfloor> = 0" "\<lfloor>sgn b / 2\<rfloor> = 0"
      by (simp_all add: floor_eq_iff)

    have "\<lfloor>(a + b) * 2 powr q\<rfloor> = \<lfloor>(a + b) * 2 powr p * 2 powr (q - p)\<rfloor>"
      by (simp add: algebra_simps powr_realpow[symmetric] powr_add[symmetric])
    also have "\<dots> = \<lfloor>(ai + b * 2 powr p) * 2 powr (q - p)\<rfloor>"
      by (simp add: assms algebra_simps)
    also have "\<dots> = \<lfloor>(ai + b * 2 powr p) / real ((2::int) ^ nat (p - q))\<rfloor>"
      using assms
      by (simp add: algebra_simps powr_realpow[symmetric] divide_powr_uminus powr_add[symmetric])
    also have "\<dots> = \<lfloor>ai / real ((2::int) ^ nat (p - q))\<rfloor>"
      by (simp del: real_of_int_power add: floor_divide_real_eq_div floor_eq)
    finally have "\<lfloor>(a + b) * 2 powr real q\<rfloor> = \<lfloor>real ai / real ((2::int) ^ nat (p - q))\<rfloor>" .
    moreover
    {
      have "\<lfloor>(2 * ai + sgn b) * 2 powr (real (q - p) - 1)\<rfloor> = \<lfloor>(ai + sgn b / 2) * 2 powr (q - p)\<rfloor>"
        by (subst powr_divide2[symmetric]) (simp add: field_simps)
      also have "\<dots> = \<lfloor>(ai + sgn b / 2) / real ((2::int) ^ nat (p - q))\<rfloor>"
        using leqp by (simp add: powr_realpow[symmetric] powr_divide2[symmetric])
      also have "\<dots> = \<lfloor>ai / real ((2::int) ^ nat (p - q))\<rfloor>"
        by (simp del: real_of_int_power add: floor_divide_real_eq_div floor_eq)
      finally
      have "\<lfloor>(2 * ai + (sgn b)) * 2 powr (real (q - p) - 1)\<rfloor> =
          \<lfloor>real ai / real ((2::int) ^ nat (p - q))\<rfloor>"
        .
    } ultimately have ?thesis by simp
  } moreover {
    assume "\<not> 0 \<le> b"
    hence "0 > b" by simp
    hence floor_eq: "\<lfloor>b * 2 powr (real p + 1)\<rfloor> = -1"
      using b_le_1
      by (auto simp: floor_eq_iff algebra_simps pos_divide_le_eq[symmetric] abs_if divide_powr_uminus
        intro!: mult_neg_pos split: split_if_asm)
    have "\<lfloor>(a + b) * 2 powr q\<rfloor> = \<lfloor>(2*a + 2*b) * 2 powr p * 2 powr (q - p - 1)\<rfloor>"
      by (simp add: algebra_simps powr_realpow[symmetric] powr_add[symmetric] powr_mult_base)
    also have "\<dots> = \<lfloor>(2 * (a * 2 powr p) + 2 * b * 2 powr p) * 2 powr (q - p - 1)\<rfloor>"
      by (simp add: algebra_simps)
    also have "\<dots> = \<lfloor>(2 * ai + b * 2 powr (p + 1)) / 2 powr (1 - q + p)\<rfloor>"
      using assms by (simp add: algebra_simps powr_mult_base divide_powr_uminus)
    also have "\<dots> = \<lfloor>(2 * ai + b * 2 powr (p + 1)) / real ((2::int) ^ nat (p - q + 1))\<rfloor>"
      using assms by (simp add: algebra_simps powr_realpow[symmetric])
    also have "\<dots> = \<lfloor>(2 * ai - 1) / real ((2::int) ^ nat (p - q + 1))\<rfloor>"
      using `b < 0` assms
      by (simp add: floor_divide_eq_div floor_eq floor_divide_real_eq_div
        del: real_of_int_mult real_of_int_power real_of_int_diff)
    also have "\<dots> = \<lfloor>(2 * ai - 1) * 2 powr (q - p - 1)\<rfloor>"
      using assms by (simp add: algebra_simps divide_powr_uminus powr_realpow[symmetric])
    finally have ?thesis using `b < 0` by simp
  } ultimately show ?thesis by arith
qed

lemma
  log2_abs_int_add_less_half_sgn_eq:
  fixes ai::int and b::real
  assumes "abs b \<le> 1/2" "ai \<noteq> 0"
  shows "\<lfloor>log 2 \<bar>real ai + b\<bar>\<rfloor> = \<lfloor>log 2 \<bar>ai + sgn b / 2\<bar>\<rfloor>"
proof cases
  assume "b = 0" thus ?thesis by simp
next
  assume "b \<noteq> 0"
  def k \<equiv> "\<lfloor>log 2 \<bar>ai\<bar>\<rfloor>"
  hence "\<lfloor>log 2 \<bar>ai\<bar>\<rfloor> = k" by simp
  hence k: "2 powr k \<le> \<bar>ai\<bar>" "\<bar>ai\<bar> < 2 powr (k + 1)"
    by (simp_all add: floor_log_eq_powr_iff `ai \<noteq> 0`)
  have "k \<ge> 0"
    using assms by (auto simp: k_def)
  def r \<equiv> "\<bar>ai\<bar> - 2 ^ nat k"
  have r: "0 \<le> r" "r < 2 powr k"
    using `k \<ge> 0` k
    by (auto simp: r_def k_def algebra_simps powr_add abs_if powr_int)
  hence "r \<le> (2::int) ^ nat k - 1"
    using `k \<ge> 0` by (auto simp: powr_int)
  from this[simplified real_of_int_le_iff[symmetric]] `0 \<le> k`
  have r_le: "r \<le> 2 powr k - 1"
    by (auto simp: algebra_simps powr_int simp del: real_of_int_le_iff)

  have "\<bar>ai\<bar> = 2 powr k + r"
    using `k \<ge> 0` by (auto simp: k_def r_def powr_realpow[symmetric])

  have pos: "\<And>b::real. abs b < 1 \<Longrightarrow> 0 < 2 powr k + (r + b)"
    using `0 \<le> k` `ai \<noteq> 0`
    by (auto simp add: r_def powr_realpow[symmetric] abs_if sgn_if algebra_simps
      split: split_if_asm)
  have less: "\<bar>sgn ai * b\<bar> < 1"
    and less': "\<bar>sgn (sgn ai * b) / 2\<bar> < 1"
    using `abs b \<le> _` by (auto simp: abs_if sgn_if split: split_if_asm)

  have floor_eq: "\<And>b::real. abs b \<le> 1 / 2 \<Longrightarrow>
      \<lfloor>log 2 (1 + (r + b) / 2 powr k)\<rfloor> = (if r = 0 \<and> b < 0 then -1 else 0)"
    using `k \<ge> 0` r r_le
    by (auto simp: floor_log_eq_powr_iff powr_minus_divide field_simps sgn_if)

  from `real \<bar>ai\<bar> = _` have "\<bar>ai + b\<bar> = 2 powr k + (r + sgn ai * b)"
    using `abs b <= _` `0 \<le> k` r
    by (auto simp add: sgn_if abs_if)
  also have "\<lfloor>log 2 \<dots>\<rfloor> = \<lfloor>log 2 (2 powr k + r + sgn (sgn ai * b) / 2)\<rfloor>"
  proof -
    have "2 powr k + (r + (sgn ai) * b) = 2 powr k * (1 + (r + sgn ai * b) / 2 powr k)"
      by (simp add: field_simps)
    also have "\<lfloor>log 2 \<dots>\<rfloor> = k + \<lfloor>log 2 (1 + (r + sgn ai * b) / 2 powr k)\<rfloor>"
      using pos[OF less]
      by (subst log_mult) (simp_all add: log_mult powr_mult field_simps)
    also
    let ?if = "if r = 0 \<and> sgn ai * b < 0 then -1 else 0"
    have "\<lfloor>log 2 (1 + (r + sgn ai * b) / 2 powr k)\<rfloor> = ?if"
      using `abs b <= _`
      by (intro floor_eq) (auto simp: abs_mult sgn_if)
    also
    have "\<dots> = \<lfloor>log 2 (1 + (r + sgn (sgn ai * b) / 2) / 2 powr k)\<rfloor>"
      by (subst floor_eq) (auto simp: sgn_if)
    also have "k + \<dots> = \<lfloor>log 2 (2 powr k * (1 + (r + sgn (sgn ai * b) / 2) / 2 powr k))\<rfloor>"
      unfolding floor_add2[symmetric]
      using pos[OF less'] `abs b \<le> _`
      by (simp add: field_simps add_log_eq_powr)
    also have "2 powr k * (1 + (r + sgn (sgn ai * b) / 2) / 2 powr k) =
        2 powr k + r + sgn (sgn ai * b) / 2"
      by (simp add: sgn_if field_simps)
    finally show ?thesis .
  qed
  also have "2 powr k + r + sgn (sgn ai * b) / 2 = \<bar>ai + sgn b / 2\<bar>"
    unfolding `real \<bar>ai\<bar> = _`[symmetric] using `ai \<noteq> 0`
    by (auto simp: abs_if sgn_if algebra_simps)
  finally show ?thesis .
qed

lemma compute_far_float_plus_down:
  fixes m1 e1 m2 e2::int and p::nat
  defines "k1 \<equiv> p - nat (bitlen \<bar>m1\<bar>)"
  assumes H: "bitlen \<bar>m2\<bar> \<le> e1 - e2 - k1 - 2" "m1 \<noteq> 0" "m2 \<noteq> 0" "e1 \<ge> e2"
  shows "float_plus_down p (Float m1 e1) (Float m2 e2) =
    float_round_down p (Float (m1 * 2 ^ (Suc (Suc k1)) + sgn m2) (e1 - int k1 - 2))"
proof -
  let ?a = "real (Float m1 e1)"
  let ?b = "real (Float m2 e2)"
  let ?sum = "?a + ?b"
  let ?shift = "real e2 - real e1 + real k1 + 1"
  let ?m1 = "m1 * 2 ^ Suc k1"
  let ?m2 = "m2 * 2 powr ?shift"
  let ?m2' = "sgn m2 / 2"
  let ?e = "e1 - int k1 - 1"

  have sum_eq: "?sum = (?m1 + ?m2) * 2 powr ?e"
    by (auto simp: powr_add[symmetric] powr_mult[symmetric] algebra_simps
      powr_realpow[symmetric] powr_mult_base)

  have "\<bar>?m2\<bar> * 2 < 2 powr (bitlen \<bar>m2\<bar> + ?shift + 1)"
    by (auto simp: field_simps powr_add powr_mult_base powr_numeral powr_divide2[symmetric] abs_mult)
  also have "\<dots> \<le> 2 powr 0"
    using H by (intro powr_mono) auto
  finally have abs_m2_less_half: "\<bar>?m2\<bar> < 1 / 2"
    by simp

  hence "\<bar>real m2\<bar> < 2 powr -(?shift + 1)"
    unfolding powr_minus_divide by (auto simp: bitlen_def field_simps powr_mult_base abs_mult)
  also have "\<dots> \<le> 2 powr real (e1 - e2 - 2)"
    by simp
  finally have b_less_quarter: "\<bar>?b\<bar> < 1/4 * 2 powr real e1"
    by (simp add: powr_add field_simps powr_divide2[symmetric] powr_numeral abs_mult)
  also have "1/4 < \<bar>real m1\<bar> / 2" using `m1 \<noteq> 0` by simp
  finally have b_less_half_a: "\<bar>?b\<bar> < 1/2 * \<bar>?a\<bar>"
    by (simp add: algebra_simps powr_mult_base abs_mult)
  hence a_half_less_sum: "\<bar>?a\<bar> / 2 < \<bar>?sum\<bar>"
    by (auto simp: field_simps abs_if split: split_if_asm)

  from b_less_half_a have "\<bar>?b\<bar> < \<bar>?a\<bar>" "\<bar>?b\<bar> \<le> \<bar>?a\<bar>"
    by simp_all

  have "\<bar>real (Float m1 e1)\<bar> \<ge> 1/4 * 2 powr real e1"
    using `m1 \<noteq> 0`
    by (auto simp: powr_add powr_int bitlen_nonneg divide_right_mono abs_mult)
  hence "?sum \<noteq> 0" using b_less_quarter
    by (rule sum_neq_zeroI)
  hence "?m1 + ?m2 \<noteq> 0"
    unfolding sum_eq by (simp add: abs_mult zero_less_mult_iff)

  have "\<bar>real ?m1\<bar> \<ge> 2 ^ Suc k1" "\<bar>?m2'\<bar> < 2 ^ Suc k1"
    using `m1 \<noteq> 0` `m2 \<noteq> 0` by (auto simp: sgn_if less_1_mult abs_mult simp del: power.simps)
  hence sum'_nz: "?m1 + ?m2' \<noteq> 0"
    by (intro sum_neq_zeroI)

  have "\<lfloor>log 2 \<bar>real (Float m1 e1) + real (Float m2 e2)\<bar>\<rfloor> = \<lfloor>log 2 \<bar>?m1 + ?m2\<bar>\<rfloor> + ?e"
    using `?m1 + ?m2 \<noteq> 0`
    unfolding floor_add[symmetric] sum_eq
    by (simp add: abs_mult log_mult)
  also have "\<lfloor>log 2 \<bar>?m1 + ?m2\<bar>\<rfloor> = \<lfloor>log 2 \<bar>?m1 + sgn (real m2 * 2 powr ?shift) / 2\<bar>\<rfloor>"
    using abs_m2_less_half `m1 \<noteq> 0`
    by (intro log2_abs_int_add_less_half_sgn_eq) (auto simp: abs_mult)
  also have "sgn (real m2 * 2 powr ?shift) = sgn m2"
    by (auto simp: sgn_if zero_less_mult_iff less_not_sym)
  also
  have "\<bar>?m1 + ?m2'\<bar> * 2 powr ?e = \<bar>?m1 * 2 + sgn m2\<bar> * 2 powr (?e - 1)"
    by (auto simp: field_simps powr_minus[symmetric] powr_divide2[symmetric] powr_mult_base)
  hence "\<lfloor>log 2 \<bar>?m1 + ?m2'\<bar>\<rfloor> + ?e = \<lfloor>log 2 \<bar>real (Float (?m1 * 2 + sgn m2) (?e - 1))\<bar>\<rfloor>"
    using `?m1 + ?m2' \<noteq> 0`
    unfolding floor_add[symmetric]
    by (simp add: log_add_eq_powr abs_mult_pos)
  finally
  have "\<lfloor>log 2 \<bar>?sum\<bar>\<rfloor> = \<lfloor>log 2 \<bar>real (Float (?m1*2 + sgn m2) (?e - 1))\<bar>\<rfloor>" .
  hence "plus_down p (Float m1 e1) (Float m2 e2) =
      truncate_down p (Float (?m1*2 + sgn m2) (?e - 1))"
    unfolding plus_down_def
  proof (rule truncate_down_log2_eqI)
    let ?f = "(int p - \<lfloor>log 2 \<bar>real (Float m1 e1) + real (Float m2 e2)\<bar>\<rfloor> - 1)"
    let ?ai = "m1 * 2 ^ (Suc k1)"
    have "\<lfloor>(?a + ?b) * 2 powr real ?f\<rfloor> = \<lfloor>(real (2 * ?ai) + sgn ?b) * 2 powr real (?f - - ?e - 1)\<rfloor>"
    proof (rule floor_sum_times_2_powr_sgn_eq)
      show "?a * 2 powr real (-?e) = real ?ai"
        by (simp add: powr_add powr_realpow[symmetric] powr_divide2[symmetric])
      show "\<bar>?b * 2 powr real (-?e + 1)\<bar> \<le> 1"
        using abs_m2_less_half
        by (simp add: abs_mult powr_add[symmetric] algebra_simps powr_mult_base)
    next
      have "e1 + \<lfloor>log 2 \<bar>real m1\<bar>\<rfloor> - 1 = \<lfloor>log 2 \<bar>?a\<bar>\<rfloor> - 1"
        using `m1 \<noteq> 0`
        by (simp add: floor_add2[symmetric] algebra_simps log_mult abs_mult del: floor_add2)
      also have "\<dots> \<le> \<lfloor>log 2 \<bar>?a + ?b\<bar>\<rfloor>"
        using a_half_less_sum `m1 \<noteq> 0` `?sum \<noteq> 0`
        unfolding floor_subtract[symmetric]
        by (auto simp add: log_minus_eq_powr powr_minus_divide
          intro!: floor_mono)
      finally
      have "int p - \<lfloor>log 2 \<bar>?a + ?b\<bar>\<rfloor> \<le> p - (bitlen \<bar>m1\<bar>) - e1 + 2"
        by (auto simp: algebra_simps bitlen_def `m1 \<noteq> 0`)
      also have "\<dots> \<le> 1 - ?e"
        using bitlen_nonneg[of "\<bar>m1\<bar>"] by (simp add: k1_def)
      finally show "?f \<le> - ?e" by simp
    qed
    also have "sgn ?b = sgn m2"
      using powr_gt_zero[of 2 e2]
      by (auto simp add: sgn_if zero_less_mult_iff simp del: powr_gt_zero)
    also have "\<lfloor>(real (2 * ?m1) + real (sgn m2)) * 2 powr real (?f - - ?e - 1)\<rfloor> =
        \<lfloor>Float (?m1 * 2 + sgn m2) (?e - 1) * 2 powr ?f\<rfloor>"
      by (simp add: powr_add[symmetric] algebra_simps powr_realpow[symmetric])
    finally
    show "\<lfloor>(?a + ?b) * 2 powr ?f\<rfloor> = \<lfloor>real (Float (?m1 * 2 + sgn m2) (?e - 1)) * 2 powr ?f\<rfloor>" .
  qed
  thus ?thesis
    by transfer (simp add: plus_down_def ac_simps Let_def)
qed

lemma compute_float_plus_down_naive[code]: "float_plus_down p x y = float_round_down p (x + y)"
  by transfer (auto simp: plus_down_def)

lemma compute_float_plus_down[code]:
  fixes p::nat and m1 e1 m2 e2::int
  shows "float_plus_down p (Float m1 e1) (Float m2 e2) =
    (if m1 = 0 then float_round_down p (Float m2 e2)
    else if m2 = 0 then float_round_down p (Float m1 e1)
    else (if e1 \<ge> e2 then
      (let
        k1 = p - nat (bitlen \<bar>m1\<bar>)
      in
        if bitlen \<bar>m2\<bar> > e1 - e2 - k1 - 2 then float_round_down p ((Float m1 e1) + (Float m2 e2))
        else float_round_down p (Float (m1 * 2 ^ (Suc (Suc k1)) + sgn m2) (e1 - int k1 - 2)))
    else float_plus_down p (Float m2 e2) (Float m1 e1)))"
proof -
  {
    assume H: "bitlen \<bar>m2\<bar> \<le> e1 - e2 - (p - nat (bitlen \<bar>m1\<bar>)) - 2" "m1 \<noteq> 0" "m2 \<noteq> 0" "e1 \<ge> e2"
    note compute_far_float_plus_down[OF H]
  }
  thus ?thesis
    by transfer (simp add: Let_def plus_down_def ac_simps)
qed
hide_fact (open) compute_far_float_plus_down
hide_fact (open) compute_float_plus_down

lemma compute_float_plus_up[code]: "float_plus_up p x y = - float_plus_down p (-x) (-y)"
  using truncate_down_uminus_eq[of p "x + y"]
  by transfer (simp add: plus_down_def plus_up_def ac_simps)
hide_fact (open) compute_float_plus_up

lemma mantissa_zero[simp]: "mantissa 0 = 0"
by (metis mantissa_0 zero_float.abs_eq)


subsection {* Lemmas needed by Approximate *}

lemma Float_num[simp]: shows
   "real (Float 1 0) = 1" and "real (Float 1 1) = 2" and "real (Float 1 2) = 4" and
   "real (Float 1 (- 1)) = 1/2" and "real (Float 1 (- 2)) = 1/4" and "real (Float 1 (- 3)) = 1/8" and
   "real (Float (- 1) 0) = -1" and "real (Float (number_of n) 0) = number_of n"
using two_powr_int_float[of 2] two_powr_int_float[of "-1"] two_powr_int_float[of "-2"] two_powr_int_float[of "-3"]
using powr_realpow[of 2 2] powr_realpow[of 2 3]
using powr_minus[of 2 1] powr_minus[of 2 2] powr_minus[of 2 3]
by auto

lemma real_of_Float_int[simp]: "real (Float n 0) = real n" by simp

lemma float_zero[simp]: "real (Float 0 e) = 0" by simp

lemma abs_div_2_less: "a \<noteq> 0 \<Longrightarrow> a \<noteq> -1 \<Longrightarrow> abs((a::int) div 2) < abs a"
by arith

lemma lapprox_rat:
  shows "real (lapprox_rat prec x y) \<le> real x / real y"
  using round_down by (simp add: lapprox_rat_def)

lemma mult_div_le: fixes a b:: int assumes "b > 0" shows "a \<ge> b * (a div b)"
proof -
  from zmod_zdiv_equality'[of a b]
  have "a = b * (a div b) + a mod b" by simp
  also have "... \<ge> b * (a div b) + 0" apply (rule add_left_mono) apply (rule pos_mod_sign)
  using assms by simp
  finally show ?thesis by simp
qed

lemma lapprox_rat_nonneg:
  fixes n x y
  assumes "0 \<le> x" and "0 \<le> y"
  shows "0 \<le> real (lapprox_rat n x y)"
  using assms by (auto simp: lapprox_rat_def simp: round_down_nonneg)

lemma rapprox_rat: "real x / real y \<le> real (rapprox_rat prec x y)"
  using round_up by (simp add: rapprox_rat_def)

lemma rapprox_rat_le1:
  fixes n x y
  assumes xy: "0 \<le> x" "0 < y" "x \<le> y"
  shows "real (rapprox_rat n x y) \<le> 1"
proof -
  have "bitlen \<bar>x\<bar> \<le> bitlen \<bar>y\<bar>"
    using xy unfolding bitlen_def by (auto intro!: floor_mono)
  from this assms show ?thesis
    by transfer (auto intro!: round_up_le1 simp: rat_precision_def)
qed

lemma rapprox_rat_nonneg_nonpos:
  "0 \<le> x \<Longrightarrow> y \<le> 0 \<Longrightarrow> real (rapprox_rat n x y) \<le> 0"
  by transfer (simp add: round_up_le0 divide_nonneg_nonpos)

lemma rapprox_rat_nonpos_nonneg:
  "x \<le> 0 \<Longrightarrow> 0 \<le> y \<Longrightarrow> real (rapprox_rat n x y) \<le> 0"
  by transfer (simp add: round_up_le0 divide_nonpos_nonneg)

lemma real_divl: "real_divl prec x y \<le> x / y"
  by (simp add: real_divl_def round_down)

lemma real_divr: "x / y \<le> real_divr prec x y"
  using round_up by (simp add: real_divr_def)

lemma float_divl: "real (float_divl prec x y) \<le> real x / real y"
  by transfer (rule real_divl)

lemma real_divl_lower_bound:
  "0 \<le> x \<Longrightarrow> 0 \<le> y \<Longrightarrow> 0 \<le> real_divl prec x y"
  by (simp add: real_divl_def round_down_nonneg)

lemma float_divl_lower_bound:
  "0 \<le> x \<Longrightarrow> 0 \<le> y \<Longrightarrow> 0 \<le> real (float_divl prec x y)"
  by transfer (rule real_divl_lower_bound)

lemma exponent_1: "exponent 1 = 0"
  using exponent_float[of 1 0] by (simp add: one_float_def)

lemma mantissa_1: "mantissa 1 = 1"
  using mantissa_float[of 1 0] by (simp add: one_float_def)

lemma bitlen_1: "bitlen 1 = 1"
  by (simp add: bitlen_def)

lemma mantissa_eq_zero_iff: "mantissa x = 0 \<longleftrightarrow> x = 0"
proof
  assume "mantissa x = 0" hence z: "0 = real x" using mantissa_exponent by simp
  show "x = 0" by (simp add: zero_float_def z)
qed (simp add: zero_float_def)

lemma float_upper_bound: "x \<le> 2 powr (bitlen \<bar>mantissa x\<bar> + exponent x)"
proof (cases "x = 0", simp)
  assume "x \<noteq> 0" hence "mantissa x \<noteq> 0" using mantissa_eq_zero_iff by auto
  have "x = mantissa x * 2 powr (exponent x)" by (rule mantissa_exponent)
  also have "mantissa x \<le> \<bar>mantissa x\<bar>" by simp
  also have "... \<le> 2 powr (bitlen \<bar>mantissa x\<bar>)"
    using bitlen_bounds[of "\<bar>mantissa x\<bar>"] bitlen_nonneg `mantissa x \<noteq> 0`
    by (simp add: powr_int) (simp only: two_real_int int_of_reals real_of_int_abs[symmetric]
      real_of_int_le_iff less_imp_le)
  finally show ?thesis by (simp add: powr_add)
qed

lemma real_divl_pos_less1_bound:
  assumes "0 < x" "x \<le> 1" "prec \<ge> 1"
  shows "1 \<le> real_divl prec 1 x"
proof -
  have "log 2 x \<le> real prec + real \<lfloor>log 2 x\<rfloor>" using `prec \<ge> 1` by arith
  from this assms show ?thesis
    by (simp add: real_divl_def log_divide round_down_ge1)
qed

lemma float_divl_pos_less1_bound:
  "0 < real x \<Longrightarrow> real x \<le> 1 \<Longrightarrow> prec \<ge> 1 \<Longrightarrow> 1 \<le> real (float_divl prec 1 x)"
  by (transfer, rule real_divl_pos_less1_bound)

lemma float_divr: "real x / real y \<le> real (float_divr prec x y)"
  by transfer (rule real_divr)

lemma real_divr_pos_less1_lower_bound: assumes "0 < x" and "x \<le> 1" shows "1 \<le> real_divr prec 1 x"
proof -
  have "1 \<le> 1 / x" using `0 < x` and `x <= 1` by auto
  also have "\<dots> \<le> real_divr prec 1 x" using real_divr[where x=1 and y=x] by auto
  finally show ?thesis by auto
qed

lemma float_divr_pos_less1_lower_bound: "0 < x \<Longrightarrow> x \<le> 1 \<Longrightarrow> 1 \<le> float_divr prec 1 x"
  by transfer (rule real_divr_pos_less1_lower_bound)

lemma real_divr_nonpos_pos_upper_bound:
  "x \<le> 0 \<Longrightarrow> 0 \<le> y \<Longrightarrow> real_divr prec x y \<le> 0"
  by (simp add: real_divr_def round_up_le0 divide_le_0_iff)

lemma float_divr_nonpos_pos_upper_bound:
  "real x \<le> 0 \<Longrightarrow> 0 \<le> real y \<Longrightarrow> real (float_divr prec x y) \<le> 0"
  by transfer (rule real_divr_nonpos_pos_upper_bound)

lemma real_divr_nonneg_neg_upper_bound:
  "0 \<le> x \<Longrightarrow> y \<le> 0 \<Longrightarrow> real_divr prec x y \<le> 0"
  by (simp add: real_divr_def round_up_le0 divide_le_0_iff)

lemma float_divr_nonneg_neg_upper_bound:
  "0 \<le> real x \<Longrightarrow> real y \<le> 0 \<Longrightarrow> real (float_divr prec x y) \<le> 0"
  by transfer (rule real_divr_nonneg_neg_upper_bound)

lemma truncate_up_nonneg_mono:
  assumes "0 \<le> x" "x \<le> y"
  shows "truncate_up prec x \<le> truncate_up prec y"
proof -
  {
    assume "\<lfloor>log 2 x\<rfloor> = \<lfloor>log 2 y\<rfloor>"
    hence ?thesis
      using assms
      by (auto simp: truncate_up_def round_up_def intro!: ceiling_mono)
  } moreover {
    assume "0 < x"
    hence "log 2 x \<le> log 2 y" using assms by auto
    moreover
    assume "\<lfloor>log 2 x\<rfloor> \<noteq> \<lfloor>log 2 y\<rfloor>"
    ultimately have logless: "log 2 x < log 2 y" and flogless: "\<lfloor>log 2 x\<rfloor> < \<lfloor>log 2 y\<rfloor>"
      unfolding atomize_conj
      by (metis floor_less_cancel linorder_cases not_le)
    have "truncate_up prec x =
      real \<lceil>x * 2 powr real (int prec - \<lfloor>log 2 x\<rfloor> - 1)\<rceil> * 2 powr - real (int prec - \<lfloor>log 2 x\<rfloor> - 1)"
      using assms by (simp add: truncate_up_def round_up_def)
    also have "\<lceil>x * 2 powr real (int prec - \<lfloor>log 2 x\<rfloor> - 1)\<rceil> \<le> (2 ^ prec)"
    proof (unfold ceiling_le_eq)
      have "x * 2 powr real (int prec - \<lfloor>log 2 x\<rfloor> - 1) \<le> x * (2 powr real prec / (2 powr log 2 x))"
        using real_of_int_floor_add_one_ge[of "log 2 x"] assms
        by (auto simp add: algebra_simps powr_divide2 intro!: mult_left_mono)
      thus "x * 2 powr real (int prec - \<lfloor>log 2 x\<rfloor> - 1) \<le> real ((2::int) ^ prec)"
        using `0 < x` by (simp add: powr_realpow)
    qed
    hence "real \<lceil>x * 2 powr real (int prec - \<lfloor>log 2 x\<rfloor> - 1)\<rceil> \<le> 2 powr int prec"
      by (auto simp: powr_realpow)
    also
    have "2 powr - real (int prec - \<lfloor>log 2 x\<rfloor> - 1) \<le> 2 powr - real (int prec - \<lfloor>log 2 y\<rfloor>)"
      using logless flogless by (auto intro!: floor_mono)
    also have "2 powr real (int prec) \<le> 2 powr (log 2 y + real (int prec - \<lfloor>log 2 y\<rfloor>))"
      using assms `0 < x`
      by (auto simp: algebra_simps)
    finally have "truncate_up prec x \<le> 2 powr (log 2 y + real (int prec - \<lfloor>log 2 y\<rfloor>)) * 2 powr - real (int prec - \<lfloor>log 2 y\<rfloor>)"
      by simp
    also have "\<dots> = 2 powr (log 2 y + real (int prec - \<lfloor>log 2 y\<rfloor>) - real (int prec - \<lfloor>log 2 y\<rfloor>))"
      by (subst powr_add[symmetric]) simp
    also have "\<dots> = y"
      using `0 < x` assms
      by (simp add: powr_add)
    also have "\<dots> \<le> truncate_up prec y"
      by (rule truncate_up)
    finally have ?thesis .
  } moreover {
    assume "~ 0 < x"
    hence ?thesis
      using assms
      by (auto intro!: truncate_up_le)
  } ultimately show ?thesis
    by blast
qed

lemma truncate_up_switch_sign_mono:
  assumes "x \<le> 0" "0 \<le> y"
  shows "truncate_up prec x \<le> truncate_up prec y"
proof -
  note truncate_up_nonpos[OF `x \<le> 0`]
  also note truncate_up_le[OF `0 \<le> y`]
  finally show ?thesis .
qed

lemma truncate_down_zeroprec_mono:
  assumes "0 < x" "x \<le> y"
  shows "truncate_down 0 x \<le> truncate_down 0 y"
proof -
  have "x * 2 powr (- real \<lfloor>log 2 x\<rfloor> - 1) = x * inverse (2 powr ((real \<lfloor>log 2 x\<rfloor> + 1)))"
    by (simp add: powr_divide2[symmetric] powr_add powr_minus inverse_eq_divide)
  also have "\<dots> = 2 powr (log 2 x - (real \<lfloor>log 2 x\<rfloor>) - 1)"
    using `0 < x`
    by (auto simp: field_simps powr_add powr_divide2[symmetric])
  also have "\<dots> < 2 powr 0"
    using real_of_int_floor_add_one_gt
    unfolding neg_less_iff_less
    by (intro powr_less_mono) (auto simp: algebra_simps)
  finally have "\<lfloor>x * 2 powr (- real \<lfloor>log 2 x\<rfloor> - 1)\<rfloor> < 1"
    unfolding less_ceiling_eq real_of_int_minus real_of_one
    by simp
  moreover
  have "0 \<le> \<lfloor>x * 2 powr (- real \<lfloor>log 2 x\<rfloor> - 1)\<rfloor>"
    using `x > 0` by auto
  ultimately have "\<lfloor>x * 2 powr (- real \<lfloor>log 2 x\<rfloor> - 1)\<rfloor> \<in> {0 ..< 1}"
    by simp
  also have "\<dots> \<subseteq> {0}" by auto
  finally have "\<lfloor>x * 2 powr (- real \<lfloor>log 2 x\<rfloor> - 1)\<rfloor> = 0" by simp
  with assms show ?thesis
    by (auto simp: truncate_down_def round_down_def)
qed

lemma truncate_down_switch_sign_mono:
  assumes "x \<le> 0" "0 \<le> y"
  assumes "x \<le> y"
  shows "truncate_down prec x \<le> truncate_down prec y"
proof -
  note truncate_down_le[OF `x \<le> 0`]
  also note truncate_down_nonneg[OF `0 \<le> y`]
  finally show ?thesis .
qed

lemma truncate_down_nonneg_mono:
  assumes "0 \<le> x" "x \<le> y"
  shows "truncate_down prec x \<le> truncate_down prec y"
proof -
  {
    assume "0 < x" "prec = 0"
    with assms have ?thesis
      by (simp add: truncate_down_zeroprec_mono)
  } moreover {
    assume "~ 0 < x"
    with assms have "x = 0" "0 \<le> y" by simp_all
    hence ?thesis
      by (auto intro!: truncate_down_nonneg)
  } moreover {
    assume "\<lfloor>log 2 \<bar>x\<bar>\<rfloor> = \<lfloor>log 2 \<bar>y\<bar>\<rfloor>"
    hence ?thesis
      using assms
      by (auto simp: truncate_down_def round_down_def intro!: floor_mono)
  } moreover {
    assume "0 < x"
    hence "log 2 x \<le> log 2 y" "0 < y" "0 \<le> y" using assms by auto
    moreover
    assume "\<lfloor>log 2 \<bar>x\<bar>\<rfloor> \<noteq> \<lfloor>log 2 \<bar>y\<bar>\<rfloor>"
    ultimately have logless: "log 2 x < log 2 y" and flogless: "\<lfloor>log 2 x\<rfloor> < \<lfloor>log 2 y\<rfloor>"
      unfolding atomize_conj abs_of_pos[OF `0 < x`] abs_of_pos[OF `0 < y`]
      by (metis floor_less_cancel linorder_cases not_le)
    assume "prec \<noteq> 0" hence [simp]: "prec \<ge> Suc 0" by auto
    have "2 powr (prec - 1) \<le> y * 2 powr real (prec - 1) / (2 powr log 2 y)"
      using `0 < y`
      by simp
    also have "\<dots> \<le> y * 2 powr real prec / (2 powr (real \<lfloor>log 2 y\<rfloor> + 1))"
      using `0 \<le> y` `0 \<le> x` assms(2)
      by (auto intro!: powr_mono divide_left_mono
        simp: real_of_nat_diff powr_add
        powr_divide2[symmetric])
    also have "\<dots> = y * 2 powr real prec / (2 powr real \<lfloor>log 2 y\<rfloor> * 2)"
      by (auto simp: powr_add)
    finally have "(2 ^ (prec - 1)) \<le> \<lfloor>y * 2 powr real (int prec - \<lfloor>log 2 \<bar>y\<bar>\<rfloor> - 1)\<rfloor>"
      using `0 \<le> y`
      by (auto simp: powr_divide2[symmetric] le_floor_eq powr_realpow)
    hence "(2 ^ (prec - 1)) * 2 powr - real (int prec - \<lfloor>log 2 \<bar>y\<bar>\<rfloor> - 1) \<le> truncate_down prec y"
      by (auto simp: truncate_down_def round_down_def)
    moreover
    {
      have "x = 2 powr (log 2 \<bar>x\<bar>)" using `0 < x` by simp
      also have "\<dots> \<le> (2 ^ (prec )) * 2 powr - real (int prec - \<lfloor>log 2 \<bar>x\<bar>\<rfloor> - 1)"
        using real_of_int_floor_add_one_ge[of "log 2 \<bar>x\<bar>"]
        by (auto simp: powr_realpow[symmetric] powr_add[symmetric] algebra_simps)
      also
      have "2 powr - real (int prec - \<lfloor>log 2 \<bar>x\<bar>\<rfloor> - 1) \<le> 2 powr - real (int prec - \<lfloor>log 2 \<bar>y\<bar>\<rfloor>)"
        using logless flogless `x > 0` `y > 0`
        by (auto intro!: floor_mono)
      finally have "x \<le> (2 ^ (prec - 1)) * 2 powr - real (int prec - \<lfloor>log 2 \<bar>y\<bar>\<rfloor> - 1)"
        by (auto simp: powr_realpow[symmetric] powr_divide2[symmetric] assms real_of_nat_diff)
    } ultimately have ?thesis
      by (metis dual_order.trans truncate_down)
  } ultimately show ?thesis by blast
qed

lemma truncate_down_eq_truncate_up: "truncate_down p x = - truncate_up p (-x)"
  and truncate_up_eq_truncate_down: "truncate_up p x = - truncate_down p (-x)"
  by (auto simp: truncate_up_uminus_eq truncate_down_uminus_eq)

lemma truncate_down_mono: "x \<le> y \<Longrightarrow> truncate_down p x \<le> truncate_down p y"
  apply (cases "0 \<le> x")
  apply (rule truncate_down_nonneg_mono, assumption+)
  apply (simp add: truncate_down_eq_truncate_up)
  apply (cases "0 \<le> y")
  apply (auto intro: truncate_up_nonneg_mono truncate_up_switch_sign_mono)
  done

lemma truncate_up_mono: "x \<le> y \<Longrightarrow> truncate_up p x \<le> truncate_up p y"
  by (simp add: truncate_up_eq_truncate_down truncate_down_mono)

lemma Float_le_zero_iff: "Float a b \<le> 0 \<longleftrightarrow> a \<le> 0"
 apply (auto simp: zero_float_def mult_le_0_iff)
 using powr_gt_zero[of 2 b] by simp

lemma real_of_float_pprt[simp]: fixes a::float shows "real (pprt a) = pprt (real a)"
  unfolding pprt_def sup_float_def max_def sup_real_def by auto

lemma real_of_float_nprt[simp]: fixes a::float shows "real (nprt a) = nprt (real a)"
  unfolding nprt_def inf_float_def min_def inf_real_def by auto

lift_definition int_floor_fl :: "float \<Rightarrow> int" is floor .

lemma compute_int_floor_fl[code]:
  "int_floor_fl (Float m e) = (if 0 \<le> e then m * 2 ^ nat e else m div (2 ^ (nat (-e))))"
  by transfer (simp add: powr_int int_of_reals floor_divide_eq_div del: real_of_ints)
hide_fact (open) compute_int_floor_fl

lift_definition floor_fl :: "float \<Rightarrow> float" is "\<lambda>x. real (floor x)" by simp

lemma compute_floor_fl[code]:
  "floor_fl (Float m e) = (if 0 \<le> e then Float m e else Float (m div (2 ^ (nat (-e)))) 0)"
  by transfer (simp add: powr_int int_of_reals floor_divide_eq_div del: real_of_ints)
hide_fact (open) compute_floor_fl

lemma floor_fl: "real (floor_fl x) \<le> real x" by transfer simp

lemma int_floor_fl: "real (int_floor_fl x) \<le> real x" by transfer simp

lemma floor_pos_exp: "exponent (floor_fl x) \<ge> 0"
proof (cases "floor_fl x = float_of 0")
  case True
  then show ?thesis by (simp add: floor_fl_def)
next
  case False
  have eq: "floor_fl x = Float \<lfloor>real x\<rfloor> 0" by transfer simp
  obtain i where "\<lfloor>real x\<rfloor> = mantissa (floor_fl x) * 2 ^ i" "0 = exponent (floor_fl x) - int i"
    by (rule denormalize_shift[OF eq[THEN eq_reflection] False])
  then show ?thesis by simp
qed

lemma compute_mantissa[code]:
  "mantissa (Float m e) = (if m = 0 then 0 else if 2 dvd m then mantissa (normfloat (Float m e)) else m)"
  by (auto simp: mantissa_float Float.abs_eq)

lemma compute_exponent[code]:
  "exponent (Float m e) = (if m = 0 then 0 else if 2 dvd m then exponent (normfloat (Float m e)) else e)"
  by (auto simp: exponent_float Float.abs_eq)

end

