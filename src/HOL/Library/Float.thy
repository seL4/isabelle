(*  Title:      HOL/Library/Float.thy
    Author:     Johannes Hölzl, Fabian Immler
    Copyright   2012  TU München
*)

section \<open>Floating-Point Numbers\<close>

theory Float
imports Log_Nat Lattice_Algebras
begin

definition "float = {m * 2 powr e | (m :: int) (e :: int). True}"

typedef float = float
  morphisms real_of_float float_of
  unfolding float_def by auto

setup_lifting type_definition_float

declare real_of_float [code_unfold]

lemmas float_of_inject[simp]

declare [[coercion "real_of_float :: float \<Rightarrow> real"]]

lemma real_of_float_eq: "f1 = f2 \<longleftrightarrow> real_of_float f1 = real_of_float f2" for f1 f2 :: float
  unfolding real_of_float_inject ..

declare real_of_float_inverse[simp] float_of_inverse [simp]
declare real_of_float [simp]


subsection \<open>Real operations preserving the representation as floating point number\<close>

lemma floatI: "m * 2 powr e = x \<Longrightarrow> x \<in> float" for m e :: int
  by (auto simp: float_def)

lemma zero_float[simp]: "0 \<in> float"
  by (auto simp: float_def)

lemma one_float[simp]: "1 \<in> float"
  by (intro floatI[of 1 0]) simp

lemma numeral_float[simp]: "numeral i \<in> float"
  by (intro floatI[of "numeral i" 0]) simp

lemma neg_numeral_float[simp]: "- numeral i \<in> float"
  by (intro floatI[of "- numeral i" 0]) simp

lemma real_of_int_float[simp]: "real_of_int x \<in> float" for x :: int
  by (intro floatI[of x 0]) simp

lemma real_of_nat_float[simp]: "real x \<in> float" for x :: nat
  by (intro floatI[of x 0]) simp

lemma two_powr_int_float[simp]: "2 powr (real_of_int i) \<in> float" for i :: int
  by (intro floatI[of 1 i]) simp

lemma two_powr_nat_float[simp]: "2 powr (real i) \<in> float" for i :: nat
  by (intro floatI[of 1 i]) simp

lemma two_powr_minus_int_float[simp]: "2 powr - (real_of_int i) \<in> float" for i :: int
  by (intro floatI[of 1 "-i"]) simp

lemma two_powr_minus_nat_float[simp]: "2 powr - (real i) \<in> float" for i :: nat
  by (intro floatI[of 1 "-i"]) simp

lemma two_powr_numeral_float[simp]: "2 powr numeral i \<in> float"
  by (intro floatI[of 1 "numeral i"]) simp

lemma two_powr_neg_numeral_float[simp]: "2 powr - numeral i \<in> float"
  by (intro floatI[of 1 "- numeral i"]) simp

lemma two_pow_float[simp]: "2 ^ n \<in> float"
  by (intro floatI[of 1 n]) (simp add: powr_realpow)


lemma plus_float[simp]: "r \<in> float \<Longrightarrow> p \<in> float \<Longrightarrow> r + p \<in> float"
  unfolding float_def
proof (safe, simp)
  have *: "\<exists>(m::int) (e::int). m1 * 2 powr e1 + m2 * 2 powr e2 = m * 2 powr e"
    if "e1 \<le> e2" for e1 m1 e2 m2 :: int
  proof -
    from that have "m1 * 2 powr e1 + m2 * 2 powr e2 = (m1 + m2 * 2 ^ nat (e2 - e1)) * 2 powr e1"
      by (simp add: powr_diff field_simps flip: powr_realpow)
    then show ?thesis
      by blast
  qed
  fix e1 m1 e2 m2 :: int
  consider "e2 \<le> e1" | "e1 \<le> e2" by (rule linorder_le_cases)
  then show "\<exists>(m::int) (e::int). m1 * 2 powr e1 + m2 * 2 powr e2 = m * 2 powr e"
  proof cases
    case 1
    from *[OF this, of m2 m1] show ?thesis
      by (simp add: ac_simps)
  next
    case 2
    then show ?thesis by (rule *)
  qed
qed

lemma uminus_float[simp]: "x \<in> float \<Longrightarrow> -x \<in> float"
  apply (auto simp: float_def)
  apply hypsubst_thin
  apply (rename_tac m e)
  apply (rule_tac x="-m" in exI)
  apply (rule_tac x="e" in exI)
  apply (simp add: field_simps)
  done

lemma times_float[simp]: "x \<in> float \<Longrightarrow> y \<in> float \<Longrightarrow> x * y \<in> float"
  apply (auto simp: float_def)
  apply hypsubst_thin
  apply (rename_tac mx my ex ey)
  apply (rule_tac x="mx * my" in exI)
  apply (rule_tac x="ex + ey" in exI)
  apply (simp add: powr_add)
  done

lemma minus_float[simp]: "x \<in> float \<Longrightarrow> y \<in> float \<Longrightarrow> x - y \<in> float"
  using plus_float [of x "- y"] by simp

lemma abs_float[simp]: "x \<in> float \<Longrightarrow> \<bar>x\<bar> \<in> float"
  by (cases x rule: linorder_cases[of 0]) auto

lemma sgn_of_float[simp]: "x \<in> float \<Longrightarrow> sgn x \<in> float"
  by (cases x rule: linorder_cases[of 0]) (auto intro!: uminus_float)

lemma div_power_2_float[simp]: "x \<in> float \<Longrightarrow> x / 2^d \<in> float"
  apply (auto simp add: float_def)
  apply hypsubst_thin
  apply (rename_tac m e)
  apply (rule_tac x="m" in exI)
  apply (rule_tac x="e - d" in exI)
  apply (simp flip: powr_realpow powr_add add: field_simps)
  done

lemma div_power_2_int_float[simp]: "x \<in> float \<Longrightarrow> x / (2::int)^d \<in> float"
  apply (auto simp add: float_def)
  apply hypsubst_thin
  apply (rename_tac m e)
  apply (rule_tac x="m" in exI)
  apply (rule_tac x="e - d" in exI)
  apply (simp flip: powr_realpow powr_add add: field_simps)
  done

lemma div_numeral_Bit0_float[simp]:
  assumes "x / numeral n \<in> float"
  shows "x / (numeral (Num.Bit0 n)) \<in> float"
proof -
  have "(x / numeral n) / 2^1 \<in> float"
    by (intro assms div_power_2_float)
  also have "(x / numeral n) / 2^1 = x / (numeral (Num.Bit0 n))"
    by (induct n) auto
  finally show ?thesis .
qed

lemma div_neg_numeral_Bit0_float[simp]:
  assumes "x / numeral n \<in> float"
  shows "x / (- numeral (Num.Bit0 n)) \<in> float"
proof -
  have "- (x / numeral (Num.Bit0 n)) \<in> float"
    using assms by simp
  also have "- (x / numeral (Num.Bit0 n)) = x / - numeral (Num.Bit0 n)"
    by simp
  finally show ?thesis .
qed

lemma power_float[simp]:
  assumes "a \<in> float"
  shows "a ^ b \<in> float"
proof -
  from assms obtain m e :: int where "a = m * 2 powr e"
    by (auto simp: float_def)
  then show ?thesis
    by (auto intro!: floatI[where m="m^b" and e = "e*b"]
      simp: power_mult_distrib powr_realpow[symmetric] powr_powr)
qed

lift_definition Float :: "int \<Rightarrow> int \<Rightarrow> float" is "\<lambda>(m::int) (e::int). m * 2 powr e"
  by simp
declare Float.rep_eq[simp]

code_datatype Float

lemma compute_real_of_float[code]:
  "real_of_float (Float m e) = (if e \<ge> 0 then m * 2 ^ nat e else m / 2 ^ (nat (-e)))"
  by (simp add: powr_int)


subsection \<open>Arithmetic operations on floating point numbers\<close>

instantiation float :: "{ring_1,linorder,linordered_ring,linordered_idom,numeral,equal}"
begin

lift_definition zero_float :: float is 0 by simp
declare zero_float.rep_eq[simp]

lift_definition one_float :: float is 1 by simp
declare one_float.rep_eq[simp]

lift_definition plus_float :: "float \<Rightarrow> float \<Rightarrow> float" is "(+)" by simp
declare plus_float.rep_eq[simp]

lift_definition times_float :: "float \<Rightarrow> float \<Rightarrow> float" is "(*)" by simp
declare times_float.rep_eq[simp]

lift_definition minus_float :: "float \<Rightarrow> float \<Rightarrow> float" is "(-)" by simp
declare minus_float.rep_eq[simp]

lift_definition uminus_float :: "float \<Rightarrow> float" is "uminus" by simp
declare uminus_float.rep_eq[simp]

lift_definition abs_float :: "float \<Rightarrow> float" is abs by simp
declare abs_float.rep_eq[simp]

lift_definition sgn_float :: "float \<Rightarrow> float" is sgn by simp
declare sgn_float.rep_eq[simp]

lift_definition equal_float :: "float \<Rightarrow> float \<Rightarrow> bool" is "(=) :: real \<Rightarrow> real \<Rightarrow> bool" .

lift_definition less_eq_float :: "float \<Rightarrow> float \<Rightarrow> bool" is "(\<le>)" .
declare less_eq_float.rep_eq[simp]

lift_definition less_float :: "float \<Rightarrow> float \<Rightarrow> bool" is "(<)" .
declare less_float.rep_eq[simp]

instance
  by standard (transfer; fastforce simp add: field_simps intro: mult_left_mono mult_right_mono)+

end

lemma real_of_float [simp]: "real_of_float (of_nat n) = of_nat n"
  by (induct n) simp_all

lemma real_of_float_of_int_eq [simp]: "real_of_float (of_int z) = of_int z"
  by (cases z rule: int_diff_cases) (simp_all add: of_rat_diff)

lemma Float_0_eq_0[simp]: "Float 0 e = 0"
  by transfer simp

lemma real_of_float_power[simp]: "real_of_float (f^n) = real_of_float f^n" for f :: float
  by (induct n) simp_all

lemma real_of_float_min: "real_of_float (min x y) = min (real_of_float x) (real_of_float y)"
  and real_of_float_max: "real_of_float (max x y) = max (real_of_float x) (real_of_float y)"
  for x y :: float
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
  show "\<exists>c. a < c \<and> c < b" if "a < b"
    apply (rule exI[of _ "(a + b) * Float 1 (- 1)"])
    using that
    apply transfer
    apply (simp add: powr_minus)
    done
qed

instantiation float :: lattice_ab_group_add
begin

definition inf_float :: "float \<Rightarrow> float \<Rightarrow> float"
  where "inf_float a b = min a b"

definition sup_float :: "float \<Rightarrow> float \<Rightarrow> float"
  where "sup_float a b = max a b"

instance
  by standard (transfer; simp add: inf_float_def sup_float_def real_of_float_min real_of_float_max)+

end

lemma float_numeral[simp]: "real_of_float (numeral x :: float) = numeral x"
  apply (induct x)
  apply simp
  apply (simp_all only: numeral_Bit0 numeral_Bit1 real_of_float_eq float_of_inverse
          plus_float.rep_eq one_float.rep_eq plus_float numeral_float one_float)
  done

lemma transfer_numeral [transfer_rule]:
  "rel_fun (=) pcr_float (numeral :: _ \<Rightarrow> real) (numeral :: _ \<Rightarrow> float)"
  by (simp add: rel_fun_def float.pcr_cr_eq cr_float_def)

lemma float_neg_numeral[simp]: "real_of_float (- numeral x :: float) = - numeral x"
  by simp

lemma transfer_neg_numeral [transfer_rule]:
  "rel_fun (=) pcr_float (- numeral :: _ \<Rightarrow> real) (- numeral :: _ \<Rightarrow> float)"
  by (simp add: rel_fun_def float.pcr_cr_eq cr_float_def)

lemma float_of_numeral: "numeral k = float_of (numeral k)"
  and float_of_neg_numeral: "- numeral k = float_of (- numeral k)"
  unfolding real_of_float_eq by simp_all


subsection \<open>Quickcheck\<close>

instantiation float :: exhaustive
begin

definition exhaustive_float where
  "exhaustive_float f d =
    Quickcheck_Exhaustive.exhaustive (\<lambda>x. Quickcheck_Exhaustive.exhaustive (\<lambda>y. f (Float x y)) d) d"

instance ..

end

context
  includes term_syntax
begin

definition [code_unfold]:
  "valtermify_float x y = Code_Evaluation.valtermify Float {\<cdot>} x {\<cdot>} y"

end

instantiation float :: full_exhaustive
begin

definition
  "full_exhaustive_float f d =
    Quickcheck_Exhaustive.full_exhaustive
      (\<lambda>x. Quickcheck_Exhaustive.full_exhaustive (\<lambda>y. f (valtermify_float x y)) d) d"

instance ..

end

instantiation float :: random
begin

definition "Quickcheck_Random.random i =
  scomp (Quickcheck_Random.random (2 ^ nat_of_natural i))
    (\<lambda>man. scomp (Quickcheck_Random.random i) (\<lambda>exp. Pair (valtermify_float man exp)))"

instance ..

end


subsection \<open>Represent floats as unique mantissa and exponent\<close>

lemma int_induct_abs[case_names less]:
  fixes j :: int
  assumes H: "\<And>n. (\<And>i. \<bar>i\<bar> < \<bar>n\<bar> \<Longrightarrow> P i) \<Longrightarrow> P n"
  shows "P j"
proof (induct "nat \<bar>j\<bar>" arbitrary: j rule: less_induct)
  case less
  show ?case by (rule H[OF less]) simp
qed

lemma int_cancel_factors:
  fixes n :: int
  assumes "1 < r"
  shows "n = 0 \<or> (\<exists>k i. n = k * r ^ i \<and> \<not> r dvd k)"
proof (induct n rule: int_induct_abs)
  case (less n)
  have "\<exists>k i. n = k * r ^ Suc i \<and> \<not> r dvd k" if "n \<noteq> 0" "n = m * r" for m
  proof -
    from that have "\<bar>m \<bar> < \<bar>n\<bar>"
      using \<open>1 < r\<close> by (simp add: abs_mult)
    from less[OF this] that show ?thesis by auto
  qed
  then show ?case
    by (metis dvd_def monoid_mult_class.mult.right_neutral mult.commute power_0)
qed

lemma mult_powr_eq_mult_powr_iff_asym:
  fixes m1 m2 e1 e2 :: int
  assumes m1: "\<not> 2 dvd m1"
    and "e1 \<le> e2"
  shows "m1 * 2 powr e1 = m2 * 2 powr e2 \<longleftrightarrow> m1 = m2 \<and> e1 = e2"
  (is "?lhs \<longleftrightarrow> ?rhs")
proof
  show ?rhs if eq: ?lhs
  proof -
    have "m1 \<noteq> 0"
      using m1 unfolding dvd_def by auto
    from \<open>e1 \<le> e2\<close> eq have "m1 = m2 * 2 powr nat (e2 - e1)"
      by (simp add: powr_diff field_simps)
    also have "\<dots> = m2 * 2^nat (e2 - e1)"
      by (simp add: powr_realpow)
    finally have m1_eq: "m1 = m2 * 2^nat (e2 - e1)"
      by linarith
    with m1 have "m1 = m2"
      by (cases "nat (e2 - e1)") (auto simp add: dvd_def)
    then show ?thesis
      using eq \<open>m1 \<noteq> 0\<close> by (simp add: powr_inj)
  qed
  show ?lhs if ?rhs
    using that by simp
qed

lemma mult_powr_eq_mult_powr_iff:
  "\<not> 2 dvd m1 \<Longrightarrow> \<not> 2 dvd m2 \<Longrightarrow> m1 * 2 powr e1 = m2 * 2 powr e2 \<longleftrightarrow> m1 = m2 \<and> e1 = e2"
  for m1 m2 e1 e2 :: int
  using mult_powr_eq_mult_powr_iff_asym[of m1 e1 e2 m2]
  using mult_powr_eq_mult_powr_iff_asym[of m2 e2 e1 m1]
  by (cases e1 e2 rule: linorder_le_cases) auto

lemma floatE_normed:
  assumes x: "x \<in> float"
  obtains (zero) "x = 0"
   | (powr) m e :: int where "x = m * 2 powr e" "\<not> 2 dvd m" "x \<noteq> 0"
proof -
  have "\<exists>(m::int) (e::int). x = m * 2 powr e \<and> \<not> (2::int) dvd m" if "x \<noteq> 0"
  proof -
    from x obtain m e :: int where x: "x = m * 2 powr e"
      by (auto simp: float_def)
    with \<open>x \<noteq> 0\<close> int_cancel_factors[of 2 m] obtain k i where "m = k * 2 ^ i" "\<not> 2 dvd k"
      by auto
    with \<open>\<not> 2 dvd k\<close> x show ?thesis
      apply (rule_tac exI[of _ "k"])
      apply (rule_tac exI[of _ "e + int i"])
      apply (simp add: powr_add powr_realpow)
      done
  qed
  with that show thesis by blast
qed

lemma float_normed_cases:
  fixes f :: float
  obtains (zero) "f = 0"
   | (powr) m e :: int where "real_of_float f = m * 2 powr e" "\<not> 2 dvd m" "f \<noteq> 0"
proof (atomize_elim, induct f)
  case (float_of y)
  then show ?case
    by (cases rule: floatE_normed) (auto simp: zero_float_def)
qed

definition mantissa :: "float \<Rightarrow> int"
  where "mantissa f =
    fst (SOME p::int \<times> int. (f = 0 \<and> fst p = 0 \<and> snd p = 0) \<or>
      (f \<noteq> 0 \<and> real_of_float f = real_of_int (fst p) * 2 powr real_of_int (snd p) \<and> \<not> 2 dvd fst p))"

definition exponent :: "float \<Rightarrow> int"
  where "exponent f =
    snd (SOME p::int \<times> int. (f = 0 \<and> fst p = 0 \<and> snd p = 0) \<or>
      (f \<noteq> 0 \<and> real_of_float f = real_of_int (fst p) * 2 powr real_of_int (snd p) \<and> \<not> 2 dvd fst p))"

lemma exponent_0[simp]: "exponent 0 = 0" (is ?E)
  and mantissa_0[simp]: "mantissa 0 = 0" (is ?M)
proof -
  have "\<And>p::int \<times> int. fst p = 0 \<and> snd p = 0 \<longleftrightarrow> p = (0, 0)"
    by auto
  then show ?E ?M
    by (auto simp add: mantissa_def exponent_def zero_float_def)
qed

lemma mantissa_exponent: "real_of_float f = mantissa f * 2 powr exponent f" (is ?E)
  and mantissa_not_dvd: "f \<noteq> 0 \<Longrightarrow> \<not> 2 dvd mantissa f" (is "_ \<Longrightarrow> ?D")
proof cases
  assume [simp]: "f \<noteq> 0"
  have "f = mantissa f * 2 powr exponent f \<and> \<not> 2 dvd mantissa f"
  proof (cases f rule: float_normed_cases)
    case zero
    then show ?thesis by simp
  next
    case (powr m e)
    then have "\<exists>p::int \<times> int. (f = 0 \<and> fst p = 0 \<and> snd p = 0) \<or>
      (f \<noteq> 0 \<and> real_of_float f = real_of_int (fst p) * 2 powr real_of_int (snd p) \<and> \<not> 2 dvd fst p)"
      by auto
    then show ?thesis
      unfolding exponent_def mantissa_def
      by (rule someI2_ex) simp
  qed
  then show ?E ?D by auto
qed simp

lemma mantissa_noteq_0: "f \<noteq> 0 \<Longrightarrow> mantissa f \<noteq> 0"
  using mantissa_not_dvd[of f] by auto

lemma mantissa_eq_zero_iff: "mantissa x = 0 \<longleftrightarrow> x = 0"
  (is "?lhs \<longleftrightarrow> ?rhs")
proof
  show ?rhs if ?lhs
  proof -
    from that have z: "0 = real_of_float x"
      using mantissa_exponent by simp
    show ?thesis
      by (simp add: zero_float_def z)
  qed
  show ?lhs if ?rhs
    using that by simp
qed

lemma mantissa_pos_iff: "0 < mantissa x \<longleftrightarrow> 0 < x"
  by (auto simp: mantissa_exponent algebra_split_simps)

lemma mantissa_nonneg_iff: "0 \<le> mantissa x \<longleftrightarrow> 0 \<le> x"
  by (auto simp: mantissa_exponent algebra_split_simps)

lemma mantissa_neg_iff: "0 > mantissa x \<longleftrightarrow> 0 > x"
  by (auto simp: mantissa_exponent algebra_split_simps)

lemma
  fixes m e :: int
  defines "f \<equiv> float_of (m * 2 powr e)"
  assumes dvd: "\<not> 2 dvd m"
  shows mantissa_float: "mantissa f = m" (is "?M")
    and exponent_float: "m \<noteq> 0 \<Longrightarrow> exponent f = e" (is "_ \<Longrightarrow> ?E")
proof cases
  assume "m = 0"
  with dvd show "mantissa f = m" by auto
next
  assume "m \<noteq> 0"
  then have f_not_0: "f \<noteq> 0" by (simp add: f_def zero_float_def)
  from mantissa_exponent[of f] have "m * 2 powr e = mantissa f * 2 powr exponent f"
    by (auto simp add: f_def)
  then show ?M ?E
    using mantissa_not_dvd[OF f_not_0] dvd
    by (auto simp: mult_powr_eq_mult_powr_iff)
qed


subsection \<open>Compute arithmetic operations\<close>

lemma Float_mantissa_exponent: "Float (mantissa f) (exponent f) = f"
  unfolding real_of_float_eq mantissa_exponent[of f] by simp

lemma Float_cases [cases type: float]:
  fixes f :: float
  obtains (Float) m e :: int where "f = Float m e"
  using Float_mantissa_exponent[symmetric]
  by (atomize_elim) auto

lemma denormalize_shift:
  assumes f_def: "f = Float m e"
    and not_0: "f \<noteq> 0"
  obtains i where "m = mantissa f * 2 ^ i" "e = exponent f - i"
proof
  from mantissa_exponent[of f] f_def
  have "m * 2 powr e = mantissa f * 2 powr exponent f"
    by simp
  then have eq: "m = mantissa f * 2 powr (exponent f - e)"
    by (simp add: powr_diff field_simps)
  moreover
  have "e \<le> exponent f"
  proof (rule ccontr)
    assume "\<not> e \<le> exponent f"
    then have pos: "exponent f < e" by simp
    then have "2 powr (exponent f - e) = 2 powr - real_of_int (e - exponent f)"
      by simp
    also have "\<dots> = 1 / 2^nat (e - exponent f)"
      using pos by (simp flip: powr_realpow add: powr_diff)
    finally have "m * 2^nat (e - exponent f) = real_of_int (mantissa f)"
      using eq by simp
    then have "mantissa f = m * 2^nat (e - exponent f)"
      by linarith
    with \<open>exponent f < e\<close> have "2 dvd mantissa f"
      apply (intro dvdI[where k="m * 2^(nat (e-exponent f)) div 2"])
      apply (cases "nat (e - exponent f)")
      apply auto
      done
    then show False using mantissa_not_dvd[OF not_0] by simp
  qed
  ultimately have "real_of_int m = mantissa f * 2^nat (exponent f - e)"
    by (simp flip: powr_realpow)
  with \<open>e \<le> exponent f\<close>
  show "m = mantissa f * 2 ^ nat (exponent f - e)"
    by linarith
  show "e = exponent f - nat (exponent f - e)"
    using \<open>e \<le> exponent f\<close> by auto
qed

context
begin

qualified lemma compute_float_zero[code_unfold, code]: "0 = Float 0 0"
  by transfer simp

qualified lemma compute_float_one[code_unfold, code]: "1 = Float 1 0"
  by transfer simp

lift_definition normfloat :: "float \<Rightarrow> float" is "\<lambda>x. x" .
lemma normloat_id[simp]: "normfloat x = x" by transfer rule

qualified lemma compute_normfloat[code]:
  "normfloat (Float m e) =
    (if m mod 2 = 0 \<and> m \<noteq> 0 then normfloat (Float (m div 2) (e + 1))
     else if m = 0 then 0 else Float m e)"
  by transfer (auto simp add: powr_add zmod_eq_0_iff)

qualified lemma compute_float_numeral[code_abbrev]: "Float (numeral k) 0 = numeral k"
  by transfer simp

qualified lemma compute_float_neg_numeral[code_abbrev]: "Float (- numeral k) 0 = - numeral k"
  by transfer simp

qualified lemma compute_float_uminus[code]: "- Float m1 e1 = Float (- m1) e1"
  by transfer simp

qualified lemma compute_float_times[code]: "Float m1 e1 * Float m2 e2 = Float (m1 * m2) (e1 + e2)"
  by transfer (simp add: field_simps powr_add)

qualified lemma compute_float_plus[code]:
  "Float m1 e1 + Float m2 e2 =
    (if m1 = 0 then Float m2 e2
     else if m2 = 0 then Float m1 e1
     else if e1 \<le> e2 then Float (m1 + m2 * 2^nat (e2 - e1)) e1
     else Float (m2 + m1 * 2^nat (e1 - e2)) e2)"
  by transfer (simp add: field_simps powr_realpow[symmetric] powr_diff)

qualified lemma compute_float_minus[code]: "f - g = f + (-g)" for f g :: float
  by simp

qualified lemma compute_float_sgn[code]:
  "sgn (Float m1 e1) = (if 0 < m1 then 1 else if m1 < 0 then -1 else 0)"
  by transfer (simp add: sgn_mult)

lift_definition is_float_pos :: "float \<Rightarrow> bool" is "(<) 0 :: real \<Rightarrow> bool" .

qualified lemma compute_is_float_pos[code]: "is_float_pos (Float m e) \<longleftrightarrow> 0 < m"
  by transfer (auto simp add: zero_less_mult_iff not_le[symmetric, of _ 0])

lift_definition is_float_nonneg :: "float \<Rightarrow> bool" is "(\<le>) 0 :: real \<Rightarrow> bool" .

qualified lemma compute_is_float_nonneg[code]: "is_float_nonneg (Float m e) \<longleftrightarrow> 0 \<le> m"
  by transfer (auto simp add: zero_le_mult_iff not_less[symmetric, of _ 0])

lift_definition is_float_zero :: "float \<Rightarrow> bool"  is "(=) 0 :: real \<Rightarrow> bool" .

qualified lemma compute_is_float_zero[code]: "is_float_zero (Float m e) \<longleftrightarrow> 0 = m"
  by transfer (auto simp add: is_float_zero_def)

qualified lemma compute_float_abs[code]: "\<bar>Float m e\<bar> = Float \<bar>m\<bar> e"
  by transfer (simp add: abs_mult)

qualified lemma compute_float_eq[code]: "equal_class.equal f g = is_float_zero (f - g)"
  by transfer simp

end


subsection \<open>Lemmas for types \<^typ>\<open>real\<close>, \<^typ>\<open>nat\<close>, \<^typ>\<open>int\<close>\<close>

lemmas real_of_ints =
  of_int_add
  of_int_minus
  of_int_diff
  of_int_mult
  of_int_power
  of_int_numeral of_int_neg_numeral

lemmas int_of_reals = real_of_ints[symmetric]


subsection \<open>Rounding Real Numbers\<close>

definition round_down :: "int \<Rightarrow> real \<Rightarrow> real"
  where "round_down prec x = \<lfloor>x * 2 powr prec\<rfloor> * 2 powr -prec"

definition round_up :: "int \<Rightarrow> real \<Rightarrow> real"
  where "round_up prec x = \<lceil>x * 2 powr prec\<rceil> * 2 powr -prec"

lemma round_down_float[simp]: "round_down prec x \<in> float"
  unfolding round_down_def
  by (auto intro!: times_float simp flip: of_int_minus)

lemma round_up_float[simp]: "round_up prec x \<in> float"
  unfolding round_up_def
  by (auto intro!: times_float simp flip: of_int_minus)

lemma round_up: "x \<le> round_up prec x"
  by (simp add: powr_minus_divide le_divide_eq round_up_def ceiling_correct)

lemma round_down: "round_down prec x \<le> x"
  by (simp add: powr_minus_divide divide_le_eq round_down_def)

lemma round_up_0[simp]: "round_up p 0 = 0"
  unfolding round_up_def by simp

lemma round_down_0[simp]: "round_down p 0 = 0"
  unfolding round_down_def by simp

lemma round_up_diff_round_down: "round_up prec x - round_down prec x \<le> 2 powr -prec"
proof -
  have "round_up prec x - round_down prec x = (\<lceil>x * 2 powr prec\<rceil> - \<lfloor>x * 2 powr prec\<rfloor>) * 2 powr -prec"
    by (simp add: round_up_def round_down_def field_simps)
  also have "\<dots> \<le> 1 * 2 powr -prec"
    by (rule mult_mono)
      (auto simp flip: of_int_diff simp: ceiling_diff_floor_le_1)
  finally show ?thesis by simp
qed

lemma round_down_shift: "round_down p (x * 2 powr k) = 2 powr k * round_down (p + k) x"
  unfolding round_down_def
  by (simp add: powr_add powr_mult field_simps powr_diff)
    (simp flip: powr_add)

lemma round_up_shift: "round_up p (x * 2 powr k) = 2 powr k * round_up (p + k) x"
  unfolding round_up_def
  by (simp add: powr_add powr_mult field_simps powr_diff)
    (simp flip: powr_add)

lemma round_up_uminus_eq: "round_up p (-x) = - round_down p x"
  and round_down_uminus_eq: "round_down p (-x) = - round_up p x"
  by (auto simp: round_up_def round_down_def ceiling_def)

lemma round_up_mono: "x \<le> y \<Longrightarrow> round_up p x \<le> round_up p y"
  by (auto intro!: ceiling_mono simp: round_up_def)

lemma round_up_le1:
  assumes "x \<le> 1" "prec \<ge> 0"
  shows "round_up prec x \<le> 1"
proof -
  have "real_of_int \<lceil>x * 2 powr prec\<rceil> \<le> real_of_int \<lceil>2 powr real_of_int prec\<rceil>"
    using assms by (auto intro!: ceiling_mono)
  also have "\<dots> = 2 powr prec" using assms by (auto simp: powr_int intro!: exI[where x="2^nat prec"])
  finally show ?thesis
    by (simp add: round_up_def) (simp add: powr_minus inverse_eq_divide)
qed

lemma round_up_less1:
  assumes "x < 1 / 2" "p > 0"
  shows "round_up p x < 1"
proof -
  have "x * 2 powr p < 1 / 2 * 2 powr p"
    using assms by simp
  also have "\<dots> \<le> 2 powr p - 1" using \<open>p > 0\<close>
    by (auto simp: powr_diff powr_int field_simps self_le_power)
  finally show ?thesis using \<open>p > 0\<close>
    by (simp add: round_up_def field_simps powr_minus powr_int ceiling_less_iff)
qed

lemma round_down_ge1:
  assumes x: "x \<ge> 1"
  assumes prec: "p \<ge> - log 2 x"
  shows "1 \<le> round_down p x"
proof cases
  assume nonneg: "0 \<le> p"
  have "2 powr p = real_of_int \<lfloor>2 powr real_of_int p\<rfloor>"
    using nonneg by (auto simp: powr_int)
  also have "\<dots> \<le> real_of_int \<lfloor>x * 2 powr p\<rfloor>"
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

  from neg have "2 powr real_of_int p \<le> 2 powr 0"
    by (intro powr_mono) auto
  also have "\<dots> \<le> \<lfloor>2 powr 0::real\<rfloor>" by simp
  also have "\<dots> \<le> \<lfloor>x * 2 powr (real_of_int p)\<rfloor>"
    unfolding of_int_le_iff
    using x x_le by (intro floor_mono) (simp add: powr_minus_divide field_simps)
  finally show ?thesis
    using prec x
    by (simp add: round_down_def powr_minus_divide pos_le_divide_eq)
qed

lemma round_up_le0: "x \<le> 0 \<Longrightarrow> round_up p x \<le> 0"
  unfolding round_up_def
  by (auto simp: field_simps mult_le_0_iff zero_le_mult_iff)


subsection \<open>Rounding Floats\<close>

definition div_twopow :: "int \<Rightarrow> nat \<Rightarrow> int"
  where [simp]: "div_twopow x n = x div (2 ^ n)"

definition mod_twopow :: "int \<Rightarrow> nat \<Rightarrow> int"
  where [simp]: "mod_twopow x n = x mod (2 ^ n)"

lemma compute_div_twopow[code]:
  "div_twopow x n = (if x = 0 \<or> x = -1 \<or> n = 0 then x else div_twopow (x div 2) (n - 1))"
  by (cases n) (auto simp: zdiv_zmult2_eq div_eq_minus1)

lemma compute_mod_twopow[code]:
  "mod_twopow x n = (if n = 0 then 0 else x mod 2 + 2 * mod_twopow (x div 2) (n - 1))"
  by (cases n) (auto simp: zmod_zmult2_eq)

lift_definition float_up :: "int \<Rightarrow> float \<Rightarrow> float" is round_up by simp
declare float_up.rep_eq[simp]

lemma round_up_correct: "round_up e f - f \<in> {0..2 powr -e}"
  unfolding atLeastAtMost_iff
proof
  have "round_up e f - f \<le> round_up e f - round_down e f"
    using round_down by simp
  also have "\<dots> \<le> 2 powr -e"
    using round_up_diff_round_down by simp
  finally show "round_up e f - f \<le> 2 powr - (real_of_int e)"
    by simp
qed (simp add: algebra_simps round_up)

lemma float_up_correct: "real_of_float (float_up e f) - real_of_float f \<in> {0..2 powr -e}"
  by transfer (rule round_up_correct)

lift_definition float_down :: "int \<Rightarrow> float \<Rightarrow> float" is round_down by simp
declare float_down.rep_eq[simp]

lemma round_down_correct: "f - (round_down e f) \<in> {0..2 powr -e}"
  unfolding atLeastAtMost_iff
proof
  have "f - round_down e f \<le> round_up e f - round_down e f"
    using round_up by simp
  also have "\<dots> \<le> 2 powr -e"
    using round_up_diff_round_down by simp
  finally show "f - round_down e f \<le> 2 powr - (real_of_int e)"
    by simp
qed (simp add: algebra_simps round_down)

lemma float_down_correct: "real_of_float f - real_of_float (float_down e f) \<in> {0..2 powr -e}"
  by transfer (rule round_down_correct)

context
begin

qualified lemma compute_float_down[code]:
  "float_down p (Float m e) =
    (if p + e < 0 then Float (div_twopow m (nat (-(p + e)))) (-p) else Float m e)"
proof (cases "p + e < 0")
  case True
  then have "real_of_int ((2::int) ^ nat (-(p + e))) = 2 powr (-(p + e))"
    using powr_realpow[of 2 "nat (-(p + e))"] by simp
  also have "\<dots> = 1 / 2 powr p / 2 powr e"
    unfolding powr_minus_divide of_int_minus by (simp add: powr_add)
  finally show ?thesis
    using \<open>p + e < 0\<close>
    apply transfer
    apply (simp add: round_down_def field_simps flip: floor_divide_of_int_eq)
    apply (metis (no_types, hide_lams) Float.rep_eq
      add.inverse_inverse compute_real_of_float diff_minus_eq_add
      floor_divide_of_int_eq int_of_reals(1) linorder_not_le
      minus_add_distrib of_int_eq_numeral_power_cancel_iff powr_add)
    done
next
  case False
  then have r: "real_of_int e + real_of_int p = real (nat (e + p))"
    by simp
  have r: "\<lfloor>(m * 2 powr e) * 2 powr real_of_int p\<rfloor> = (m * 2 powr e) * 2 powr real_of_int p"
    by (auto intro: exI[where x="m*2^nat (e+p)"]
        simp add: ac_simps powr_add[symmetric] r powr_realpow)
  with \<open>\<not> p + e < 0\<close> show ?thesis
    by transfer (auto simp add: round_down_def field_simps powr_add powr_minus)
qed

lemma abs_round_down_le: "\<bar>f - (round_down e f)\<bar> \<le> 2 powr -e"
  using round_down_correct[of f e] by simp

lemma abs_round_up_le: "\<bar>f - (round_up e f)\<bar> \<le> 2 powr -e"
  using round_up_correct[of e f] by simp

lemma round_down_nonneg: "0 \<le> s \<Longrightarrow> 0 \<le> round_down p s"
  by (auto simp: round_down_def)

lemma ceil_divide_floor_conv:
  assumes "b \<noteq> 0"
  shows "\<lceil>real_of_int a / real_of_int b\<rceil> =
    (if b dvd a then a div b else \<lfloor>real_of_int a / real_of_int b\<rfloor> + 1)"
proof (cases "b dvd a")
  case True
  then show ?thesis
    by (simp add: ceiling_def floor_divide_of_int_eq dvd_neg_div
             flip: of_int_minus divide_minus_left)
next
  case False
  then have "a mod b \<noteq> 0"
    by auto
  then have ne: "real_of_int (a mod b) / real_of_int b \<noteq> 0"
    using \<open>b \<noteq> 0\<close> by auto
  have "\<lceil>real_of_int a / real_of_int b\<rceil> = \<lfloor>real_of_int a / real_of_int b\<rfloor> + 1"
    apply (rule ceiling_eq)
    apply (auto simp flip: floor_divide_of_int_eq)
  proof -
    have "real_of_int \<lfloor>real_of_int a / real_of_int b\<rfloor> \<le> real_of_int a / real_of_int b"
      by simp
    moreover have "real_of_int \<lfloor>real_of_int a / real_of_int b\<rfloor> \<noteq> real_of_int a / real_of_int b"
      apply (subst (2) real_of_int_div_aux)
      unfolding floor_divide_of_int_eq
      using ne \<open>b \<noteq> 0\<close> apply auto
      done
    ultimately show "real_of_int \<lfloor>real_of_int a / real_of_int b\<rfloor> < real_of_int a / real_of_int b" by arith
  qed
  then show ?thesis
    using \<open>\<not> b dvd a\<close> by simp
qed

qualified lemma compute_float_up[code]: "float_up p x = - float_down p (-x)"
  by transfer (simp add: round_down_uminus_eq)

end


lemma bitlen_Float:
  fixes m e
  defines [THEN meta_eq_to_obj_eq]: "f \<equiv> Float m e"
  shows "bitlen \<bar>mantissa f\<bar> + exponent f = (if m = 0 then 0 else bitlen \<bar>m\<bar> + e)"
proof (cases "m = 0")
  case True
  then show ?thesis by (simp add: f_def bitlen_alt_def)
next
  case False
  then have "f \<noteq> 0"
    unfolding real_of_float_eq by (simp add: f_def)
  then have "mantissa f \<noteq> 0"
    by (simp add: mantissa_eq_zero_iff)
  moreover
  obtain i where "m = mantissa f * 2 ^ i" "e = exponent f - int i"
    by (rule f_def[THEN denormalize_shift, OF \<open>f \<noteq> 0\<close>])
  ultimately show ?thesis by (simp add: abs_mult)
qed

lemma float_gt1_scale:
  assumes "1 \<le> Float m e"
  shows "0 \<le> e + (bitlen m - 1)"
proof -
  have "0 < Float m e" using assms by auto
  then have "0 < m" using powr_gt_zero[of 2 e]
    by (auto simp: zero_less_mult_iff)
  then have "m \<noteq> 0" by auto
  show ?thesis
  proof (cases "0 \<le> e")
    case True
    then show ?thesis
      using \<open>0 < m\<close> by (simp add: bitlen_alt_def)
  next
    case False
    have "(1::int) < 2" by simp
    let ?S = "2^(nat (-e))"
    have "inverse (2 ^ nat (- e)) = 2 powr e"
      using assms False powr_realpow[of 2 "nat (-e)"]
      by (auto simp: powr_minus field_simps)
    then have "1 \<le> real_of_int m * inverse ?S"
      using assms False powr_realpow[of 2 "nat (-e)"]
      by (auto simp: powr_minus)
    then have "1 * ?S \<le> real_of_int m * inverse ?S * ?S"
      by (rule mult_right_mono) auto
    then have "?S \<le> real_of_int m"
      unfolding mult.assoc by auto
    then have "?S \<le> m"
      unfolding of_int_le_iff[symmetric] by auto
    from this bitlen_bounds[OF \<open>0 < m\<close>, THEN conjunct2]
    have "nat (-e) < (nat (bitlen m))"
      unfolding power_strict_increasing_iff[OF \<open>1 < 2\<close>, symmetric]
      by (rule order_le_less_trans)
    then have "-e < bitlen m"
      using False by auto
    then show ?thesis
      by auto
  qed
qed


subsection \<open>Truncating Real Numbers\<close>

definition truncate_down::"nat \<Rightarrow> real \<Rightarrow> real"
  where "truncate_down prec x = round_down (prec - \<lfloor>log 2 \<bar>x\<bar>\<rfloor>) x"

lemma truncate_down: "truncate_down prec x \<le> x"
  using round_down by (simp add: truncate_down_def)

lemma truncate_down_le: "x \<le> y \<Longrightarrow> truncate_down prec x \<le> y"
  by (rule order_trans[OF truncate_down])

lemma truncate_down_zero[simp]: "truncate_down prec 0 = 0"
  by (simp add: truncate_down_def)

lemma truncate_down_float[simp]: "truncate_down p x \<in> float"
  by (auto simp: truncate_down_def)

definition truncate_up::"nat \<Rightarrow> real \<Rightarrow> real"
  where "truncate_up prec x = round_up (prec - \<lfloor>log 2 \<bar>x\<bar>\<rfloor>) x"

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
  assumes "x > 0"
  shows "truncate_down p x > 0"
proof -
  have "0 \<le> log 2 x - real_of_int \<lfloor>log 2 x\<rfloor>"
    by (simp add: algebra_simps)
  with assms
  show ?thesis
    apply (auto simp: truncate_down_def round_down_def mult_powr_eq
      intro!: ge_one_powr_ge_zero mult_pos_pos)
    by linarith
qed

lemma truncate_down_nonneg: "0 \<le> y \<Longrightarrow> 0 \<le> truncate_down prec y"
  by (auto simp: truncate_down_def round_down_def)

lemma truncate_down_ge1: "1 \<le> x \<Longrightarrow> 1 \<le> truncate_down p x"
  apply (auto simp: truncate_down_def algebra_simps intro!: round_down_ge1)
  apply linarith
  done

lemma truncate_up_nonpos: "x \<le> 0 \<Longrightarrow> truncate_up prec x \<le> 0"
  by (auto simp: truncate_up_def round_up_def intro!: mult_nonpos_nonneg)

lemma truncate_up_le1:
  assumes "x \<le> 1"
  shows "truncate_up p x \<le> 1"
proof -
  consider "x \<le> 0" | "x > 0"
    by arith
  then show ?thesis
  proof cases
    case 1
    with truncate_up_nonpos[OF this, of p] show ?thesis
      by simp
  next
    case 2
    then have le: "\<lfloor>log 2 \<bar>x\<bar>\<rfloor> \<le> 0"
      using assms by (auto simp: log_less_iff)
    from assms have "0 \<le> int p" by simp
    from add_mono[OF this le]
    show ?thesis
      using assms by (simp add: truncate_up_def round_up_le1 add_mono)
  qed
qed

lemma truncate_down_shift_int:
  "truncate_down p (x * 2 powr real_of_int k) = truncate_down p x * 2 powr k"
  by (cases "x = 0")
    (simp_all add: algebra_simps abs_mult log_mult truncate_down_def
      round_down_shift[of _ _ k, simplified])

lemma truncate_down_shift_nat: "truncate_down p (x * 2 powr real k) = truncate_down p x * 2 powr k"
  by (metis of_int_of_nat_eq truncate_down_shift_int)

lemma truncate_up_shift_int: "truncate_up p (x * 2 powr real_of_int k) = truncate_up p x * 2 powr k"
  by (cases "x = 0")
    (simp_all add: algebra_simps abs_mult log_mult truncate_up_def
      round_up_shift[of _ _ k, simplified])

lemma truncate_up_shift_nat: "truncate_up p (x * 2 powr real k) = truncate_up p x * 2 powr k"
  by (metis of_int_of_nat_eq truncate_up_shift_int)


subsection \<open>Truncating Floats\<close>

lift_definition float_round_up :: "nat \<Rightarrow> float \<Rightarrow> float" is truncate_up
  by (simp add: truncate_up_def)

lemma float_round_up: "real_of_float x \<le> real_of_float (float_round_up prec x)"
  using truncate_up by transfer simp

lemma float_round_up_zero[simp]: "float_round_up prec 0 = 0"
  by transfer simp

lift_definition float_round_down :: "nat \<Rightarrow> float \<Rightarrow> float" is truncate_down
  by (simp add: truncate_down_def)

lemma float_round_down: "real_of_float (float_round_down prec x) \<le> real_of_float x"
  using truncate_down by transfer simp

lemma float_round_down_zero[simp]: "float_round_down prec 0 = 0"
  by transfer simp

lemmas float_round_up_le = order_trans[OF _ float_round_up]
  and float_round_down_le = order_trans[OF float_round_down]

lemma minus_float_round_up_eq: "- float_round_up prec x = float_round_down prec (- x)"
  and minus_float_round_down_eq: "- float_round_down prec x = float_round_up prec (- x)"
  by (transfer; simp add: truncate_down_uminus_eq truncate_up_uminus_eq)+

context
begin

qualified lemma compute_float_round_down[code]:
  "float_round_down prec (Float m e) =
    (let d = bitlen \<bar>m\<bar> - int prec - 1 in
      if 0 < d then Float (div_twopow m (nat d)) (e + d)
      else Float m e)"
  using Float.compute_float_down[of "Suc prec - bitlen \<bar>m\<bar> - e" m e, symmetric]
  by transfer
    (simp add: field_simps abs_mult log_mult bitlen_alt_def truncate_down_def
      cong del: if_weak_cong)

qualified lemma compute_float_round_up[code]:
  "float_round_up prec x = - float_round_down prec (-x)"
  by transfer (simp add: truncate_down_uminus_eq)

end

lemma truncate_up_nonneg_mono:
  assumes "0 \<le> x" "x \<le> y"
  shows "truncate_up prec x \<le> truncate_up prec y"
proof -
  consider "\<lfloor>log 2 x\<rfloor> = \<lfloor>log 2 y\<rfloor>" | "\<lfloor>log 2 x\<rfloor> \<noteq> \<lfloor>log 2 y\<rfloor>" "0 < x" | "x \<le> 0"
    by arith
  then show ?thesis
  proof cases
    case 1
    then show ?thesis
      using assms
      by (auto simp: truncate_up_def round_up_def intro!: ceiling_mono)
  next
    case 2
    from assms \<open>0 < x\<close> have "log 2 x \<le> log 2 y"
      by auto
    with \<open>\<lfloor>log 2 x\<rfloor> \<noteq> \<lfloor>log 2 y\<rfloor>\<close>
    have logless: "log 2 x < log 2 y"
      by linarith
    have flogless: "\<lfloor>log 2 x\<rfloor> < \<lfloor>log 2 y\<rfloor>"
      using \<open>\<lfloor>log 2 x\<rfloor> \<noteq> \<lfloor>log 2 y\<rfloor>\<close> \<open>log 2 x \<le> log 2 y\<close> by linarith
    have "truncate_up prec x =
      real_of_int \<lceil>x * 2 powr real_of_int (int prec - \<lfloor>log 2 x\<rfloor> )\<rceil> * 2 powr - real_of_int (int prec - \<lfloor>log 2 x\<rfloor>)"
      using assms by (simp add: truncate_up_def round_up_def)
    also have "\<lceil>x * 2 powr real_of_int (int prec - \<lfloor>log 2 x\<rfloor>)\<rceil> \<le> (2 ^ (Suc prec))"
    proof (simp only: ceiling_le_iff)
      have "x * 2 powr real_of_int (int prec - \<lfloor>log 2 x\<rfloor>) \<le>
        x * (2 powr real (Suc prec) / (2 powr log 2 x))"
        using real_of_int_floor_add_one_ge[of "log 2 x"] assms
        by (auto simp: algebra_simps simp flip: powr_diff intro!: mult_left_mono)
      then show "x * 2 powr real_of_int (int prec - \<lfloor>log 2 x\<rfloor>) \<le> real_of_int ((2::int) ^ (Suc prec))"
        using \<open>0 < x\<close> by (simp add: powr_realpow powr_add)
    qed
    then have "real_of_int \<lceil>x * 2 powr real_of_int (int prec - \<lfloor>log 2 x\<rfloor>)\<rceil> \<le> 2 powr int (Suc prec)"
      by (auto simp: powr_realpow powr_add)
        (metis power_Suc of_int_le_numeral_power_cancel_iff)
    also
    have "2 powr - real_of_int (int prec - \<lfloor>log 2 x\<rfloor>) \<le> 2 powr - real_of_int (int prec - \<lfloor>log 2 y\<rfloor> + 1)"
      using logless flogless by (auto intro!: floor_mono)
    also have "2 powr real_of_int (int (Suc prec)) \<le>
        2 powr (log 2 y + real_of_int (int prec - \<lfloor>log 2 y\<rfloor> + 1))"
      using assms \<open>0 < x\<close>
      by (auto simp: algebra_simps)
    finally have "truncate_up prec x \<le>
        2 powr (log 2 y + real_of_int (int prec - \<lfloor>log 2 y\<rfloor> + 1)) * 2 powr - real_of_int (int prec - \<lfloor>log 2 y\<rfloor> + 1)"
      by simp
    also have "\<dots> = 2 powr (log 2 y + real_of_int (int prec - \<lfloor>log 2 y\<rfloor>) - real_of_int (int prec - \<lfloor>log 2 y\<rfloor>))"
      by (subst powr_add[symmetric]) simp
    also have "\<dots> = y"
      using \<open>0 < x\<close> assms
      by (simp add: powr_add)
    also have "\<dots> \<le> truncate_up prec y"
      by (rule truncate_up)
    finally show ?thesis .
  next
    case 3
    then show ?thesis
      using assms
      by (auto intro!: truncate_up_le)
  qed
qed

lemma truncate_up_switch_sign_mono:
  assumes "x \<le> 0" "0 \<le> y"
  shows "truncate_up prec x \<le> truncate_up prec y"
proof -
  note truncate_up_nonpos[OF \<open>x \<le> 0\<close>]
  also note truncate_up_le[OF \<open>0 \<le> y\<close>]
  finally show ?thesis .
qed

lemma truncate_down_switch_sign_mono:
  assumes "x \<le> 0"
    and "0 \<le> y"
    and "x \<le> y"
  shows "truncate_down prec x \<le> truncate_down prec y"
proof -
  note truncate_down_le[OF \<open>x \<le> 0\<close>]
  also note truncate_down_nonneg[OF \<open>0 \<le> y\<close>]
  finally show ?thesis .
qed

lemma truncate_down_nonneg_mono:
  assumes "0 \<le> x" "x \<le> y"
  shows "truncate_down prec x \<le> truncate_down prec y"
proof -
  consider "x \<le> 0" | "\<lfloor>log 2 \<bar>x\<bar>\<rfloor> = \<lfloor>log 2 \<bar>y\<bar>\<rfloor>" |
    "0 < x" "\<lfloor>log 2 \<bar>x\<bar>\<rfloor> \<noteq> \<lfloor>log 2 \<bar>y\<bar>\<rfloor>"
    by arith
  then show ?thesis
  proof cases
    case 1
    with assms have "x = 0" "0 \<le> y" by simp_all
    then show ?thesis
      by (auto intro!: truncate_down_nonneg)
  next
    case 2
    then show ?thesis
      using assms
      by (auto simp: truncate_down_def round_down_def intro!: floor_mono)
  next
    case 3
    from \<open>0 < x\<close> have "log 2 x \<le> log 2 y" "0 < y" "0 \<le> y"
      using assms by auto
    with \<open>\<lfloor>log 2 \<bar>x\<bar>\<rfloor> \<noteq> \<lfloor>log 2 \<bar>y\<bar>\<rfloor>\<close>
    have logless: "log 2 x < log 2 y" and flogless: "\<lfloor>log 2 x\<rfloor> < \<lfloor>log 2 y\<rfloor>"
      unfolding atomize_conj abs_of_pos[OF \<open>0 < x\<close>] abs_of_pos[OF \<open>0 < y\<close>]
      by (metis floor_less_cancel linorder_cases not_le)
    have "2 powr prec \<le> y * 2 powr real prec / (2 powr log 2 y)"
      using \<open>0 < y\<close> by simp
    also have "\<dots> \<le> y * 2 powr real (Suc prec) / (2 powr (real_of_int \<lfloor>log 2 y\<rfloor> + 1))"
      using \<open>0 \<le> y\<close> \<open>0 \<le> x\<close> assms(2)
      by (auto intro!: powr_mono divide_left_mono
          simp: of_nat_diff powr_add powr_diff)
    also have "\<dots> = y * 2 powr real (Suc prec) / (2 powr real_of_int \<lfloor>log 2 y\<rfloor> * 2)"
      by (auto simp: powr_add)
    finally have "(2 ^ prec) \<le> \<lfloor>y * 2 powr real_of_int (int (Suc prec) - \<lfloor>log 2 \<bar>y\<bar>\<rfloor> - 1)\<rfloor>"
      using \<open>0 \<le> y\<close>
      by (auto simp: powr_diff le_floor_iff powr_realpow powr_add)
    then have "(2 ^ (prec)) * 2 powr - real_of_int (int prec - \<lfloor>log 2 \<bar>y\<bar>\<rfloor>) \<le> truncate_down prec y"
      by (auto simp: truncate_down_def round_down_def)
    moreover have "x \<le> (2 ^ prec) * 2 powr - real_of_int (int prec - \<lfloor>log 2 \<bar>y\<bar>\<rfloor>)"
    proof -
      have "x = 2 powr (log 2 \<bar>x\<bar>)" using \<open>0 < x\<close> by simp
      also have "\<dots> \<le> (2 ^ (Suc prec )) * 2 powr - real_of_int (int prec - \<lfloor>log 2 \<bar>x\<bar>\<rfloor>)"
        using real_of_int_floor_add_one_ge[of "log 2 \<bar>x\<bar>"] \<open>0 < x\<close>
        by (auto simp flip: powr_realpow powr_add simp: algebra_simps powr_mult_base le_powr_iff)
      also
      have "2 powr - real_of_int (int prec - \<lfloor>log 2 \<bar>x\<bar>\<rfloor>) \<le> 2 powr - real_of_int (int prec - \<lfloor>log 2 \<bar>y\<bar>\<rfloor> + 1)"
        using logless flogless \<open>x > 0\<close> \<open>y > 0\<close>
        by (auto intro!: floor_mono)
      finally show ?thesis
        by (auto simp flip: powr_realpow simp: powr_diff assms of_nat_diff)
    qed
    ultimately show ?thesis
      by (metis dual_order.trans truncate_down)
  qed
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

lemma truncate_up_nonneg: "0 \<le> truncate_up p x" if "0 \<le> x"
  by (simp add: that truncate_up_le)

lemma truncate_up_pos: "0 < truncate_up p x" if "0 < x"
  by (meson less_le_trans that truncate_up)

lemma truncate_up_less_zero_iff[simp]: "truncate_up p x < 0 \<longleftrightarrow> x < 0"
proof -
  have f1: "\<forall>n r. truncate_up n r + truncate_down n (- 1 * r) = 0"
    by (simp add: truncate_down_uminus_eq)
  have f2: "(\<forall>v0 v1. truncate_up v0 v1 + truncate_down v0 (- 1 * v1) = 0) = (\<forall>v0 v1. truncate_up v0 v1 = - 1 * truncate_down v0 (- 1 * v1))"
    by (auto simp: truncate_up_eq_truncate_down)
  have f3: "\<forall>x1. ((0::real) < x1) = (\<not> x1 \<le> 0)"
    by fastforce
  have "(- 1 * x \<le> 0) = (0 \<le> x)"
    by force
  then have "0 \<le> x \<or> \<not> truncate_down p (- 1 * x) \<le> 0"
    using f3 by (meson truncate_down_pos)
  then have "(0 \<le> truncate_up p x) \<noteq> (\<not> 0 \<le> x)"
    using f2 f1 truncate_up_nonneg by force
  then show ?thesis
    by linarith
qed

lemma truncate_up_nonneg_iff[simp]: "truncate_up p x \<ge> 0 \<longleftrightarrow> x \<ge> 0"
  using truncate_up_less_zero_iff[of p x] truncate_up_nonneg[of x]
  by linarith

lemma truncate_down_less_zero_iff[simp]: "truncate_down p x < 0 \<longleftrightarrow> x < 0"
  by (metis le_less_trans not_less_iff_gr_or_eq truncate_down truncate_down_pos truncate_down_zero)

lemma truncate_down_nonneg_iff[simp]: "truncate_down p x \<ge> 0 \<longleftrightarrow> x \<ge> 0"
  using truncate_down_less_zero_iff[of p x] truncate_down_nonneg[of x p]
  by linarith

lemma truncate_down_eq_zero_iff[simp]: "truncate_down prec x = 0 \<longleftrightarrow> x = 0"
  by (metis not_less_iff_gr_or_eq truncate_down_less_zero_iff truncate_down_pos truncate_down_zero)

lemma truncate_up_eq_zero_iff[simp]: "truncate_up prec x = 0 \<longleftrightarrow> x = 0"
  by (metis not_less_iff_gr_or_eq truncate_up_less_zero_iff truncate_up_pos truncate_up_zero)


subsection \<open>Approximation of positive rationals\<close>

lemma div_mult_twopow_eq: "a div ((2::nat) ^ n) div b = a div (b * 2 ^ n)" for a b :: nat
  by (cases "b = 0") (simp_all add: div_mult2_eq[symmetric] ac_simps)

lemma real_div_nat_eq_floor_of_divide: "a div b = real_of_int \<lfloor>a / b\<rfloor>" for a b :: nat
  by (simp add: floor_divide_of_nat_eq [of a b])

definition "rat_precision prec x y =
  (let d = bitlen x - bitlen y
   in int prec - d + (if Float (abs x) 0 < Float (abs y) d then 1 else 0))"

lemma floor_log_divide_eq:
  assumes "i > 0" "j > 0" "p > 1"
  shows "\<lfloor>log p (i / j)\<rfloor> = floor (log p i) - floor (log p j) -
    (if i \<ge> j * p powr (floor (log p i) - floor (log p j)) then 0 else 1)"
proof -
  let ?l = "log p"
  let ?fl = "\<lambda>x. floor (?l x)"
  have "\<lfloor>?l (i / j)\<rfloor> = \<lfloor>?l i - ?l j\<rfloor>" using assms
    by (auto simp: log_divide)
  also have "\<dots> = floor (real_of_int (?fl i - ?fl j) + (?l i - ?fl i - (?l j - ?fl j)))"
    (is "_ = floor (_ + ?r)")
    by (simp add: algebra_simps)
  also note floor_add2
  also note \<open>p > 1\<close>
  note powr = powr_le_cancel_iff[symmetric, OF \<open>1 < p\<close>, THEN iffD2]
  note powr_strict = powr_less_cancel_iff[symmetric, OF \<open>1 < p\<close>, THEN iffD2]
  have "floor ?r = (if i \<ge> j * p powr (?fl i - ?fl j) then 0 else -1)" (is "_ = ?if")
    using assms
    by (linarith |
      auto
        intro!: floor_eq2
        intro: powr_strict powr
        simp: powr_diff powr_add field_split_simps algebra_simps)+
  finally
  show ?thesis by simp
qed

lemma truncate_down_rat_precision:
    "truncate_down prec (real x / real y) = round_down (rat_precision prec x y) (real x / real y)"
  and truncate_up_rat_precision:
    "truncate_up prec (real x / real y) = round_up (rat_precision prec x y) (real x / real y)"
  unfolding truncate_down_def truncate_up_def rat_precision_def
  by (cases x; cases y) (auto simp: floor_log_divide_eq algebra_simps bitlen_alt_def)

lift_definition lapprox_posrat :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> float"
  is "\<lambda>prec (x::nat) (y::nat). truncate_down prec (x / y)"
  by simp

context
begin

qualified lemma compute_lapprox_posrat[code]:
  "lapprox_posrat prec x y =
   (let
      l = rat_precision prec x y;
      d = if 0 \<le> l then x * 2^nat l div y else x div 2^nat (- l) div y
    in normfloat (Float d (- l)))"
    unfolding div_mult_twopow_eq
    by transfer
      (simp add: round_down_def powr_int real_div_nat_eq_floor_of_divide field_simps Let_def
        truncate_down_rat_precision del: two_powr_minus_int_float)

end

lift_definition rapprox_posrat :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> float"
  is "\<lambda>prec (x::nat) (y::nat). truncate_up prec (x / y)"
  by simp

context
begin

qualified lemma compute_rapprox_posrat[code]:
  fixes prec x y
  defines "l \<equiv> rat_precision prec x y"
  shows "rapprox_posrat prec x y =
   (let
      l = l;
      (r, s) = if 0 \<le> l then (x * 2^nat l, y) else (x, y * 2^nat(-l));
      d = r div s;
      m = r mod s
    in normfloat (Float (d + (if m = 0 \<or> y = 0 then 0 else 1)) (- l)))"
proof (cases "y = 0")
  assume "y = 0"
  then show ?thesis by transfer simp
next
  assume "y \<noteq> 0"
  show ?thesis
  proof (cases "0 \<le> l")
    case True
    define x' where "x' = x * 2 ^ nat l"
    have "int x * 2 ^ nat l = x'"
      by (simp add: x'_def)
    moreover have "real x * 2 powr l = real x'"
      by (simp flip: powr_realpow add: \<open>0 \<le> l\<close> x'_def)
    ultimately show ?thesis
      using ceil_divide_floor_conv[of y x'] powr_realpow[of 2 "nat l"] \<open>0 \<le> l\<close> \<open>y \<noteq> 0\<close>
        l_def[symmetric, THEN meta_eq_to_obj_eq]
      apply transfer
      apply (auto simp add: round_up_def truncate_up_rat_precision)
      apply (metis dvd_triv_left of_nat_dvd_iff)
      apply (metis floor_divide_of_int_eq of_int_of_nat_eq)
      done
   next
    case False
    define y' where "y' = y * 2 ^ nat (- l)"
    from \<open>y \<noteq> 0\<close> have "y' \<noteq> 0" by (simp add: y'_def)
    have "int y * 2 ^ nat (- l) = y'"
      by (simp add: y'_def)
    moreover have "real x * real_of_int (2::int) powr real_of_int l / real y = x / real y'"
      using \<open>\<not> 0 \<le> l\<close> by (simp flip: powr_realpow add: powr_minus y'_def field_simps)
    ultimately show ?thesis
      using ceil_divide_floor_conv[of y' x] \<open>\<not> 0 \<le> l\<close> \<open>y' \<noteq> 0\<close> \<open>y \<noteq> 0\<close>
        l_def[symmetric, THEN meta_eq_to_obj_eq]
      apply transfer
      apply (auto simp add: round_up_def ceil_divide_floor_conv truncate_up_rat_precision)
      apply (metis dvd_triv_left of_nat_dvd_iff)
      apply (metis floor_divide_of_int_eq of_int_of_nat_eq)
      done
  qed
qed

end

lemma rat_precision_pos:
  assumes "0 \<le> x"
    and "0 < y"
    and "2 * x < y"
  shows "rat_precision n (int x) (int y) > 0"
proof -
  have "0 < x \<Longrightarrow> log 2 x + 1 = log 2 (2 * x)"
    by (simp add: log_mult)
  then have "bitlen (int x) < bitlen (int y)"
    using assms
    by (simp add: bitlen_alt_def)
      (auto intro!: floor_mono simp add: one_add_floor)
  then show ?thesis
    using assms
    by (auto intro!: pos_add_strict simp add: field_simps rat_precision_def)
qed

lemma rapprox_posrat_less1:
  "0 \<le> x \<Longrightarrow> 0 < y \<Longrightarrow> 2 * x < y \<Longrightarrow> real_of_float (rapprox_posrat n x y) < 1"
  by transfer (simp add: rat_precision_pos round_up_less1 truncate_up_rat_precision)

lift_definition lapprox_rat :: "nat \<Rightarrow> int \<Rightarrow> int \<Rightarrow> float" is
  "\<lambda>prec (x::int) (y::int). truncate_down prec (x / y)"
  by simp

context
begin

qualified lemma compute_lapprox_rat[code]:
  "lapprox_rat prec x y =
   (if y = 0 then 0
    else if 0 \<le> x then
     (if 0 < y then lapprox_posrat prec (nat x) (nat y)
      else - (rapprox_posrat prec (nat x) (nat (-y))))
      else
       (if 0 < y
        then - (rapprox_posrat prec (nat (-x)) (nat y))
        else lapprox_posrat prec (nat (-x)) (nat (-y))))"
  by transfer (simp add: truncate_up_uminus_eq)

lift_definition rapprox_rat :: "nat \<Rightarrow> int \<Rightarrow> int \<Rightarrow> float" is
  "\<lambda>prec (x::int) (y::int). truncate_up prec (x / y)"
  by simp

lemma "rapprox_rat = rapprox_posrat"
  by transfer auto

lemma "lapprox_rat = lapprox_posrat"
  by transfer auto

qualified lemma compute_rapprox_rat[code]:
  "rapprox_rat prec x y = - lapprox_rat prec (-x) y"
  by transfer (simp add: truncate_down_uminus_eq)

qualified lemma compute_truncate_down[code]:
  "truncate_down p (Ratreal r) = (let (a, b) = quotient_of r in lapprox_rat p a b)"
  by transfer (auto split: prod.split simp: of_rat_divide dest!: quotient_of_div)

qualified lemma compute_truncate_up[code]:
  "truncate_up p (Ratreal r) = (let (a, b) = quotient_of r in rapprox_rat p a b)"
  by transfer (auto split: prod.split simp:  of_rat_divide dest!: quotient_of_div)

end


subsection \<open>Division\<close>

definition "real_divl prec a b = truncate_down prec (a / b)"

definition "real_divr prec a b = truncate_up prec (a / b)"

lift_definition float_divl :: "nat \<Rightarrow> float \<Rightarrow> float \<Rightarrow> float" is real_divl
  by (simp add: real_divl_def)

context
begin

qualified lemma compute_float_divl[code]:
  "float_divl prec (Float m1 s1) (Float m2 s2) = lapprox_rat prec m1 m2 * Float 1 (s1 - s2)"
  apply transfer
  unfolding real_divl_def of_int_1 mult_1 truncate_down_shift_int[symmetric]
  apply (simp add: powr_diff powr_minus)
  done

lift_definition float_divr :: "nat \<Rightarrow> float \<Rightarrow> float \<Rightarrow> float" is real_divr
  by (simp add: real_divr_def)

qualified lemma compute_float_divr[code]:
  "float_divr prec x y = - float_divl prec (-x) y"
  by transfer (simp add: real_divr_def real_divl_def truncate_down_uminus_eq)

end


subsection \<open>Approximate Addition\<close>

definition "plus_down prec x y = truncate_down prec (x + y)"

definition "plus_up prec x y = truncate_up prec (x + y)"

lemma float_plus_down_float[intro, simp]: "x \<in> float \<Longrightarrow> y \<in> float \<Longrightarrow> plus_down p x y \<in> float"
  by (simp add: plus_down_def)

lemma float_plus_up_float[intro, simp]: "x \<in> float \<Longrightarrow> y \<in> float \<Longrightarrow> plus_up p x y \<in> float"
  by (simp add: plus_up_def)

lift_definition float_plus_down :: "nat \<Rightarrow> float \<Rightarrow> float \<Rightarrow> float" is plus_down ..

lift_definition float_plus_up :: "nat \<Rightarrow> float \<Rightarrow> float \<Rightarrow> float" is plus_up ..

lemma plus_down: "plus_down prec x y \<le> x + y"
  and plus_up: "x + y \<le> plus_up prec x y"
  by (auto simp: plus_down_def truncate_down plus_up_def truncate_up)

lemma float_plus_down: "real_of_float (float_plus_down prec x y) \<le> x + y"
  and float_plus_up: "x + y \<le> real_of_float (float_plus_up prec x y)"
  by (transfer; rule plus_down plus_up)+

lemmas plus_down_le = order_trans[OF plus_down]
  and plus_up_le = order_trans[OF _ plus_up]
  and float_plus_down_le = order_trans[OF float_plus_down]
  and float_plus_up_le = order_trans[OF _ float_plus_up]

lemma compute_plus_up[code]: "plus_up p x y = - plus_down p (-x) (-y)"
  using truncate_down_uminus_eq[of p "x + y"]
  by (auto simp: plus_down_def plus_up_def)

lemma truncate_down_log2_eqI:
  assumes "\<lfloor>log 2 \<bar>x\<bar>\<rfloor> = \<lfloor>log 2 \<bar>y\<bar>\<rfloor>"
  assumes "\<lfloor>x * 2 powr (p - \<lfloor>log 2 \<bar>x\<bar>\<rfloor>)\<rfloor> = \<lfloor>y * 2 powr (p - \<lfloor>log 2 \<bar>x\<bar>\<rfloor>)\<rfloor>"
  shows "truncate_down p x = truncate_down p y"
  using assms by (auto simp: truncate_down_def round_down_def)

lemma sum_neq_zeroI:
  "\<bar>a\<bar> \<ge> k \<Longrightarrow> \<bar>b\<bar> < k \<Longrightarrow> a + b \<noteq> 0"
  "\<bar>a\<bar> > k \<Longrightarrow> \<bar>b\<bar> \<le> k \<Longrightarrow> a + b \<noteq> 0"
  for a k :: real
  by auto

lemma abs_real_le_2_powr_bitlen[simp]: "\<bar>real_of_int m2\<bar> < 2 powr real_of_int (bitlen \<bar>m2\<bar>)"
proof (cases "m2 = 0")
  case True
  then show ?thesis by simp
next
  case False
  then have "\<bar>m2\<bar> < 2 ^ nat (bitlen \<bar>m2\<bar>)"
    using bitlen_bounds[of "\<bar>m2\<bar>"]
    by (auto simp: powr_add bitlen_nonneg)
  then show ?thesis
    by (metis bitlen_nonneg powr_int of_int_abs of_int_less_numeral_power_cancel_iff
        zero_less_numeral)
qed

lemma floor_sum_times_2_powr_sgn_eq:
  fixes ai p q :: int
    and a b :: real
  assumes "a * 2 powr p = ai"
    and b_le_1: "\<bar>b * 2 powr (p + 1)\<bar> \<le> 1"
    and leqp: "q \<le> p"
  shows "\<lfloor>(a + b) * 2 powr q\<rfloor> = \<lfloor>(2 * ai + sgn b) * 2 powr (q - p - 1)\<rfloor>"
proof -
  consider "b = 0" | "b > 0" | "b < 0" by arith
  then show ?thesis
  proof cases
    case 1
    then show ?thesis
      by (simp flip: assms(1) powr_add add: algebra_simps powr_mult_base)
  next
    case 2
    then have "b * 2 powr p < \<bar>b * 2 powr (p + 1)\<bar>"
      by simp
    also note b_le_1
    finally have b_less_1: "b * 2 powr real_of_int p < 1" .

    from b_less_1 \<open>b > 0\<close> have floor_eq: "\<lfloor>b * 2 powr real_of_int p\<rfloor> = 0" "\<lfloor>sgn b / 2\<rfloor> = 0"
      by (simp_all add: floor_eq_iff)

    have "\<lfloor>(a + b) * 2 powr q\<rfloor> = \<lfloor>(a + b) * 2 powr p * 2 powr (q - p)\<rfloor>"
      by (simp add: algebra_simps flip: powr_realpow powr_add)
    also have "\<dots> = \<lfloor>(ai + b * 2 powr p) * 2 powr (q - p)\<rfloor>"
      by (simp add: assms algebra_simps)
    also have "\<dots> = \<lfloor>(ai + b * 2 powr p) / real_of_int ((2::int) ^ nat (p - q))\<rfloor>"
      using assms
      by (simp add: algebra_simps divide_powr_uminus flip: powr_realpow powr_add)
    also have "\<dots> = \<lfloor>ai / real_of_int ((2::int) ^ nat (p - q))\<rfloor>"
      by (simp del: of_int_power add: floor_divide_real_eq_div floor_eq)
    finally have "\<lfloor>(a + b) * 2 powr real_of_int q\<rfloor> = \<lfloor>real_of_int ai / real_of_int ((2::int) ^ nat (p - q))\<rfloor>" .
    moreover
    have "\<lfloor>(2 * ai + (sgn b)) * 2 powr (real_of_int (q - p) - 1)\<rfloor> =
        \<lfloor>real_of_int ai / real_of_int ((2::int) ^ nat (p - q))\<rfloor>"
    proof -
      have "\<lfloor>(2 * ai + sgn b) * 2 powr (real_of_int (q - p) - 1)\<rfloor> = \<lfloor>(ai + sgn b / 2) * 2 powr (q - p)\<rfloor>"
        by (subst powr_diff) (simp add: field_simps)
      also have "\<dots> = \<lfloor>(ai + sgn b / 2) / real_of_int ((2::int) ^ nat (p - q))\<rfloor>"
        using leqp by (simp flip: powr_realpow add: powr_diff)
      also have "\<dots> = \<lfloor>ai / real_of_int ((2::int) ^ nat (p - q))\<rfloor>"
        by (simp del: of_int_power add: floor_divide_real_eq_div floor_eq)
      finally show ?thesis .
    qed
    ultimately show ?thesis by simp
  next
    case 3
    then have floor_eq: "\<lfloor>b * 2 powr (real_of_int p + 1)\<rfloor> = -1"
      using b_le_1
      by (auto simp: floor_eq_iff algebra_simps pos_divide_le_eq[symmetric] abs_if divide_powr_uminus
        intro!: mult_neg_pos split: if_split_asm)
    have "\<lfloor>(a + b) * 2 powr q\<rfloor> = \<lfloor>(2*a + 2*b) * 2 powr p * 2 powr (q - p - 1)\<rfloor>"
      by (simp add: algebra_simps powr_mult_base flip: powr_realpow powr_add)
    also have "\<dots> = \<lfloor>(2 * (a * 2 powr p) + 2 * b * 2 powr p) * 2 powr (q - p - 1)\<rfloor>"
      by (simp add: algebra_simps)
    also have "\<dots> = \<lfloor>(2 * ai + b * 2 powr (p + 1)) / 2 powr (1 - q + p)\<rfloor>"
      using assms by (simp add: algebra_simps powr_mult_base divide_powr_uminus)
    also have "\<dots> = \<lfloor>(2 * ai + b * 2 powr (p + 1)) / real_of_int ((2::int) ^ nat (p - q + 1))\<rfloor>"
      using assms by (simp add: algebra_simps flip: powr_realpow)
    also have "\<dots> = \<lfloor>(2 * ai - 1) / real_of_int ((2::int) ^ nat (p - q + 1))\<rfloor>"
      using \<open>b < 0\<close> assms
      by (simp add: floor_divide_of_int_eq floor_eq floor_divide_real_eq_div
        del: of_int_mult of_int_power of_int_diff)
    also have "\<dots> = \<lfloor>(2 * ai - 1) * 2 powr (q - p - 1)\<rfloor>"
      using assms by (simp add: algebra_simps divide_powr_uminus flip: powr_realpow)
    finally show ?thesis
      using \<open>b < 0\<close> by simp
  qed
qed

lemma log2_abs_int_add_less_half_sgn_eq:
  fixes ai :: int
    and b :: real
  assumes "\<bar>b\<bar> \<le> 1/2"
    and "ai \<noteq> 0"
  shows "\<lfloor>log 2 \<bar>real_of_int ai + b\<bar>\<rfloor> = \<lfloor>log 2 \<bar>ai + sgn b / 2\<bar>\<rfloor>"
proof (cases "b = 0")
  case True
  then show ?thesis by simp
next
  case False
  define k where "k = \<lfloor>log 2 \<bar>ai\<bar>\<rfloor>"
  then have "\<lfloor>log 2 \<bar>ai\<bar>\<rfloor> = k"
    by simp
  then have k: "2 powr k \<le> \<bar>ai\<bar>" "\<bar>ai\<bar> < 2 powr (k + 1)"
    by (simp_all add: floor_log_eq_powr_iff \<open>ai \<noteq> 0\<close>)
  have "k \<ge> 0"
    using assms by (auto simp: k_def)
  define r where "r = \<bar>ai\<bar> - 2 ^ nat k"
  have r: "0 \<le> r" "r < 2 powr k"
    using \<open>k \<ge> 0\<close> k
    by (auto simp: r_def k_def algebra_simps powr_add abs_if powr_int)
  then have "r \<le> (2::int) ^ nat k - 1"
    using \<open>k \<ge> 0\<close> by (auto simp: powr_int)
  from this[simplified of_int_le_iff[symmetric]] \<open>0 \<le> k\<close>
  have r_le: "r \<le> 2 powr k - 1"
    by (auto simp: algebra_simps powr_int)
      (metis of_int_1 of_int_add of_int_le_numeral_power_cancel_iff)

  have "\<bar>ai\<bar> = 2 powr k + r"
    using \<open>k \<ge> 0\<close> by (auto simp: k_def r_def simp flip: powr_realpow)

  have pos: "\<bar>b\<bar> < 1 \<Longrightarrow> 0 < 2 powr k + (r + b)" for b :: real
    using \<open>0 \<le> k\<close> \<open>ai \<noteq> 0\<close>
    by (auto simp add: r_def powr_realpow[symmetric] abs_if sgn_if algebra_simps
      split: if_split_asm)
  have less: "\<bar>sgn ai * b\<bar> < 1"
    and less': "\<bar>sgn (sgn ai * b) / 2\<bar> < 1"
    using \<open>\<bar>b\<bar> \<le> _\<close> by (auto simp: abs_if sgn_if split: if_split_asm)

  have floor_eq: "\<And>b::real. \<bar>b\<bar> \<le> 1 / 2 \<Longrightarrow>
      \<lfloor>log 2 (1 + (r + b) / 2 powr k)\<rfloor> = (if r = 0 \<and> b < 0 then -1 else 0)"
    using \<open>k \<ge> 0\<close> r r_le
    by (auto simp: floor_log_eq_powr_iff powr_minus_divide field_simps sgn_if)

  from \<open>real_of_int \<bar>ai\<bar> = _\<close> have "\<bar>ai + b\<bar> = 2 powr k + (r + sgn ai * b)"
    using \<open>\<bar>b\<bar> \<le> _\<close> \<open>0 \<le> k\<close> r
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
      using \<open>\<bar>b\<bar> \<le> _\<close>
      by (intro floor_eq) (auto simp: abs_mult sgn_if)
    also
    have "\<dots> = \<lfloor>log 2 (1 + (r + sgn (sgn ai * b) / 2) / 2 powr k)\<rfloor>"
      by (subst floor_eq) (auto simp: sgn_if)
    also have "k + \<dots> = \<lfloor>log 2 (2 powr k * (1 + (r + sgn (sgn ai * b) / 2) / 2 powr k))\<rfloor>"
      unfolding int_add_floor
      using pos[OF less'] \<open>\<bar>b\<bar> \<le> _\<close>
      by (simp add: field_simps add_log_eq_powr del: floor_add2)
    also have "2 powr k * (1 + (r + sgn (sgn ai * b) / 2) / 2 powr k) =
        2 powr k + r + sgn (sgn ai * b) / 2"
      by (simp add: sgn_if field_simps)
    finally show ?thesis .
  qed
  also have "2 powr k + r + sgn (sgn ai * b) / 2 = \<bar>ai + sgn b / 2\<bar>"
    unfolding \<open>real_of_int \<bar>ai\<bar> = _\<close>[symmetric] using \<open>ai \<noteq> 0\<close>
    by (auto simp: abs_if sgn_if algebra_simps)
  finally show ?thesis .
qed

context
begin

qualified lemma compute_far_float_plus_down:
  fixes m1 e1 m2 e2 :: int
    and p :: nat
  defines "k1 \<equiv> Suc p - nat (bitlen \<bar>m1\<bar>)"
  assumes H: "bitlen \<bar>m2\<bar> \<le> e1 - e2 - k1 - 2" "m1 \<noteq> 0" "m2 \<noteq> 0" "e1 \<ge> e2"
  shows "float_plus_down p (Float m1 e1) (Float m2 e2) =
    float_round_down p (Float (m1 * 2 ^ (Suc (Suc k1)) + sgn m2) (e1 - int k1 - 2))"
proof -
  let ?a = "real_of_float (Float m1 e1)"
  let ?b = "real_of_float (Float m2 e2)"
  let ?sum = "?a + ?b"
  let ?shift = "real_of_int e2 - real_of_int e1 + real k1 + 1"
  let ?m1 = "m1 * 2 ^ Suc k1"
  let ?m2 = "m2 * 2 powr ?shift"
  let ?m2' = "sgn m2 / 2"
  let ?e = "e1 - int k1 - 1"

  have sum_eq: "?sum = (?m1 + ?m2) * 2 powr ?e"
    by (auto simp flip: powr_add powr_mult powr_realpow simp: powr_mult_base algebra_simps)

  have "\<bar>?m2\<bar> * 2 < 2 powr (bitlen \<bar>m2\<bar> + ?shift + 1)"
    by (auto simp: field_simps powr_add powr_mult_base powr_diff abs_mult)
  also have "\<dots> \<le> 2 powr 0"
    using H by (intro powr_mono) auto
  finally have abs_m2_less_half: "\<bar>?m2\<bar> < 1 / 2"
    by simp

  then have "\<bar>real_of_int m2\<bar> < 2 powr -(?shift + 1)"
    unfolding powr_minus_divide by (auto simp: bitlen_alt_def field_simps powr_mult_base abs_mult)
  also have "\<dots> \<le> 2 powr real_of_int (e1 - e2 - 2)"
    by simp
  finally have b_less_quarter: "\<bar>?b\<bar> < 1/4 * 2 powr real_of_int e1"
    by (simp add: powr_add field_simps powr_diff abs_mult)
  also have "1/4 < \<bar>real_of_int m1\<bar> / 2" using \<open>m1 \<noteq> 0\<close> by simp
  finally have b_less_half_a: "\<bar>?b\<bar> < 1/2 * \<bar>?a\<bar>"
    by (simp add: algebra_simps powr_mult_base abs_mult)
  then have a_half_less_sum: "\<bar>?a\<bar> / 2 < \<bar>?sum\<bar>"
    by (auto simp: field_simps abs_if split: if_split_asm)

  from b_less_half_a have "\<bar>?b\<bar> < \<bar>?a\<bar>" "\<bar>?b\<bar> \<le> \<bar>?a\<bar>"
    by simp_all

  have "\<bar>real_of_float (Float m1 e1)\<bar> \<ge> 1/4 * 2 powr real_of_int e1"
    using \<open>m1 \<noteq> 0\<close>
    by (auto simp: powr_add powr_int bitlen_nonneg divide_right_mono abs_mult)
  then have "?sum \<noteq> 0" using b_less_quarter
    by (rule sum_neq_zeroI)
  then have "?m1 + ?m2 \<noteq> 0"
    unfolding sum_eq by (simp add: abs_mult zero_less_mult_iff)

  have "\<bar>real_of_int ?m1\<bar> \<ge> 2 ^ Suc k1" "\<bar>?m2'\<bar> < 2 ^ Suc k1"
    using \<open>m1 \<noteq> 0\<close> \<open>m2 \<noteq> 0\<close> by (auto simp: sgn_if less_1_mult abs_mult simp del: power.simps)
  then have sum'_nz: "?m1 + ?m2' \<noteq> 0"
    by (intro sum_neq_zeroI)

  have "\<lfloor>log 2 \<bar>real_of_float (Float m1 e1) + real_of_float (Float m2 e2)\<bar>\<rfloor> = \<lfloor>log 2 \<bar>?m1 + ?m2\<bar>\<rfloor> + ?e"
    using \<open>?m1 + ?m2 \<noteq> 0\<close>
    unfolding floor_add[symmetric] sum_eq
    by (simp add: abs_mult log_mult) linarith
  also have "\<lfloor>log 2 \<bar>?m1 + ?m2\<bar>\<rfloor> = \<lfloor>log 2 \<bar>?m1 + sgn (real_of_int m2 * 2 powr ?shift) / 2\<bar>\<rfloor>"
    using abs_m2_less_half \<open>m1 \<noteq> 0\<close>
    by (intro log2_abs_int_add_less_half_sgn_eq) (auto simp: abs_mult)
  also have "sgn (real_of_int m2 * 2 powr ?shift) = sgn m2"
    by (auto simp: sgn_if zero_less_mult_iff less_not_sym)
  also
  have "\<bar>?m1 + ?m2'\<bar> * 2 powr ?e = \<bar>?m1 * 2 + sgn m2\<bar> * 2 powr (?e - 1)"
    by (auto simp: field_simps powr_minus[symmetric] powr_diff powr_mult_base)
  then have "\<lfloor>log 2 \<bar>?m1 + ?m2'\<bar>\<rfloor> + ?e = \<lfloor>log 2 \<bar>real_of_float (Float (?m1 * 2 + sgn m2) (?e - 1))\<bar>\<rfloor>"
    using \<open>?m1 + ?m2' \<noteq> 0\<close>
    unfolding floor_add_int
    by (simp add: log_add_eq_powr abs_mult_pos del: floor_add2)
  finally
  have "\<lfloor>log 2 \<bar>?sum\<bar>\<rfloor> = \<lfloor>log 2 \<bar>real_of_float (Float (?m1*2 + sgn m2) (?e - 1))\<bar>\<rfloor>" .
  then have "plus_down p (Float m1 e1) (Float m2 e2) =
      truncate_down p (Float (?m1*2 + sgn m2) (?e - 1))"
    unfolding plus_down_def
  proof (rule truncate_down_log2_eqI)
    let ?f = "(int p - \<lfloor>log 2 \<bar>real_of_float (Float m1 e1) + real_of_float (Float m2 e2)\<bar>\<rfloor>)"
    let ?ai = "m1 * 2 ^ (Suc k1)"
    have "\<lfloor>(?a + ?b) * 2 powr real_of_int ?f\<rfloor> = \<lfloor>(real_of_int (2 * ?ai) + sgn ?b) * 2 powr real_of_int (?f - - ?e - 1)\<rfloor>"
    proof (rule floor_sum_times_2_powr_sgn_eq)
      show "?a * 2 powr real_of_int (-?e) = real_of_int ?ai"
        by (simp add: powr_add powr_realpow[symmetric] powr_diff)
      show "\<bar>?b * 2 powr real_of_int (-?e + 1)\<bar> \<le> 1"
        using abs_m2_less_half
        by (simp add: abs_mult powr_add[symmetric] algebra_simps powr_mult_base)
    next
      have "e1 + \<lfloor>log 2 \<bar>real_of_int m1\<bar>\<rfloor> - 1 = \<lfloor>log 2 \<bar>?a\<bar>\<rfloor> - 1"
        using \<open>m1 \<noteq> 0\<close>
        by (simp add: int_add_floor algebra_simps log_mult abs_mult del: floor_add2)
      also have "\<dots> \<le> \<lfloor>log 2 \<bar>?a + ?b\<bar>\<rfloor>"
        using a_half_less_sum \<open>m1 \<noteq> 0\<close> \<open>?sum \<noteq> 0\<close>
        unfolding floor_diff_of_int[symmetric]
        by (auto simp add: log_minus_eq_powr powr_minus_divide intro!: floor_mono)
      finally
      have "int p - \<lfloor>log 2 \<bar>?a + ?b\<bar>\<rfloor> \<le> p - (bitlen \<bar>m1\<bar>) - e1 + 2"
        by (auto simp: algebra_simps bitlen_alt_def \<open>m1 \<noteq> 0\<close>)
      also have "\<dots> \<le> - ?e"
        using bitlen_nonneg[of "\<bar>m1\<bar>"] by (simp add: k1_def)
      finally show "?f \<le> - ?e" by simp
    qed
    also have "sgn ?b = sgn m2"
      using powr_gt_zero[of 2 e2]
      by (auto simp add: sgn_if zero_less_mult_iff simp del: powr_gt_zero)
    also have "\<lfloor>(real_of_int (2 * ?m1) + real_of_int (sgn m2)) * 2 powr real_of_int (?f - - ?e - 1)\<rfloor> =
        \<lfloor>Float (?m1 * 2 + sgn m2) (?e - 1) * 2 powr ?f\<rfloor>"
      by (simp flip: powr_add powr_realpow add: algebra_simps)
    finally
    show "\<lfloor>(?a + ?b) * 2 powr ?f\<rfloor> = \<lfloor>real_of_float (Float (?m1 * 2 + sgn m2) (?e - 1)) * 2 powr ?f\<rfloor>" .
  qed
  then show ?thesis
    by transfer (simp add: plus_down_def ac_simps Let_def)
qed

lemma compute_float_plus_down_naive[code]: "float_plus_down p x y = float_round_down p (x + y)"
  by transfer (auto simp: plus_down_def)

qualified lemma compute_float_plus_down[code]:
  fixes p::nat and m1 e1 m2 e2::int
  shows "float_plus_down p (Float m1 e1) (Float m2 e2) =
    (if m1 = 0 then float_round_down p (Float m2 e2)
    else if m2 = 0 then float_round_down p (Float m1 e1)
    else
      (if e1 \<ge> e2 then
        (let k1 = Suc p - nat (bitlen \<bar>m1\<bar>) in
          if bitlen \<bar>m2\<bar> > e1 - e2 - k1 - 2
          then float_round_down p ((Float m1 e1) + (Float m2 e2))
          else float_round_down p (Float (m1 * 2 ^ (Suc (Suc k1)) + sgn m2) (e1 - int k1 - 2)))
    else float_plus_down p (Float m2 e2) (Float m1 e1)))"
proof -
  {
    assume "bitlen \<bar>m2\<bar> \<le> e1 - e2 - (Suc p - nat (bitlen \<bar>m1\<bar>)) - 2" "m1 \<noteq> 0" "m2 \<noteq> 0" "e1 \<ge> e2"
    note compute_far_float_plus_down[OF this]
  }
  then show ?thesis
    by transfer (simp add: Let_def plus_down_def ac_simps)
qed

qualified lemma compute_float_plus_up[code]: "float_plus_up p x y = - float_plus_down p (-x) (-y)"
  using truncate_down_uminus_eq[of p "x + y"]
  by transfer (simp add: plus_down_def plus_up_def ac_simps)

lemma mantissa_zero: "mantissa 0 = 0"
  by (fact mantissa_0)

qualified lemma compute_float_less[code]: "a < b \<longleftrightarrow> is_float_pos (float_plus_down 0 b (- a))"
  using truncate_down[of 0 "b - a"] truncate_down_pos[of "b - a" 0]
  by transfer (auto simp: plus_down_def)

qualified lemma compute_float_le[code]: "a \<le> b \<longleftrightarrow> is_float_nonneg (float_plus_down 0 b (- a))"
  using truncate_down[of 0 "b - a"] truncate_down_nonneg[of "b - a" 0]
  by transfer (auto simp: plus_down_def)

end

lemma plus_down_mono: "plus_down p a b \<le> plus_down p c d" if "a + b \<le> c + d"
  by (auto simp: plus_down_def intro!: truncate_down_mono that)

lemma plus_up_mono: "plus_up p a b \<le> plus_up p c d" if "a + b \<le> c + d"
  by (auto simp: plus_up_def intro!: truncate_up_mono that)

subsection \<open>Approximate Multiplication\<close>

lemma mult_mono_nonpos_nonneg: "a * b \<le> c * d"
  if  "a \<le> c" "a \<le> 0" "0 \<le> d" "d \<le> b" for a b c d::"'a::ordered_ring"
  by (meson dual_order.trans mult_left_mono_neg mult_right_mono that)

lemma mult_mono_nonneg_nonpos: "b * a \<le> d * c"
  if  "a \<le> c" "c \<le> 0" "0 \<le> d" "d \<le> b" for a b c d::"'a::ordered_ring"
  by (meson dual_order.trans mult_right_mono_neg mult_left_mono that)

lemma mult_mono_nonpos_nonpos: "a * b \<le> c * d"
  if  "a \<ge> c" "a \<le> 0" "b \<ge> d" "d \<le> 0" for a b c d::real
  by (meson dual_order.trans mult_left_mono_neg mult_right_mono_neg that)

lemma mult_float_mono1:
  notes mono_rules = plus_down_mono add_mono nprt_mono nprt_le_zero zero_le_pprt pprt_mono
  shows "a \<le> b \<Longrightarrow> ab \<le> bb \<Longrightarrow>
       aa \<le> a \<Longrightarrow>
       b \<le> ba \<Longrightarrow>
       ac \<le> ab \<Longrightarrow>
       bb \<le> bc \<Longrightarrow>
       plus_down prec (nprt aa * pprt bc)
        (plus_down prec (nprt ba * nprt bc)
          (plus_down prec (pprt aa * pprt ac)
            (pprt ba * nprt ac)))
       \<le> plus_down prec (nprt a * pprt bb)
           (plus_down prec (nprt b * nprt bb)
             (plus_down prec (pprt a * pprt ab)
               (pprt b * nprt ab)))"
  apply (rule order_trans)
   apply (rule mono_rules | assumption)+
    apply (rule mult_mono_nonpos_nonneg)
       apply (rule mono_rules | assumption)+
    apply (rule mult_mono_nonpos_nonpos)
       apply (rule mono_rules | assumption)+
    apply (rule mult_mono)
       apply (rule mono_rules | assumption)+
   apply (rule mult_mono_nonneg_nonpos)
      apply (rule mono_rules | assumption)+
  by (rule order_refl)+

lemma mult_float_mono2:
  notes mono_rules = plus_up_mono add_mono nprt_mono nprt_le_zero zero_le_pprt pprt_mono
  shows "a \<le> b \<Longrightarrow>
       ab \<le> bb \<Longrightarrow>
       aa \<le> a \<Longrightarrow>
       b \<le> ba \<Longrightarrow>
       ac \<le> ab \<Longrightarrow>
       bb \<le> bc \<Longrightarrow>
       plus_up prec (pprt b * pprt bb)
        (plus_up prec (pprt a * nprt bb)
          (plus_up prec (nprt b * pprt ab)
            (nprt a * nprt ab)))
       \<le> plus_up prec (pprt ba * pprt bc)
           (plus_up prec (pprt aa * nprt bc)
             (plus_up prec (nprt ba * pprt ac)
               (nprt aa * nprt ac)))"
  apply (rule order_trans)
   apply (rule mono_rules | assumption)+
    apply (rule mult_mono)
       apply (rule mono_rules | assumption)+
    apply (rule mult_mono_nonneg_nonpos)
       apply (rule mono_rules | assumption)+
    apply (rule mult_mono_nonpos_nonneg)
       apply (rule mono_rules | assumption)+
   apply (rule mult_mono_nonpos_nonpos)
      apply (rule mono_rules | assumption)+
  by (rule order_refl)+


subsection \<open>Approximate Power\<close>

lemma div2_less_self[termination_simp]: "odd n \<Longrightarrow> n div 2 < n" for n :: nat
  by (simp add: odd_pos)

fun power_down :: "nat \<Rightarrow> real \<Rightarrow> nat \<Rightarrow> real"
where
  "power_down p x 0 = 1"
| "power_down p x (Suc n) =
    (if odd n then truncate_down (Suc p) ((power_down p x (Suc n div 2))\<^sup>2)
     else truncate_down (Suc p) (x * power_down p x n))"

fun power_up :: "nat \<Rightarrow> real \<Rightarrow> nat \<Rightarrow> real"
where
  "power_up p x 0 = 1"
| "power_up p x (Suc n) =
    (if odd n then truncate_up p ((power_up p x (Suc n div 2))\<^sup>2)
     else truncate_up p (x * power_up p x n))"

lift_definition power_up_fl :: "nat \<Rightarrow> float \<Rightarrow> nat \<Rightarrow> float" is power_up
  by (induct_tac rule: power_up.induct) simp_all

lift_definition power_down_fl :: "nat \<Rightarrow> float \<Rightarrow> nat \<Rightarrow> float" is power_down
  by (induct_tac rule: power_down.induct) simp_all

lemma power_float_transfer[transfer_rule]:
  "(rel_fun pcr_float (rel_fun (=) pcr_float)) (^) (^)"
  unfolding power_def
  by transfer_prover

lemma compute_power_up_fl[code]:
    "power_up_fl p x 0 = 1"
    "power_up_fl p x (Suc n) =
      (if odd n then float_round_up p ((power_up_fl p x (Suc n div 2))\<^sup>2)
       else float_round_up p (x * power_up_fl p x n))"
  and compute_power_down_fl[code]:
    "power_down_fl p x 0 = 1"
    "power_down_fl p x (Suc n) =
      (if odd n then float_round_down (Suc p) ((power_down_fl p x (Suc n div 2))\<^sup>2)
       else float_round_down (Suc p) (x * power_down_fl p x n))"
  unfolding atomize_conj by transfer simp

lemma power_down_pos: "0 < x \<Longrightarrow> 0 < power_down p x n"
  by (induct p x n rule: power_down.induct)
    (auto simp del: odd_Suc_div_two intro!: truncate_down_pos)

lemma power_down_nonneg: "0 \<le> x \<Longrightarrow> 0 \<le> power_down p x n"
  by (induct p x n rule: power_down.induct)
    (auto simp del: odd_Suc_div_two intro!: truncate_down_nonneg mult_nonneg_nonneg)

lemma power_down: "0 \<le> x \<Longrightarrow> power_down p x n \<le> x ^ n"
proof (induct p x n rule: power_down.induct)
  case (2 p x n)
  have ?case if "odd n"
  proof -
    from that 2 have "(power_down p x (Suc n div 2)) ^ 2 \<le> (x ^ (Suc n div 2)) ^ 2"
      by (auto intro: power_mono power_down_nonneg simp del: odd_Suc_div_two)
    also have "\<dots> = x ^ (Suc n div 2 * 2)"
      by (simp flip: power_mult)
    also have "Suc n div 2 * 2 = Suc n"
      using \<open>odd n\<close> by presburger
    finally show ?thesis
      using that by (auto intro!: truncate_down_le simp del: odd_Suc_div_two)
  qed
  then show ?case
    by (auto intro!: truncate_down_le mult_left_mono 2 mult_nonneg_nonneg power_down_nonneg)
qed simp

lemma power_up: "0 \<le> x \<Longrightarrow> x ^ n \<le> power_up p x n"
proof (induct p x n rule: power_up.induct)
  case (2 p x n)
  have ?case if "odd n"
  proof -
    from that even_Suc have "Suc n = Suc n div 2 * 2"
      by presburger
    then have "x ^ Suc n \<le> (x ^ (Suc n div 2))\<^sup>2"
      by (simp flip: power_mult)
    also from that 2 have "\<dots> \<le> (power_up p x (Suc n div 2))\<^sup>2"
      by (auto intro: power_mono simp del: odd_Suc_div_two)
    finally show ?thesis
      using that by (auto intro!: truncate_up_le simp del: odd_Suc_div_two)
  qed
  then show ?case
    by (auto intro!: truncate_up_le mult_left_mono 2)
qed simp

lemmas power_up_le = order_trans[OF _ power_up]
  and power_up_less = less_le_trans[OF _ power_up]
  and power_down_le = order_trans[OF power_down]

lemma power_down_fl: "0 \<le> x \<Longrightarrow> power_down_fl p x n \<le> x ^ n"
  by transfer (rule power_down)

lemma power_up_fl: "0 \<le> x \<Longrightarrow> x ^ n \<le> power_up_fl p x n"
  by transfer (rule power_up)

lemma real_power_up_fl: "real_of_float (power_up_fl p x n) = power_up p x n"
  by transfer simp

lemma real_power_down_fl: "real_of_float (power_down_fl p x n) = power_down p x n"
  by transfer simp

lemmas [simp del] = power_down.simps(2) power_up.simps(2)

lemmas power_down_simp = power_down.simps(2)
lemmas power_up_simp = power_up.simps(2)

lemma power_down_even_nonneg: "even n \<Longrightarrow> 0 \<le> power_down p x n"
  by (induct p x n rule: power_down.induct)
    (auto simp: power_down_simp simp del: odd_Suc_div_two intro!: truncate_down_nonneg )

lemma power_down_eq_zero_iff[simp]: "power_down prec b n = 0 \<longleftrightarrow> b = 0 \<and> n \<noteq> 0"
proof (induction n arbitrary: b rule: less_induct)
  case (less x)
  then show ?case
    using power_down_simp[of _ _ "x - 1"]
    by (cases x) (auto simp add: div2_less_self)
qed

lemma power_down_nonneg_iff[simp]:
  "power_down prec b n \<ge> 0 \<longleftrightarrow> even n \<or> b \<ge> 0"
proof (induction n arbitrary: b rule: less_induct)
  case (less x)
  show ?case
    using less(1)[of "x - 1" b] power_down_simp[of _ _ "x - 1"]
    by (cases x) (auto simp: algebra_split_simps zero_le_mult_iff)
qed

lemma power_down_neg_iff[simp]:
  "power_down prec b n < 0 \<longleftrightarrow>
    b < 0 \<and> odd n"
  using power_down_nonneg_iff[of prec b n] by (auto simp del: power_down_nonneg_iff)

lemma power_down_nonpos_iff[simp]:
  notes [simp del] = power_down_neg_iff power_down_eq_zero_iff
  shows "power_down prec b n \<le> 0 \<longleftrightarrow> b < 0 \<and> odd n \<or> b = 0 \<and> n \<noteq> 0"
  using power_down_neg_iff[of prec b n] power_down_eq_zero_iff[of prec b n]
  by auto

lemma power_down_mono:
  "power_down prec a n \<le> power_down prec b n"
  if "((0 \<le> a \<and> a \<le> b)\<or>(odd n \<and> a \<le> b) \<or> (even n \<and> a \<le> 0 \<and> b \<le> a))"
  using that
proof (induction n arbitrary: a b rule: less_induct)
  case (less i)
  show ?case
  proof (cases i)
    case j: (Suc j)
    note IH = less[unfolded j even_Suc not_not]
    note [simp del] = power_down.simps
    show ?thesis
    proof cases
      assume [simp]: "even j"
      have "a * power_down prec a j \<le> b * power_down prec b j"
        by (metis IH(1) IH(2) \<open>even j\<close> lessI linear mult_mono mult_mono' mult_mono_nonpos_nonneg power_down_even_nonneg)
      then have "truncate_down (Suc prec) (a * power_down prec a j) \<le> truncate_down (Suc prec) (b * power_down prec b j)"
        by (auto intro!: truncate_down_mono simp: abs_le_square_iff[symmetric] abs_real_def)
      then show ?thesis
        unfolding j
        by (simp add: power_down_simp)
    next
      assume [simp]: "odd j"
      have "power_down prec 0 (Suc (j div 2)) \<le> - power_down prec b (Suc (j div 2))"
        if "b < 0" "even (j div 2)"
        apply (rule order_trans[where y=0])
        using IH that by (auto simp: div2_less_self)
      then have "truncate_down (Suc prec) ((power_down prec a (Suc (j div 2)))\<^sup>2)
        \<le> truncate_down (Suc prec) ((power_down prec b (Suc (j div 2)))\<^sup>2)"
        using IH
        by (auto intro!: truncate_down_mono intro: order_trans[where y=0]
            simp: abs_le_square_iff[symmetric] abs_real_def
            div2_less_self)
      then show ?thesis
        unfolding j
        by (simp add: power_down_simp)
    qed
  qed simp
qed

lemma power_up_even_nonneg: "even n \<Longrightarrow> 0 \<le> power_up p x n"
  by (induct p x n rule: power_up.induct)
    (auto simp: power_up.simps simp del: odd_Suc_div_two intro!: )

lemma power_up_eq_zero_iff[simp]: "power_up prec b n = 0 \<longleftrightarrow> b = 0 \<and> n \<noteq> 0"
proof (induction n arbitrary: b rule: less_induct)
  case (less x)
  then show ?case
    using power_up_simp[of _ _ "x - 1"]
    by (cases x) (auto simp: algebra_split_simps zero_le_mult_iff div2_less_self)
qed

lemma power_up_nonneg_iff[simp]:
  "power_up prec b n \<ge> 0 \<longleftrightarrow> even n \<or> b \<ge> 0"
proof (induction n arbitrary: b rule: less_induct)
  case (less x)
  show ?case
    using less(1)[of "x - 1" b] power_up_simp[of _ _ "x - 1"]
    by (cases x) (auto simp: algebra_split_simps zero_le_mult_iff)
qed

lemma power_up_neg_iff[simp]:
  "power_up prec b n < 0 \<longleftrightarrow> b < 0 \<and> odd n"
  using power_up_nonneg_iff[of prec b n] by (auto simp del: power_up_nonneg_iff)

lemma power_up_nonpos_iff[simp]:
  notes [simp del] = power_up_neg_iff power_up_eq_zero_iff
  shows "power_up prec b n \<le> 0 \<longleftrightarrow> b < 0 \<and> odd n \<or> b = 0 \<and> n \<noteq> 0"
  using power_up_neg_iff[of prec b n] power_up_eq_zero_iff[of prec b n]
  by auto

lemma power_up_mono:
  "power_up prec a n \<le> power_up prec b n"
  if "((0 \<le> a \<and> a \<le> b)\<or>(odd n \<and> a \<le> b) \<or> (even n \<and> a \<le> 0 \<and> b \<le> a))"
  using that
proof (induction n arbitrary: a b rule: less_induct)
  case (less i)
  show ?case
  proof (cases i)
    case j: (Suc j)
    note IH = less[unfolded j even_Suc not_not]
    note [simp del] = power_up.simps
    show ?thesis
    proof cases
      assume [simp]: "even j"
      have "a * power_up prec a j \<le> b * power_up prec b j"
        by (metis IH(1) IH(2) \<open>even j\<close> lessI linear mult_mono mult_mono' mult_mono_nonpos_nonneg power_up_even_nonneg)
      then have "truncate_up prec (a * power_up prec a j) \<le> truncate_up prec (b * power_up prec b j)"
        by (auto intro!: truncate_up_mono simp: abs_le_square_iff[symmetric] abs_real_def)
      then show ?thesis
        unfolding j
        by (simp add: power_up_simp)
    next
      assume [simp]: "odd j"
      have "power_up prec 0 (Suc (j div 2)) \<le> - power_up prec b (Suc (j div 2))"
        if "b < 0" "even (j div 2)"
        apply (rule order_trans[where y=0])
        using IH that by (auto simp: div2_less_self)
      then have "truncate_up prec ((power_up prec a (Suc (j div 2)))\<^sup>2)
        \<le> truncate_up prec ((power_up prec b (Suc (j div 2)))\<^sup>2)"
        using IH
        by (auto intro!: truncate_up_mono intro: order_trans[where y=0]
            simp: abs_le_square_iff[symmetric] abs_real_def
            div2_less_self)
      then show ?thesis
        unfolding j
        by (simp add: power_up_simp)
    qed
  qed simp
qed


subsection \<open>Lemmas needed by Approximate\<close>

lemma Float_num[simp]:
   "real_of_float (Float 1 0) = 1"
   "real_of_float (Float 1 1) = 2"
   "real_of_float (Float 1 2) = 4"
   "real_of_float (Float 1 (- 1)) = 1/2"
   "real_of_float (Float 1 (- 2)) = 1/4"
   "real_of_float (Float 1 (- 3)) = 1/8"
   "real_of_float (Float (- 1) 0) = -1"
   "real_of_float (Float (numeral n) 0) = numeral n"
   "real_of_float (Float (- numeral n) 0) = - numeral n"
  using two_powr_int_float[of 2] two_powr_int_float[of "-1"] two_powr_int_float[of "-2"]
    two_powr_int_float[of "-3"]
  using powr_realpow[of 2 2] powr_realpow[of 2 3]
  using powr_minus[of "2::real" 1] powr_minus[of "2::real" 2] powr_minus[of "2::real" 3]
  by auto

lemma real_of_Float_int[simp]: "real_of_float (Float n 0) = real n"
  by simp

lemma float_zero[simp]: "real_of_float (Float 0 e) = 0"
  by simp

lemma abs_div_2_less: "a \<noteq> 0 \<Longrightarrow> a \<noteq> -1 \<Longrightarrow> \<bar>(a::int) div 2\<bar> < \<bar>a\<bar>"
  by arith

lemma lapprox_rat: "real_of_float (lapprox_rat prec x y) \<le> real_of_int x / real_of_int y"
  by (simp add: lapprox_rat.rep_eq truncate_down)

lemma mult_div_le:
  fixes a b :: int
  assumes "b > 0"
  shows "a \<ge> b * (a div b)"
proof -
  from minus_div_mult_eq_mod [symmetric, of a b] have "a = b * (a div b) + a mod b"
    by simp
  also have "\<dots> \<ge> b * (a div b) + 0"
    apply (rule add_left_mono)
    apply (rule pos_mod_sign)
    using assms
    apply simp
    done
  finally show ?thesis
    by simp
qed

lemma lapprox_rat_nonneg:
  assumes "0 \<le> x" and "0 \<le> y"
  shows "0 \<le> real_of_float (lapprox_rat n x y)"
  using assms
  by transfer (simp add: truncate_down_nonneg)

lemma rapprox_rat: "real_of_int x / real_of_int y \<le> real_of_float (rapprox_rat prec x y)"
  by transfer (simp add: truncate_up)

lemma rapprox_rat_le1:
  assumes "0 \<le> x" "0 < y" "x \<le> y"
  shows "real_of_float (rapprox_rat n x y) \<le> 1"
  using assms
  by transfer (simp add: truncate_up_le1)

lemma rapprox_rat_nonneg_nonpos: "0 \<le> x \<Longrightarrow> y \<le> 0 \<Longrightarrow> real_of_float (rapprox_rat n x y) \<le> 0"
  by transfer (simp add: truncate_up_nonpos divide_nonneg_nonpos)

lemma rapprox_rat_nonpos_nonneg: "x \<le> 0 \<Longrightarrow> 0 \<le> y \<Longrightarrow> real_of_float (rapprox_rat n x y) \<le> 0"
  by transfer (simp add: truncate_up_nonpos divide_nonpos_nonneg)

lemma real_divl: "real_divl prec x y \<le> x / y"
  by (simp add: real_divl_def truncate_down)

lemma real_divr: "x / y \<le> real_divr prec x y"
  by (simp add: real_divr_def truncate_up)

lemma float_divl: "real_of_float (float_divl prec x y) \<le> x / y"
  by transfer (rule real_divl)

lemma real_divl_lower_bound: "0 \<le> x \<Longrightarrow> 0 \<le> y \<Longrightarrow> 0 \<le> real_divl prec x y"
  by (simp add: real_divl_def truncate_down_nonneg)

lemma float_divl_lower_bound: "0 \<le> x \<Longrightarrow> 0 \<le> y \<Longrightarrow> 0 \<le> real_of_float (float_divl prec x y)"
  by transfer (rule real_divl_lower_bound)

lemma exponent_1: "exponent 1 = 0"
  using exponent_float[of 1 0] by (simp add: one_float_def)

lemma mantissa_1: "mantissa 1 = 1"
  using mantissa_float[of 1 0] by (simp add: one_float_def)

lemma bitlen_1: "bitlen 1 = 1"
  by (simp add: bitlen_alt_def)

lemma float_upper_bound: "x \<le> 2 powr (bitlen \<bar>mantissa x\<bar> + exponent x)"
proof (cases "x = 0")
  case True
  then show ?thesis by simp
next
  case False
  then have "mantissa x \<noteq> 0"
    using mantissa_eq_zero_iff by auto
  have "x = mantissa x * 2 powr (exponent x)"
    by (rule mantissa_exponent)
  also have "mantissa x \<le> \<bar>mantissa x\<bar>"
    by simp
  also have "\<dots> \<le> 2 powr (bitlen \<bar>mantissa x\<bar>)"
    using bitlen_bounds[of "\<bar>mantissa x\<bar>"] bitlen_nonneg \<open>mantissa x \<noteq> 0\<close>
    by (auto simp del: of_int_abs simp add: powr_int)
  finally show ?thesis by (simp add: powr_add)
qed

lemma real_divl_pos_less1_bound:
  assumes "0 < x" "x \<le> 1"
  shows "1 \<le> real_divl prec 1 x"
  using assms
  by (auto intro!: truncate_down_ge1 simp: real_divl_def)

lemma float_divl_pos_less1_bound:
  "0 < real_of_float x \<Longrightarrow> real_of_float x \<le> 1 \<Longrightarrow> prec \<ge> 1 \<Longrightarrow>
    1 \<le> real_of_float (float_divl prec 1 x)"
  by transfer (rule real_divl_pos_less1_bound)

lemma float_divr: "real_of_float x / real_of_float y \<le> real_of_float (float_divr prec x y)"
  by transfer (rule real_divr)

lemma real_divr_pos_less1_lower_bound:
  assumes "0 < x"
    and "x \<le> 1"
  shows "1 \<le> real_divr prec 1 x"
proof -
  have "1 \<le> 1 / x"
    using \<open>0 < x\<close> and \<open>x \<le> 1\<close> by auto
  also have "\<dots> \<le> real_divr prec 1 x"
    using real_divr[where x = 1 and y = x] by auto
  finally show ?thesis by auto
qed

lemma float_divr_pos_less1_lower_bound: "0 < x \<Longrightarrow> x \<le> 1 \<Longrightarrow> 1 \<le> float_divr prec 1 x"
  by transfer (rule real_divr_pos_less1_lower_bound)

lemma real_divr_nonpos_pos_upper_bound: "x \<le> 0 \<Longrightarrow> 0 \<le> y \<Longrightarrow> real_divr prec x y \<le> 0"
  by (simp add: real_divr_def truncate_up_nonpos divide_le_0_iff)

lemma float_divr_nonpos_pos_upper_bound:
  "real_of_float x \<le> 0 \<Longrightarrow> 0 \<le> real_of_float y \<Longrightarrow> real_of_float (float_divr prec x y) \<le> 0"
  by transfer (rule real_divr_nonpos_pos_upper_bound)

lemma real_divr_nonneg_neg_upper_bound: "0 \<le> x \<Longrightarrow> y \<le> 0 \<Longrightarrow> real_divr prec x y \<le> 0"
  by (simp add: real_divr_def truncate_up_nonpos divide_le_0_iff)

lemma float_divr_nonneg_neg_upper_bound:
  "0 \<le> real_of_float x \<Longrightarrow> real_of_float y \<le> 0 \<Longrightarrow> real_of_float (float_divr prec x y) \<le> 0"
  by transfer (rule real_divr_nonneg_neg_upper_bound)

lemma Float_le_zero_iff: "Float a b \<le> 0 \<longleftrightarrow> a \<le> 0"
  by (auto simp: zero_float_def mult_le_0_iff)

lemma real_of_float_pprt[simp]:
  fixes a :: float
  shows "real_of_float (pprt a) = pprt (real_of_float a)"
  unfolding pprt_def sup_float_def max_def sup_real_def by auto

lemma real_of_float_nprt[simp]:
  fixes a :: float
  shows "real_of_float (nprt a) = nprt (real_of_float a)"
  unfolding nprt_def inf_float_def min_def inf_real_def by auto

context
begin

lift_definition int_floor_fl :: "float \<Rightarrow> int" is floor .

qualified lemma compute_int_floor_fl[code]:
  "int_floor_fl (Float m e) = (if 0 \<le> e then m * 2 ^ nat e else m div (2 ^ (nat (-e))))"
  apply transfer
  apply (simp add: powr_int floor_divide_of_int_eq)
  apply (metis (no_types, hide_lams)floor_divide_of_int_eq of_int_numeral of_int_power floor_of_int of_int_mult)
  done

lift_definition floor_fl :: "float \<Rightarrow> float" is "\<lambda>x. real_of_int \<lfloor>x\<rfloor>"
  by simp

qualified lemma compute_floor_fl[code]:
  "floor_fl (Float m e) = (if 0 \<le> e then Float m e else Float (m div (2 ^ (nat (-e)))) 0)"
  apply transfer
  apply (simp add: powr_int floor_divide_of_int_eq)
  apply (metis (no_types, hide_lams)floor_divide_of_int_eq of_int_numeral of_int_power of_int_mult)
  done

end

lemma floor_fl: "real_of_float (floor_fl x) \<le> real_of_float x"
  by transfer simp

lemma int_floor_fl: "real_of_int (int_floor_fl x) \<le> real_of_float x"
  by transfer simp

lemma floor_pos_exp: "exponent (floor_fl x) \<ge> 0"
proof (cases "floor_fl x = 0")
  case True
  then show ?thesis
    by (simp add: floor_fl_def)
next
  case False
  have eq: "floor_fl x = Float \<lfloor>real_of_float x\<rfloor> 0"
    by transfer simp
  obtain i where "\<lfloor>real_of_float x\<rfloor> = mantissa (floor_fl x) * 2 ^ i" "0 = exponent (floor_fl x) - int i"
    by (rule denormalize_shift[OF eq False])
  then show ?thesis
    by simp
qed

lemma compute_mantissa[code]:
  "mantissa (Float m e) =
    (if m = 0 then 0 else if 2 dvd m then mantissa (normfloat (Float m e)) else m)"
  by (auto simp: mantissa_float Float.abs_eq simp flip: zero_float_def)

lemma compute_exponent[code]:
  "exponent (Float m e) =
    (if m = 0 then 0 else if 2 dvd m then exponent (normfloat (Float m e)) else e)"
  by (auto simp: exponent_float Float.abs_eq simp flip: zero_float_def)

lifting_update Float.float.lifting
lifting_forget Float.float.lifting

end
