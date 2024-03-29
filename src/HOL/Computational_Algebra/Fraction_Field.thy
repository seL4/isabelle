(*  Title:      HOL/Computational_Algebra/Fraction_Field.thy
    Author:     Amine Chaieb, University of Cambridge
*)

section\<open>The fraction field of any integral domain\<close>

theory Fraction_Field
imports Main
begin

subsection \<open>General fractions construction\<close>

subsubsection \<open>Construction of the type of fractions\<close>

context idom begin

definition fractrel :: "'a \<times> 'a \<Rightarrow> 'a * 'a \<Rightarrow> bool" where
  "fractrel = (\<lambda>x y. snd x \<noteq> 0 \<and> snd y \<noteq> 0 \<and> fst x * snd y = fst y * snd x)"

lemma fractrel_iff [simp]:
  "fractrel x y \<longleftrightarrow> snd x \<noteq> 0 \<and> snd y \<noteq> 0 \<and> fst x * snd y = fst y * snd x"
  by (simp add: fractrel_def)

lemma symp_fractrel: "symp fractrel"
  by (simp add: symp_def)

lemma transp_fractrel: "transp fractrel"
proof (rule transpI, unfold split_paired_all)
  fix a b a' b' a'' b'' :: 'a
  assume A: "fractrel (a, b) (a', b')"
  assume B: "fractrel (a', b') (a'', b'')"
  have "b' * (a * b'') = b'' * (a * b')" by (simp add: ac_simps)
  also from A have "a * b' = a' * b" by auto
  also have "b'' * (a' * b) = b * (a' * b'')" by (simp add: ac_simps)
  also from B have "a' * b'' = a'' * b'" by auto
  also have "b * (a'' * b') = b' * (a'' * b)" by (simp add: ac_simps)
  finally have "b' * (a * b'') = b' * (a'' * b)" .
  moreover from B have "b' \<noteq> 0" by auto
  ultimately have "a * b'' = a'' * b" by simp
  with A B show "fractrel (a, b) (a'', b'')" by auto
qed

lemma part_equivp_fractrel: "part_equivp fractrel"
using _ symp_fractrel transp_fractrel
by(rule part_equivpI)(rule exI[where x="(0, 1)"]; simp)

end

quotient_type (overloaded) 'a fract = "'a :: idom \<times> 'a" / partial: "fractrel"
by(rule part_equivp_fractrel)

subsubsection \<open>Representation and basic operations\<close>

lift_definition Fract :: "'a :: idom \<Rightarrow> 'a \<Rightarrow> 'a fract"
  is "\<lambda>a b. if b = 0 then (0, 1) else (a, b)"
  by simp

lemma Fract_cases [cases type: fract]:
  obtains (Fract) a b where "q = Fract a b" "b \<noteq> 0"
by transfer simp

lemma Fract_induct [case_names Fract, induct type: fract]:
  "(\<And>a b. b \<noteq> 0 \<Longrightarrow> P (Fract a b)) \<Longrightarrow> P q"
  by (cases q) simp

lemma eq_fract:
  shows "\<And>a b c d. b \<noteq> 0 \<Longrightarrow> d \<noteq> 0 \<Longrightarrow> Fract a b = Fract c d \<longleftrightarrow> a * d = c * b"
    and "\<And>a. Fract a 0 = Fract 0 1"
    and "\<And>a c. Fract 0 a = Fract 0 c"
by(transfer; simp)+

instantiation fract :: (idom) comm_ring_1
begin

lift_definition zero_fract :: "'a fract" is "(0, 1)" by simp

lemma Zero_fract_def: "0 = Fract 0 1"
by transfer simp

lift_definition one_fract :: "'a fract" is "(1, 1)" by simp

lemma One_fract_def: "1 = Fract 1 1"
by transfer simp

lift_definition plus_fract :: "'a fract \<Rightarrow> 'a fract \<Rightarrow> 'a fract"
  is "\<lambda>q r. (fst q * snd r + fst r * snd q, snd q * snd r)"
by(auto simp add: algebra_simps)

lemma add_fract [simp]:
  "\<lbrakk> b \<noteq> 0; d \<noteq> 0 \<rbrakk> \<Longrightarrow> Fract a b + Fract c d = Fract (a * d + c * b) (b * d)"
by transfer simp

lift_definition uminus_fract :: "'a fract \<Rightarrow> 'a fract"
  is "\<lambda>x. (- fst x, snd x)"
by simp

lemma minus_fract [simp]:
  fixes a b :: "'a::idom"
  shows "- Fract a b = Fract (- a) b"
by transfer simp

lemma minus_fract_cancel [simp]: "Fract (- a) (- b) = Fract a b"
  by (cases "b = 0") (simp_all add: eq_fract)

definition diff_fract_def: "q - r = q + - (r::'a fract)"

lemma diff_fract [simp]:
  "\<lbrakk> b \<noteq> 0; d \<noteq> 0 \<rbrakk> \<Longrightarrow> Fract a b - Fract c d = Fract (a * d - c * b) (b * d)"
  by (simp add: diff_fract_def)

lift_definition times_fract :: "'a fract \<Rightarrow> 'a fract \<Rightarrow> 'a fract"
  is "\<lambda>q r. (fst q * fst r, snd q * snd r)"
by(simp add: algebra_simps)

lemma mult_fract [simp]: "Fract (a::'a::idom) b * Fract c d = Fract (a * c) (b * d)"
by transfer simp

lemma mult_fract_cancel:
  "c \<noteq> 0 \<Longrightarrow> Fract (c * a) (c * b) = Fract a b"
by transfer simp

instance
proof
  fix q r s :: "'a fract"
  show "(q * r) * s = q * (r * s)"
    by (cases q, cases r, cases s) (simp add: eq_fract algebra_simps)
  show "q * r = r * q"
    by (cases q, cases r) (simp add: eq_fract algebra_simps)
  show "1 * q = q"
    by (cases q) (simp add: One_fract_def eq_fract)
  show "(q + r) + s = q + (r + s)"
    by (cases q, cases r, cases s) (simp add: eq_fract algebra_simps)
  show "q + r = r + q"
    by (cases q, cases r) (simp add: eq_fract algebra_simps)
  show "0 + q = q"
    by (cases q) (simp add: Zero_fract_def eq_fract)
  show "- q + q = 0"
    by (cases q) (simp add: Zero_fract_def eq_fract)
  show "q - r = q + - r"
    by (cases q, cases r) (simp add: eq_fract)
  show "(q + r) * s = q * s + r * s"
    by (cases q, cases r, cases s) (simp add: eq_fract algebra_simps)
  show "(0::'a fract) \<noteq> 1"
    by (simp add: Zero_fract_def One_fract_def eq_fract)
qed

end

lemma of_nat_fract: "of_nat k = Fract (of_nat k) 1"
  by (induct k) (simp_all add: Zero_fract_def One_fract_def)

lemma Fract_of_nat_eq: "Fract (of_nat k) 1 = of_nat k"
  by (rule of_nat_fract [symmetric])

lemma fract_collapse:
  "Fract 0 k = 0"
  "Fract 1 1 = 1"
  "Fract k 0 = 0"
by(transfer; simp)+

lemma fract_expand:
  "0 = Fract 0 1"
  "1 = Fract 1 1"
  by (simp_all add: fract_collapse)

lemma Fract_cases_nonzero:
  obtains (Fract) a b where "q = Fract a b" and "b \<noteq> 0" and "a \<noteq> 0"
    | (0) "q = 0"
proof (cases "q = 0")
  case True
  then show thesis using 0 by auto
next
  case False
  then obtain a b where "q = Fract a b" and "b \<noteq> 0" by (cases q) auto
  with False have "0 \<noteq> Fract a b" by simp
  with \<open>b \<noteq> 0\<close> have "a \<noteq> 0" by (simp add: Zero_fract_def eq_fract)
  with Fract \<open>q = Fract a b\<close> \<open>b \<noteq> 0\<close> show thesis by auto
qed


subsubsection \<open>The field of rational numbers\<close>

context idom
begin

subclass ring_no_zero_divisors ..

end

instantiation fract :: (idom) field
begin

lift_definition inverse_fract :: "'a fract \<Rightarrow> 'a fract"
  is "\<lambda>x. if fst x = 0 then (0, 1) else (snd x, fst x)"
by(auto simp add: algebra_simps)

lemma inverse_fract [simp]: "inverse (Fract a b) = Fract (b::'a::idom) a"
by transfer simp

definition divide_fract_def: "q div r = q * inverse (r:: 'a fract)"

lemma divide_fract [simp]: "Fract a b div Fract c d = Fract (a * d) (b * c)"
  by (simp add: divide_fract_def)

instance
proof
  fix q :: "'a fract"
  assume "q \<noteq> 0"
  then show "inverse q * q = 1"
    by (cases q rule: Fract_cases_nonzero)
      (simp_all add: fract_expand eq_fract mult.commute)
next
  fix q r :: "'a fract"
  show "q div r = q * inverse r" by (simp add: divide_fract_def)
next
  show "inverse 0 = (0:: 'a fract)"
    by (simp add: fract_expand) (simp add: fract_collapse)
qed

end


subsubsection \<open>The ordered field of fractions over an ordered idom\<close>

instantiation fract :: (linordered_idom) linorder
begin

lemma less_eq_fract_respect:
  fixes a b a' b' c d c' d' :: 'a
  assumes neq: "b \<noteq> 0"  "b' \<noteq> 0"  "d \<noteq> 0"  "d' \<noteq> 0"
  assumes eq1: "a * b' = a' * b"
  assumes eq2: "c * d' = c' * d"
  shows "((a * d) * (b * d) \<le> (c * b) * (b * d)) \<longleftrightarrow> ((a' * d') * (b' * d') \<le> (c' * b') * (b' * d'))"
proof -
  let ?le = "\<lambda>a b c d. ((a * d) * (b * d) \<le> (c * b) * (b * d))"
  {
    fix a b c d x :: 'a
    assume x: "x \<noteq> 0"
    have "?le a b c d = ?le (a * x) (b * x) c d"
    proof -
      from x have "0 < x * x"
        by (auto simp add: zero_less_mult_iff)
      then have "?le a b c d =
          ((a * d) * (b * d) * (x * x) \<le> (c * b) * (b * d) * (x * x))"
        by (simp add: mult_le_cancel_right)
      also have "... = ?le (a * x) (b * x) c d"
        by (simp add: ac_simps)
      finally show ?thesis .
    qed
  } note le_factor = this

  let ?D = "b * d" and ?D' = "b' * d'"
  from neq have D: "?D \<noteq> 0" by simp
  from neq have "?D' \<noteq> 0" by simp
  then have "?le a b c d = ?le (a * ?D') (b * ?D') c d"
    by (rule le_factor)
  also have "... = ((a * b') * ?D * ?D' * d * d' \<le> (c * d') * ?D * ?D' * b * b')"
    by (simp add: ac_simps)
  also have "... = ((a' * b) * ?D * ?D' * d * d' \<le> (c' * d) * ?D * ?D' * b * b')"
    by (simp only: eq1 eq2)
  also have "... = ?le (a' * ?D) (b' * ?D) c' d'"
    by (simp add: ac_simps)
  also from D have "... = ?le a' b' c' d'"
    by (rule le_factor [symmetric])
  finally show "?le a b c d = ?le a' b' c' d'" .
qed

lift_definition less_eq_fract :: "'a fract \<Rightarrow> 'a fract \<Rightarrow> bool"
  is "\<lambda>q r. (fst q * snd r) * (snd q * snd r) \<le> (fst r * snd q) * (snd q * snd r)"
by (clarsimp simp add: less_eq_fract_respect)

definition less_fract_def: "z < (w::'a fract) \<longleftrightarrow> z \<le> w \<and> \<not> w \<le> z"

lemma le_fract [simp]:
  "\<lbrakk> b \<noteq> 0; d \<noteq> 0 \<rbrakk> \<Longrightarrow> Fract a b \<le> Fract c d \<longleftrightarrow> (a * d) * (b * d) \<le> (c * b) * (b * d)"
  by transfer simp

lemma less_fract [simp]:
  "\<lbrakk> b \<noteq> 0; d \<noteq> 0 \<rbrakk> \<Longrightarrow> Fract a b < Fract c d \<longleftrightarrow> (a * d) * (b * d) < (c * b) * (b * d)"
  by (simp add: less_fract_def less_le_not_le ac_simps)

instance
proof
  fix q r s :: "'a fract"
  assume "q \<le> r" and "r \<le> s"
  then show "q \<le> s"
  proof (induct q, induct r, induct s)
    fix a b c d e f :: 'a
    assume neq: "b \<noteq> 0" "d \<noteq> 0" "f \<noteq> 0"
    assume 1: "Fract a b \<le> Fract c d"
    assume 2: "Fract c d \<le> Fract e f"
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
      also have "... = (c * f) * (d * f) * (b * b)"
        by (simp only: ac_simps)
      also have "... \<le> (e * d) * (d * f) * (b * b)"
      proof -
        from neq 2 have "(c * f) * (d * f) \<le> (e * d) * (d * f)"
          by simp
        with bb show ?thesis by (simp add: mult_le_cancel_right)
      qed
      finally have "(a * f) * (b * f) * (d * d) \<le> e * b * (b * f) * (d * d)"
        by (simp only: ac_simps)
      with dd have "(a * f) * (b * f) \<le> (e * b) * (b * f)"
        by (simp add: mult_le_cancel_right)
      with neq show ?thesis by simp
    qed
  qed
next
  fix q r :: "'a fract"
  assume "q \<le> r" and "r \<le> q"
  then show "q = r"
  proof (induct q, induct r)
    fix a b c d :: 'a
    assume neq: "b \<noteq> 0" "d \<noteq> 0"
    assume 1: "Fract a b \<le> Fract c d"
    assume 2: "Fract c d \<le> Fract a b"
    show "Fract a b = Fract c d"
    proof -
      from neq 1 have "(a * d) * (b * d) \<le> (c * b) * (b * d)"
        by simp
      also have "... \<le> (a * d) * (b * d)"
      proof -
        from neq 2 have "(c * b) * (d * b) \<le> (a * d) * (d * b)"
          by simp
        then show ?thesis by (simp only: ac_simps)
      qed
      finally have "(a * d) * (b * d) = (c * b) * (b * d)" .
      moreover from neq have "b * d \<noteq> 0" by simp
      ultimately have "a * d = c * b" by simp
      with neq show ?thesis by (simp add: eq_fract)
    qed
  qed
next
  fix q r :: "'a fract"
  show "q \<le> q"
    by (induct q) simp
  show "(q < r) = (q \<le> r \<and> \<not> r \<le> q)"
    by (simp only: less_fract_def)
  show "q \<le> r \<or> r \<le> q"
    by (induct q, induct r)
       (simp add: mult.commute, rule linorder_linear)
qed

end

instantiation fract :: (linordered_idom) linordered_field
begin

definition abs_fract_def2:
  "\<bar>q\<bar> = (if q < 0 then -q else (q::'a fract))"

definition sgn_fract_def:
  "sgn (q::'a fract) = (if q = 0 then 0 else if 0 < q then 1 else - 1)"

theorem abs_fract [simp]: "\<bar>Fract a b\<bar> = Fract \<bar>a\<bar> \<bar>b\<bar>"
  unfolding abs_fract_def2 not_le [symmetric]
  by transfer (auto simp add: zero_less_mult_iff le_less)

instance proof
  fix q r s :: "'a fract"
  assume "q \<le> r"
  then show "s + q \<le> s + r"
  proof (induct q, induct r, induct s)
    fix a b c d e f :: 'a
    assume neq: "b \<noteq> 0" "d \<noteq> 0" "f \<noteq> 0"
    assume le: "Fract a b \<le> Fract c d"
    show "Fract e f + Fract a b \<le> Fract e f + Fract c d"
    proof -
      let ?F = "f * f" from neq have F: "0 < ?F"
        by (auto simp add: zero_less_mult_iff)
      from neq le have "(a * d) * (b * d) \<le> (c * b) * (b * d)"
        by simp
      with F have "(a * d) * (b * d) * ?F * ?F \<le> (c * b) * (b * d) * ?F * ?F"
        by (simp add: mult_le_cancel_right)
      with neq show ?thesis by (simp add: field_simps)
    qed
  qed
next
  fix q r s :: "'a fract"
  assume "q < r" and "0 < s"
  then show "s * q < s * r"
  proof (induct q, induct r, induct s)
    fix a b c d e f :: 'a
    assume neq: "b \<noteq> 0" "d \<noteq> 0" "f \<noteq> 0"
    assume le: "Fract a b < Fract c d"
    assume gt: "0 < Fract e f"
    show "Fract e f * Fract a b < Fract e f * Fract c d"
    proof -
      let ?E = "e * f" and ?F = "f * f"
      from neq gt have "0 < ?E"
        by (auto simp add: Zero_fract_def order_less_le eq_fract)
      moreover from neq have "0 < ?F"
        by (auto simp add: zero_less_mult_iff)
      moreover from neq le have "(a * d) * (b * d) < (c * b) * (b * d)"
        by simp
      ultimately have "(a * d) * (b * d) * ?E * ?F < (c * b) * (b * d) * ?E * ?F"
        by (simp add: mult_less_cancel_right)
      with neq show ?thesis
        by (simp add: ac_simps)
    qed
  qed
qed (fact sgn_fract_def abs_fract_def2)+

end

instantiation fract :: (linordered_idom) distrib_lattice
begin

definition inf_fract_def:
  "(inf :: 'a fract \<Rightarrow> 'a fract \<Rightarrow> 'a fract) = min"

definition sup_fract_def:
  "(sup :: 'a fract \<Rightarrow> 'a fract \<Rightarrow> 'a fract) = max"

instance
  by standard (simp_all add: inf_fract_def sup_fract_def max_min_distrib2)
  
end

lemma fract_induct_pos [case_names Fract]:
  fixes P :: "'a::linordered_idom fract \<Rightarrow> bool"
  assumes step: "\<And>a b. 0 < b \<Longrightarrow> P (Fract a b)"
  shows "P q"
proof (cases q)
  case (Fract a b)
  {
    fix a b :: 'a
    assume b: "b < 0"
    have "P (Fract a b)"
    proof -
      from b have "0 < - b" by simp
      then have "P (Fract (- a) (- b))"
        by (rule step)
      then show "P (Fract a b)"
        by (simp add: order_less_imp_not_eq [OF b])
    qed
  }
  with Fract show "P q"
    by (auto simp add: linorder_neq_iff step)
qed

lemma zero_less_Fract_iff: "0 < b \<Longrightarrow> 0 < Fract a b \<longleftrightarrow> 0 < a"
  by (auto simp add: Zero_fract_def zero_less_mult_iff)

lemma Fract_less_zero_iff: "0 < b \<Longrightarrow> Fract a b < 0 \<longleftrightarrow> a < 0"
  by (auto simp add: Zero_fract_def mult_less_0_iff)

lemma zero_le_Fract_iff: "0 < b \<Longrightarrow> 0 \<le> Fract a b \<longleftrightarrow> 0 \<le> a"
  by (auto simp add: Zero_fract_def zero_le_mult_iff)

lemma Fract_le_zero_iff: "0 < b \<Longrightarrow> Fract a b \<le> 0 \<longleftrightarrow> a \<le> 0"
  by (auto simp add: Zero_fract_def mult_le_0_iff)

lemma one_less_Fract_iff: "0 < b \<Longrightarrow> 1 < Fract a b \<longleftrightarrow> b < a"
  by (auto simp add: One_fract_def mult_less_cancel_right_disj)

lemma Fract_less_one_iff: "0 < b \<Longrightarrow> Fract a b < 1 \<longleftrightarrow> a < b"
  by (auto simp add: One_fract_def mult_less_cancel_right_disj)

lemma one_le_Fract_iff: "0 < b \<Longrightarrow> 1 \<le> Fract a b \<longleftrightarrow> b \<le> a"
  by (auto simp add: One_fract_def mult_le_cancel_right)

lemma Fract_le_one_iff: "0 < b \<Longrightarrow> Fract a b \<le> 1 \<longleftrightarrow> a \<le> b"
  by (auto simp add: One_fract_def mult_le_cancel_right)

end
