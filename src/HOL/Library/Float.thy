(*  Title:      HOL/Library/Float.thy
    Author:     Steven Obua 2008
    Author:     Johannes Hoelzl, TU Muenchen <hoelzl@in.tum.de> 2008 / 2009
*)

header {* Floating-Point Numbers *}

theory Float
imports Complex_Main Lattice_Algebras
begin

definition pow2 :: "int \<Rightarrow> real" where
  [simp]: "pow2 a = (if (0 <= a) then (2^(nat a)) else (inverse (2^(nat (-a)))))"

datatype float = Float int int

primrec of_float :: "float \<Rightarrow> real" where
  "of_float (Float a b) = real a * pow2 b"

defs (overloaded)
  real_of_float_def [code_unfold]: "real == of_float"

declare [[coercion "% x . Float x 0"]]
declare [[coercion "real::float\<Rightarrow>real"]]

primrec mantissa :: "float \<Rightarrow> int" where
  "mantissa (Float a b) = a"

primrec scale :: "float \<Rightarrow> int" where
  "scale (Float a b) = b"

instantiation float :: zero
begin
definition zero_float where "0 = Float 0 0"
instance ..
end

instantiation float :: one
begin
definition one_float where "1 = Float 1 0"
instance ..
end

lemma real_of_float_simp[simp]: "real (Float a b) = real a * pow2 b"
  unfolding real_of_float_def using of_float.simps .

lemma real_of_float_neg_exp: "e < 0 \<Longrightarrow> real (Float m e) = real m * inverse (2^nat (-e))" by auto
lemma real_of_float_nge0_exp: "\<not> 0 \<le> e \<Longrightarrow> real (Float m e) = real m * inverse (2^nat (-e))" by auto
lemma real_of_float_ge0_exp: "0 \<le> e \<Longrightarrow> real (Float m e) = real m * (2^nat e)" by auto

lemma Float_num[simp]: shows
   "real (Float 1 0) = 1" and "real (Float 1 1) = 2" and "real (Float 1 2) = 4" and
   "real (Float 1 -1) = 1/2" and "real (Float 1 -2) = 1/4" and "real (Float 1 -3) = 1/8" and
   "real (Float -1 0) = -1" and "real (Float (numeral n) 0) = numeral n"
  by auto

lemma float_number_of_int[simp]: "real (Float n 0) = real n"
  by simp

lemma pow2_0[simp]: "pow2 0 = 1" by simp
lemma pow2_1[simp]: "pow2 1 = 2" by simp
lemma pow2_neg: "pow2 x = inverse (pow2 (-x))" by simp

lemma pow2_powr: "pow2 a = 2 powr a"
  by (simp add: powr_realpow[symmetric] powr_minus)

declare pow2_def[simp del]

lemma pow2_add: "pow2 (a+b) = (pow2 a) * (pow2 b)"
  by (simp add: pow2_powr powr_add)

lemma pow2_diff: "pow2 (a - b) = pow2 a / pow2 b"
  by (simp add: pow2_powr powr_divide2)
  
lemma pow2_add1: "pow2 (1 + a) = 2 * (pow2 a)"
  by (simp add: pow2_add)

lemma float_components[simp]: "Float (mantissa f) (scale f) = f" by (cases f) auto

lemma float_split: "\<exists> a b. x = Float a b" by (cases x) auto

lemma float_split2: "(\<forall> a b. x \<noteq> Float a b) = False" by (auto simp add: float_split)

lemma float_zero[simp]: "real (Float 0 e) = 0" by simp

lemma abs_div_2_less: "a \<noteq> 0 \<Longrightarrow> a \<noteq> -1 \<Longrightarrow> abs((a::int) div 2) < abs a"
by arith

function normfloat :: "float \<Rightarrow> float" where
  "normfloat (Float a b) =
    (if a \<noteq> 0 \<and> even a then normfloat (Float (a div 2) (b+1))
     else if a=0 then Float 0 0 else Float a b)"
by pat_completeness auto
termination by (relation "measure (nat o abs o mantissa)") (auto intro: abs_div_2_less)
declare normfloat.simps[simp del]

theorem normfloat[symmetric, simp]: "real f = real (normfloat f)"
proof (induct f rule: normfloat.induct)
  case (1 a b)
  have real2: "2 = real (2::int)"
    by auto
  show ?case
    apply (subst normfloat.simps)
    apply auto
    apply (subst 1[symmetric])
    apply (auto simp add: pow2_add even_def)
    done
qed

lemma pow2_neq_zero[simp]: "pow2 x \<noteq> 0"
  by (auto simp add: pow2_def)

lemma pow2_int: "pow2 (int c) = 2^c"
  by (simp add: pow2_def)

lemma zero_less_pow2[simp]: "0 < pow2 x"
  by (simp add: pow2_powr)

lemma normfloat_imp_odd_or_zero:
  "normfloat f = Float a b \<Longrightarrow> odd a \<or> (a = 0 \<and> b = 0)"
proof (induct f rule: normfloat.induct)
  case (1 u v)
  from 1 have ab: "normfloat (Float u v) = Float a b" by auto
  {
    assume eu: "even u"
    assume z: "u \<noteq> 0"
    have "normfloat (Float u v) = normfloat (Float (u div 2) (v + 1))"
      apply (subst normfloat.simps)
      by (simp add: eu z)
    with ab have "normfloat (Float (u div 2) (v + 1)) = Float a b" by simp
    with 1 eu z have ?case by auto
  }
  note case1 = this
  {
    assume "odd u \<or> u = 0"
    then have ou: "\<not> (u \<noteq> 0 \<and> even u)" by auto
    have "normfloat (Float u v) = (if u = 0 then Float 0 0 else Float u v)"
      apply (subst normfloat.simps)
      apply (simp add: ou)
      done
    with ab have "Float a b = (if u = 0 then Float 0 0 else Float u v)" by auto
    then have ?case
      apply (case_tac "u=0")
      apply (auto)
      by (insert ou, auto)
  }
  note case2 = this
  show ?case
    apply (case_tac "odd u \<or> u = 0")
    apply (rule case2)
    apply simp
    apply (rule case1)
    apply auto
    done
qed

lemma float_eq_odd_helper: 
  assumes odd: "odd a'"
    and floateq: "real (Float a b) = real (Float a' b')"
  shows "b \<le> b'"
proof - 
  from odd have "a' \<noteq> 0" by auto
  with floateq have a': "real a' = real a * pow2 (b - b')"
    by (simp add: pow2_diff field_simps)

  {
    assume bcmp: "b > b'"
    then have "\<exists>c::nat. b - b' = int c + 1"
      by arith
    then guess c ..
    with a' have "real a' = real (a * 2^c * 2)"
      by (simp add: pow2_def nat_add_distrib)
    with odd have False
      unfolding real_of_int_inject by simp
  }
  then show ?thesis by arith
qed

lemma float_eq_odd: 
  assumes odd1: "odd a"
    and odd2: "odd a'"
    and floateq: "real (Float a b) = real (Float a' b')"
  shows "a = a' \<and> b = b'"
proof -
  from 
     float_eq_odd_helper[OF odd2 floateq] 
     float_eq_odd_helper[OF odd1 floateq[symmetric]]
  have beq: "b = b'" by arith
  with floateq show ?thesis by auto
qed

theorem normfloat_unique:
  assumes real_of_float_eq: "real f = real g"
  shows "normfloat f = normfloat g"
proof - 
  from float_split[of "normfloat f"] obtain a b where normf:"normfloat f = Float a b" by auto
  from float_split[of "normfloat g"] obtain a' b' where normg:"normfloat g = Float a' b'" by auto
  have "real (normfloat f) = real (normfloat g)"
    by (simp add: real_of_float_eq)
  then have float_eq: "real (Float a b) = real (Float a' b')"
    by (simp add: normf normg)
  have ab: "odd a \<or> (a = 0 \<and> b = 0)" by (rule normfloat_imp_odd_or_zero[OF normf])
  have ab': "odd a' \<or> (a' = 0 \<and> b' = 0)" by (rule normfloat_imp_odd_or_zero[OF normg])
  {
    assume odd: "odd a"
    then have "a \<noteq> 0" by (simp add: even_def) arith
    with float_eq have "a' \<noteq> 0" by auto
    with ab' have "odd a'" by simp
    from odd this float_eq have "a = a' \<and> b = b'" by (rule float_eq_odd)
  }
  note odd_case = this
  {
    assume even: "even a"
    with ab have a0: "a = 0" by simp
    with float_eq have a0': "a' = 0" by auto 
    from a0 a0' ab ab' have "a = a' \<and> b = b'" by auto
  }
  note even_case = this
  from odd_case even_case show ?thesis
    apply (simp add: normf normg)
    apply (case_tac "even a")
    apply auto
    done
qed

instantiation float :: plus
begin
fun plus_float where
[simp del]: "(Float a_m a_e) + (Float b_m b_e) = 
     (if a_e \<le> b_e then Float (a_m + b_m * 2^(nat(b_e - a_e))) a_e 
                   else Float (a_m * 2^(nat (a_e - b_e)) + b_m) b_e)"
instance ..
end

instantiation float :: uminus
begin
primrec uminus_float where [simp del]: "uminus_float (Float m e) = Float (-m) e"
instance ..
end

instantiation float :: minus
begin
definition minus_float where "(z::float) - w = z + (- w)"
instance ..
end

instantiation float :: times
begin
fun times_float where [simp del]: "(Float a_m a_e) * (Float b_m b_e) = Float (a_m * b_m) (a_e + b_e)"
instance ..
end

primrec float_pprt :: "float \<Rightarrow> float" where
  "float_pprt (Float a e) = (if 0 <= a then (Float a e) else 0)"

primrec float_nprt :: "float \<Rightarrow> float" where
  "float_nprt (Float a e) = (if 0 <= a then 0 else (Float a e))" 

instantiation float :: ord
begin
definition le_float_def: "z \<le> (w :: float) \<equiv> real z \<le> real w"
definition less_float_def: "z < (w :: float) \<equiv> real z < real w"
instance ..
end

lemma real_of_float_add[simp]: "real (a + b) = real a + real (b :: float)"
  by (cases a, cases b) (simp add: algebra_simps plus_float.simps, 
      auto simp add: pow2_int[symmetric] pow2_add[symmetric])

lemma real_of_float_minus[simp]: "real (- a) = - real (a :: float)"
  by (cases a) simp

lemma real_of_float_sub[simp]: "real (a - b) = real a - real (b :: float)"
  by (cases a, cases b) (simp add: minus_float_def)

lemma real_of_float_mult[simp]: "real (a*b) = real a * real (b :: float)"
  by (cases a, cases b) (simp add: times_float.simps pow2_add)

lemma real_of_float_0[simp]: "real (0 :: float) = 0"
  by (auto simp add: zero_float_def)

lemma real_of_float_1[simp]: "real (1 :: float) = 1"
  by (auto simp add: one_float_def)

lemma zero_le_float:
  "(0 <= real (Float a b)) = (0 <= a)"
  apply auto
  apply (auto simp add: zero_le_mult_iff)
  apply (insert zero_less_pow2[of b])
  apply (simp_all)
  done

lemma float_le_zero:
  "(real (Float a b) <= 0) = (a <= 0)"
  apply auto
  apply (auto simp add: mult_le_0_iff)
  apply (insert zero_less_pow2[of b])
  apply auto
  done

lemma zero_less_float:
  "(0 < real (Float a b)) = (0 < a)"
  apply auto
  apply (auto simp add: zero_less_mult_iff)
  apply (insert zero_less_pow2[of b])
  apply (simp_all)
  done

lemma float_less_zero:
  "(real (Float a b) < 0) = (a < 0)"
  apply auto
  apply (auto simp add: mult_less_0_iff)
  apply (insert zero_less_pow2[of b])
  apply (simp_all)
  done

declare real_of_float_simp[simp del]

lemma real_of_float_pprt[simp]: "real (float_pprt a) = pprt (real a)"
  by (cases a) (auto simp add: zero_le_float float_le_zero)

lemma real_of_float_nprt[simp]: "real (float_nprt a) = nprt (real a)"
  by (cases a) (auto simp add: zero_le_float float_le_zero)

instance float :: ab_semigroup_add
proof (intro_classes)
  fix a b c :: float
  show "a + b + c = a + (b + c)"
    by (cases a, cases b, cases c)
      (auto simp add: algebra_simps power_add[symmetric] plus_float.simps)
next
  fix a b :: float
  show "a + b = b + a"
    by (cases a, cases b) (simp add: plus_float.simps)
qed

instance float :: numeral ..

lemma Float_add_same_scale: "Float x e + Float y e = Float (x + y) e"
  by (simp add: plus_float.simps)

(* FIXME: define other constant for code_unfold_post *)
lemma numeral_float_Float (*[code_unfold_post]*):
  "numeral k = Float (numeral k) 0"
  by (induct k, simp_all only: numeral.simps one_float_def
    Float_add_same_scale)

lemma float_number_of[simp]: "real (numeral x :: float) = numeral x"
  by (simp only: numeral_float_Float Float_num)


instance float :: comm_monoid_mult
proof (intro_classes)
  fix a b c :: float
  show "a * b * c = a * (b * c)"
    by (cases a, cases b, cases c) (simp add: times_float.simps)
next
  fix a b :: float
  show "a * b = b * a"
    by (cases a, cases b) (simp add: times_float.simps)
next
  fix a :: float
  show "1 * a = a"
    by (cases a) (simp add: times_float.simps one_float_def)
qed

(* Floats do NOT form a cancel_semigroup_add: *)
lemma "0 + Float 0 1 = 0 + Float 0 2"
  by (simp add: plus_float.simps zero_float_def)

instance float :: comm_semiring
proof (intro_classes)
  fix a b c :: float
  show "(a + b) * c = a * c + b * c"
    by (cases a, cases b, cases c) (simp add: plus_float.simps times_float.simps algebra_simps)
qed

(* Floats do NOT form an order, because "(x < y) = (x <= y & x <> y)" does NOT hold *)

instance float :: zero_neq_one
proof (intro_classes)
  show "(0::float) \<noteq> 1"
    by (simp add: zero_float_def one_float_def)
qed

lemma float_le_simp: "((x::float) \<le> y) = (0 \<le> y - x)"
  by (auto simp add: le_float_def)

lemma float_less_simp: "((x::float) < y) = (0 < y - x)"
  by (auto simp add: less_float_def)

lemma real_of_float_min: "real (min x y :: float) = min (real x) (real y)" unfolding min_def le_float_def by auto
lemma real_of_float_max: "real (max a b :: float) = max (real a) (real b)" unfolding max_def le_float_def by auto

lemma float_power: "real (x ^ n :: float) = real x ^ n"
  by (induct n) simp_all

lemma zero_le_pow2[simp]: "0 \<le> pow2 s"
  apply (subgoal_tac "0 < pow2 s")
  apply (auto simp only:)
  apply auto
  done

lemma pow2_less_0_eq_False[simp]: "(pow2 s < 0) = False"
  apply auto
  apply (subgoal_tac "0 \<le> pow2 s")
  apply simp
  apply simp
  done

lemma pow2_le_0_eq_False[simp]: "(pow2 s \<le> 0) = False"
  apply auto
  apply (subgoal_tac "0 < pow2 s")
  apply simp
  apply simp
  done

lemma float_pos_m_pos: "0 < Float m e \<Longrightarrow> 0 < m"
  unfolding less_float_def real_of_float_simp real_of_float_0 zero_less_mult_iff
  by auto

lemma float_pos_less1_e_neg: assumes "0 < Float m e" and "Float m e < 1" shows "e < 0"
proof -
  have "0 < m" using float_pos_m_pos `0 < Float m e` by auto
  hence "0 \<le> real m" and "1 \<le> real m" by auto
  
  show "e < 0"
  proof (rule ccontr)
    assume "\<not> e < 0" hence "0 \<le> e" by auto
    hence "1 \<le> pow2 e" unfolding pow2_def by auto
    from mult_mono[OF `1 \<le> real m` this `0 \<le> real m`]
    have "1 \<le> Float m e" by (simp add: le_float_def real_of_float_simp)
    thus False using `Float m e < 1` unfolding less_float_def le_float_def by auto
  qed
qed

lemma float_less1_mantissa_bound: assumes "0 < Float m e" "Float m e < 1" shows "m < 2^(nat (-e))"
proof -
  have "e < 0" using float_pos_less1_e_neg assms by auto
  have "\<And>x. (0::real) < 2^x" by auto
  have "real m < 2^(nat (-e))" using `Float m e < 1`
    unfolding less_float_def real_of_float_neg_exp[OF `e < 0`] real_of_float_1
          real_mult_less_iff1[of _ _ 1, OF `0 < 2^(nat (-e))`, symmetric] 
          mult_assoc by auto
  thus ?thesis unfolding real_of_int_less_iff[symmetric] by auto
qed

function bitlen :: "int \<Rightarrow> int" where
"bitlen 0 = 0" | 
"bitlen -1 = 1" | 
"0 < x \<Longrightarrow> bitlen x = 1 + (bitlen (x div 2))" | 
"x < -1 \<Longrightarrow> bitlen x = 1 + (bitlen (x div 2))"
  apply (case_tac "x = 0 \<or> x = -1 \<or> x < -1 \<or> x > 0")
  apply auto
  done
termination by (relation "measure (nat o abs)", auto)

lemma bitlen_ge0: "0 \<le> bitlen x" by (induct x rule: bitlen.induct, auto)
lemma bitlen_ge1: "x \<noteq> 0 \<Longrightarrow> 1 \<le> bitlen x" by (induct x rule: bitlen.induct, auto simp add: bitlen_ge0)

lemma bitlen_bounds': assumes "0 < x" shows "2^nat (bitlen x - 1) \<le> x \<and> x + 1 \<le> 2^nat (bitlen x)" (is "?P x")
  using `0 < x`
proof (induct x rule: bitlen.induct)
  fix x
  assume "0 < x" and hyp: "0 < x div 2 \<Longrightarrow> ?P (x div 2)" hence "0 \<le> x" and "x \<noteq> 0" by auto
  { fix x have "0 \<le> 1 + bitlen x" using bitlen_ge0[of x] by auto } note gt0_pls1 = this

  have "0 < (2::int)" by auto

  show "?P x"
  proof (cases "x = 1")
    case True show "?P x" unfolding True by auto
  next
    case False hence "2 \<le> x" using `0 < x` `x \<noteq> 1` by auto
    hence "2 div 2 \<le> x div 2" by (rule zdiv_mono1, auto)
    hence "0 < x div 2" and "x div 2 \<noteq> 0" by auto
    hence bitlen_s1_ge0: "0 \<le> bitlen (x div 2) - 1" using bitlen_ge1[OF `x div 2 \<noteq> 0`] by auto

    { from hyp[OF `0 < x div 2`]
      have "2 ^ nat (bitlen (x div 2) - 1) \<le> x div 2" by auto
      hence "2 ^ nat (bitlen (x div 2) - 1) * 2 \<le> x div 2 * 2" by (rule mult_right_mono, auto)
      also have "\<dots> \<le> x" using `0 < x` by auto
      finally have "2^nat (1 + bitlen (x div 2) - 1) \<le> x" unfolding power_Suc2[symmetric] Suc_nat_eq_nat_zadd1[OF bitlen_s1_ge0] by auto
    } moreover
    { have "x + 1 \<le> x - x mod 2 + 2"
      proof -
        have "x mod 2 < 2" using `0 < x` by auto
        hence "x < x - x mod 2 +  2" unfolding algebra_simps by auto
        thus ?thesis by auto
      qed
      also have "x - x mod 2 + 2 = (x div 2 + 1) * 2" unfolding algebra_simps using `0 < x` div_mod_equality[of x 2 0] by auto
      also have "\<dots> \<le> 2^nat (bitlen (x div 2)) * 2" using hyp[OF `0 < x div 2`, THEN conjunct2] by (rule mult_right_mono, auto)
      also have "\<dots> = 2^(1 + nat (bitlen (x div 2)))" unfolding power_Suc2[symmetric] by auto
      finally have "x + 1 \<le> 2^(1 + nat (bitlen (x div 2)))" .
    }
    ultimately show ?thesis
      unfolding bitlen.simps(3)[OF `0 < x`] nat_add_distrib[OF zero_le_one bitlen_ge0]
      unfolding add_commute nat_add_distrib[OF zero_le_one gt0_pls1]
      by auto
  qed
next
  fix x :: int assume "x < -1" and "0 < x" hence False by auto
  thus "?P x" by auto
qed auto

lemma bitlen_bounds: assumes "0 < x" shows "2^nat (bitlen x - 1) \<le> x \<and> x < 2^nat (bitlen x)"
  using bitlen_bounds'[OF `0<x`] by auto

lemma bitlen_div: assumes "0 < m" shows "1 \<le> real m / 2^nat (bitlen m - 1)" and "real m / 2^nat (bitlen m - 1) < 2"
proof -
  let ?B = "2^nat(bitlen m - 1)"

  have "?B \<le> m" using bitlen_bounds[OF `0 <m`] ..
  hence "1 * ?B \<le> real m" unfolding real_of_int_le_iff[symmetric] by auto
  thus "1 \<le> real m / ?B" by auto

  have "m \<noteq> 0" using assms by auto
  have "0 \<le> bitlen m - 1" using bitlen_ge1[OF `m \<noteq> 0`] by auto

  have "m < 2^nat(bitlen m)" using bitlen_bounds[OF `0 <m`] ..
  also have "\<dots> = 2^nat(bitlen m - 1 + 1)" using bitlen_ge1[OF `m \<noteq> 0`] by auto
  also have "\<dots> = ?B * 2" unfolding nat_add_distrib[OF `0 \<le> bitlen m - 1` zero_le_one] by auto
  finally have "real m < 2 * ?B" unfolding real_of_int_less_iff[symmetric] by auto
  hence "real m / ?B < 2 * ?B / ?B" by (rule divide_strict_right_mono, auto)
  thus "real m / ?B < 2" by auto
qed

lemma float_gt1_scale: assumes "1 \<le> Float m e"
  shows "0 \<le> e + (bitlen m - 1)"
proof (cases "0 \<le> e")
  have "0 < Float m e" using assms unfolding less_float_def le_float_def by auto
  hence "0 < m" using float_pos_m_pos by auto
  hence "m \<noteq> 0" by auto
  case True with bitlen_ge1[OF `m \<noteq> 0`] show ?thesis by auto
next
  have "0 < Float m e" using assms unfolding less_float_def le_float_def by auto
  hence "0 < m" using float_pos_m_pos by auto
  hence "m \<noteq> 0" and "1 < (2::int)" by auto
  case False let ?S = "2^(nat (-e))"
  have "1 \<le> real m * inverse ?S" using assms unfolding le_float_def real_of_float_nge0_exp[OF False] by auto
  hence "1 * ?S \<le> real m * inverse ?S * ?S" by (rule mult_right_mono, auto)
  hence "?S \<le> real m" unfolding mult_assoc by auto
  hence "?S \<le> m" unfolding real_of_int_le_iff[symmetric] by auto
  from this bitlen_bounds[OF `0 < m`, THEN conjunct2]
  have "nat (-e) < (nat (bitlen m))" unfolding power_strict_increasing_iff[OF `1 < 2`, symmetric] by (rule order_le_less_trans)
  hence "-e < bitlen m" using False bitlen_ge0 by auto
  thus ?thesis by auto
qed

lemma normalized_float: assumes "m \<noteq> 0" shows "real (Float m (- (bitlen m - 1))) = real m / 2^nat (bitlen m - 1)"
proof (cases "- (bitlen m - 1) = 0")
  case True show ?thesis unfolding real_of_float_simp pow2_def using True by auto
next
  case False hence P: "\<not> 0 \<le> - (bitlen m - 1)" using bitlen_ge1[OF `m \<noteq> 0`] by auto
  show ?thesis unfolding real_of_float_nge0_exp[OF P] divide_inverse by auto
qed

(* BROKEN
lemma bitlen_Pls: "bitlen (Int.Pls) = Int.Pls" by (subst Pls_def, subst Pls_def, simp)

lemma bitlen_Min: "bitlen (Int.Min) = Int.Bit1 Int.Pls" by (subst Min_def, simp add: Bit1_def) 

lemma bitlen_B0: "bitlen (Int.Bit0 b) = (if iszero b then Int.Pls else Int.succ (bitlen b))"
  apply (auto simp add: iszero_def succ_def)
  apply (simp add: Bit0_def Pls_def)
  apply (subst Bit0_def)
  apply simp
  apply (subgoal_tac "0 < 2 * b \<or> 2 * b < -1")
  apply auto
  done

lemma bitlen_B1: "bitlen (Int.Bit1 b) = (if iszero (Int.succ b) then Int.Bit1 Int.Pls else Int.succ (bitlen b))"
proof -
  have h: "! x. (2*x + 1) div 2 = (x::int)"
    by arith    
  show ?thesis
    apply (auto simp add: iszero_def succ_def)
    apply (subst Bit1_def)+
    apply simp
    apply (subgoal_tac "2 * b + 1 = -1")
    apply (simp only:)
    apply simp_all
    apply (subst Bit1_def)
    apply simp
    apply (subgoal_tac "0 < 2 * b + 1 \<or> 2 * b + 1 < -1")
    apply (auto simp add: h)
    done
qed

lemma bitlen_number_of: "bitlen (number_of w) = number_of (bitlen w)"
  by (simp add: number_of_is_id)
BH *)

lemma [code]: "bitlen x = 
     (if x = 0  then 0 
 else if x = -1 then 1 
                else (1 + (bitlen (x div 2))))"
  by (cases "x = 0 \<or> x = -1 \<or> 0 < x") auto

definition lapprox_posrat :: "nat \<Rightarrow> int \<Rightarrow> int \<Rightarrow> float"
where
  "lapprox_posrat prec x y = 
   (let 
       l = nat (int prec + bitlen y - bitlen x) ;
       d = (x * 2^l) div y
    in normfloat (Float d (- (int l))))"

lemma pow2_minus: "pow2 (-x) = inverse (pow2 x)"
  unfolding pow2_neg[of "-x"] by auto

lemma lapprox_posrat: 
  assumes x: "0 \<le> x"
  and y: "0 < y"
  shows "real (lapprox_posrat prec x y) \<le> real x / real y"
proof -
  let ?l = "nat (int prec + bitlen y - bitlen x)"
  
  have "real (x * 2^?l div y) * inverse (2^?l) \<le> (real (x * 2^?l) / real y) * inverse (2^?l)" 
    by (rule mult_right_mono, fact real_of_int_div4, simp)
  also have "\<dots> \<le> (real x / real y) * 2^?l * inverse (2^?l)" by auto
  finally have "real (x * 2^?l div y) * inverse (2^?l) \<le> real x / real y" unfolding mult_assoc by auto
  thus ?thesis unfolding lapprox_posrat_def Let_def normfloat real_of_float_simp
    unfolding pow2_minus pow2_int minus_minus .
qed

lemma real_of_int_div_mult: 
  fixes x y c :: int assumes "0 < y" and "0 < c"
  shows "real (x div y) \<le> real (x * c div y) * inverse (real c)"
proof -
  have "c * (x div y) + 0 \<le> c * x div y" unfolding zdiv_zmult1_eq[of c x y]
    by (rule add_left_mono, 
        auto intro!: mult_nonneg_nonneg 
             simp add: pos_imp_zdiv_nonneg_iff[OF `0 < y`] `0 < c`[THEN less_imp_le] pos_mod_sign[OF `0 < y`])
  hence "real (x div y) * real c \<le> real (x * c div y)" 
    unfolding real_of_int_mult[symmetric] real_of_int_le_iff mult_commute by auto
  hence "real (x div y) * real c * inverse (real c) \<le> real (x * c div y) * inverse (real c)"
    using `0 < c` by auto
  thus ?thesis unfolding mult_assoc using `0 < c` by auto
qed

lemma lapprox_posrat_bottom: assumes "0 < y"
  shows "real (x div y) \<le> real (lapprox_posrat n x y)" 
proof -
  have pow: "\<And>x. (0::int) < 2^x" by auto
  show ?thesis
    unfolding lapprox_posrat_def Let_def real_of_float_add normfloat real_of_float_simp pow2_minus pow2_int
    using real_of_int_div_mult[OF `0 < y` pow] by auto
qed

lemma lapprox_posrat_nonneg: assumes "0 \<le> x" and "0 < y"
  shows "0 \<le> real (lapprox_posrat n x y)" 
proof -
  show ?thesis
    unfolding lapprox_posrat_def Let_def real_of_float_add normfloat real_of_float_simp pow2_minus pow2_int
    using pos_imp_zdiv_nonneg_iff[OF `0 < y`] assms by (auto intro!: mult_nonneg_nonneg)
qed

definition rapprox_posrat :: "nat \<Rightarrow> int \<Rightarrow> int \<Rightarrow> float"
where
  "rapprox_posrat prec x y = (let
     l = nat (int prec + bitlen y - bitlen x) ;
     X = x * 2^l ;
     d = X div y ;
     m = X mod y
   in normfloat (Float (d + (if m = 0 then 0 else 1)) (- (int l))))"

lemma rapprox_posrat:
  assumes x: "0 \<le> x"
  and y: "0 < y"
  shows "real x / real y \<le> real (rapprox_posrat prec x y)"
proof -
  let ?l = "nat (int prec + bitlen y - bitlen x)" let ?X = "x * 2^?l"
  show ?thesis 
  proof (cases "?X mod y = 0")
    case True hence "y dvd ?X" using `0 < y` by auto
    from real_of_int_div[OF this]
    have "real (?X div y) * inverse (2 ^ ?l) = real ?X / real y * inverse (2 ^ ?l)" by auto
    also have "\<dots> = real x / real y * (2^?l * inverse (2^?l))" by auto
    finally have "real (?X div y) * inverse (2^?l) = real x / real y" by auto
    thus ?thesis unfolding rapprox_posrat_def Let_def normfloat if_P[OF True] 
      unfolding real_of_float_simp pow2_minus pow2_int minus_minus by auto
  next
    case False
    have "0 \<le> real y" and "real y \<noteq> 0" using `0 < y` by auto
    have "0 \<le> real y * 2^?l" by (rule mult_nonneg_nonneg, rule `0 \<le> real y`, auto)

    have "?X = y * (?X div y) + ?X mod y" by auto
    also have "\<dots> \<le> y * (?X div y) + y" by (rule add_mono, auto simp add: pos_mod_bound[OF `0 < y`, THEN less_imp_le])
    also have "\<dots> = y * (?X div y + 1)" unfolding right_distrib by auto
    finally have "real ?X \<le> real y * real (?X div y + 1)" unfolding real_of_int_le_iff real_of_int_mult[symmetric] .
    hence "real ?X / (real y * 2^?l) \<le> real y * real (?X div y + 1) / (real y * 2^?l)" 
      by (rule divide_right_mono, simp only: `0 \<le> real y * 2^?l`)
    also have "\<dots> = real y * real (?X div y + 1) / real y / 2^?l" by auto
    also have "\<dots> = real (?X div y + 1) * inverse (2^?l)" unfolding nonzero_mult_divide_cancel_left[OF `real y \<noteq> 0`] 
      unfolding divide_inverse ..
    finally show ?thesis unfolding rapprox_posrat_def Let_def normfloat real_of_float_simp if_not_P[OF False]
      unfolding pow2_minus pow2_int minus_minus by auto
  qed
qed

lemma rapprox_posrat_le1: assumes "0 \<le> x" and "0 < y" and "x \<le> y"
  shows "real (rapprox_posrat n x y) \<le> 1"
proof -
  let ?l = "nat (int n + bitlen y - bitlen x)" let ?X = "x * 2^?l"
  show ?thesis
  proof (cases "?X mod y = 0")
    case True hence "y dvd ?X" using `0 < y` by auto
    from real_of_int_div[OF this]
    have "real (?X div y) * inverse (2 ^ ?l) = real ?X / real y * inverse (2 ^ ?l)" by auto
    also have "\<dots> = real x / real y * (2^?l * inverse (2^?l))" by auto
    finally have "real (?X div y) * inverse (2^?l) = real x / real y" by auto
    also have "real x / real y \<le> 1" using `0 \<le> x` and `0 < y` and `x \<le> y` by auto
    finally show ?thesis unfolding rapprox_posrat_def Let_def normfloat if_P[OF True]
      unfolding real_of_float_simp pow2_minus pow2_int minus_minus by auto
  next
    case False
    have "x \<noteq> y"
    proof (rule ccontr)
      assume "\<not> x \<noteq> y" hence "x = y" by auto
      have "?X mod y = 0" unfolding `x = y` using mod_mult_self1_is_0 by auto
      thus False using False by auto
    qed
    hence "x < y" using `x \<le> y` by auto
    hence "real x / real y < 1" using `0 < y` and `0 \<le> x` by auto

    from real_of_int_div4[of "?X" y]
    have "real (?X div y) \<le> (real x / real y) * 2^?l" unfolding real_of_int_mult times_divide_eq_left real_of_int_power real_numeral .
    also have "\<dots> < 1 * 2^?l" using `real x / real y < 1` by (rule mult_strict_right_mono, auto)
    finally have "?X div y < 2^?l" unfolding real_of_int_less_iff[of _ "2^?l", symmetric] by auto
    hence "?X div y + 1 \<le> 2^?l" by auto
    hence "real (?X div y + 1) * inverse (2^?l) \<le> 2^?l * inverse (2^?l)"
      unfolding real_of_int_le_iff[of _ "2^?l", symmetric] real_of_int_power real_numeral
      by (rule mult_right_mono, auto)
    hence "real (?X div y + 1) * inverse (2^?l) \<le> 1" by auto
    thus ?thesis unfolding rapprox_posrat_def Let_def normfloat real_of_float_simp if_not_P[OF False]
      unfolding pow2_minus pow2_int minus_minus by auto
  qed
qed

lemma zdiv_greater_zero: fixes a b :: int assumes "0 < a" and "a \<le> b"
  shows "0 < b div a"
proof (rule ccontr)
  have "0 \<le> b" using assms by auto
  assume "\<not> 0 < b div a" hence "b div a = 0" using `0 \<le> b`[unfolded pos_imp_zdiv_nonneg_iff[OF `0<a`, of b, symmetric]] by auto
  have "b = a * (b div a) + b mod a" by auto
  hence "b = b mod a" unfolding `b div a = 0` by auto
  hence "b < a" using `0 < a`[THEN pos_mod_bound, of b] by auto
  thus False using `a \<le> b` by auto
qed

lemma rapprox_posrat_less1: assumes "0 \<le> x" and "0 < y" and "2 * x < y" and "0 < n"
  shows "real (rapprox_posrat n x y) < 1"
proof (cases "x = 0")
  case True thus ?thesis unfolding rapprox_posrat_def True Let_def normfloat real_of_float_simp by auto
next
  case False hence "0 < x" using `0 \<le> x` by auto
  hence "x < y" using assms by auto
  
  let ?l = "nat (int n + bitlen y - bitlen x)" let ?X = "x * 2^?l"
  show ?thesis
  proof (cases "?X mod y = 0")
    case True hence "y dvd ?X" using `0 < y` by auto
    from real_of_int_div[OF this]
    have "real (?X div y) * inverse (2 ^ ?l) = real ?X / real y * inverse (2 ^ ?l)" by auto
    also have "\<dots> = real x / real y * (2^?l * inverse (2^?l))" by auto
    finally have "real (?X div y) * inverse (2^?l) = real x / real y" by auto
    also have "real x / real y < 1" using `0 \<le> x` and `0 < y` and `x < y` by auto
    finally show ?thesis unfolding rapprox_posrat_def Let_def normfloat real_of_float_simp if_P[OF True]
      unfolding pow2_minus pow2_int minus_minus by auto
  next
    case False
    hence "(real x / real y) < 1 / 2" using `0 < y` and `0 \<le> x` `2 * x < y` by auto

    have "0 < ?X div y"
    proof -
      have "2^nat (bitlen x - 1) \<le> y" and "y < 2^nat (bitlen y)"
        using bitlen_bounds[OF `0 < x`, THEN conjunct1] bitlen_bounds[OF `0 < y`, THEN conjunct2] `x < y` by auto
      hence "(2::int)^nat (bitlen x - 1) < 2^nat (bitlen y)" by (rule order_le_less_trans)
      hence "bitlen x \<le> bitlen y" by auto
      hence len_less: "nat (bitlen x - 1) \<le> nat (int (n - 1) + bitlen y)" by auto

      have "x \<noteq> 0" and "y \<noteq> 0" using `0 < x` `0 < y` by auto

      have exp_eq: "nat (int (n - 1) + bitlen y) - nat (bitlen x - 1) = ?l"
        using `bitlen x \<le> bitlen y` bitlen_ge1[OF `x \<noteq> 0`] bitlen_ge1[OF `y \<noteq> 0`] `0 < n` by auto

      have "y * 2^nat (bitlen x - 1) \<le> y * x" 
        using bitlen_bounds[OF `0 < x`, THEN conjunct1] `0 < y`[THEN less_imp_le] by (rule mult_left_mono)
      also have "\<dots> \<le> 2^nat (bitlen y) * x" using bitlen_bounds[OF `0 < y`, THEN conjunct2, THEN less_imp_le] `0 \<le> x` by (rule mult_right_mono)
      also have "\<dots> \<le> x * 2^nat (int (n - 1) + bitlen y)" unfolding mult_commute[of x] by (rule mult_right_mono, auto simp add: `0 \<le> x`)
      finally have "real y * 2^nat (bitlen x - 1) * inverse (2^nat (bitlen x - 1)) \<le> real x * 2^nat (int (n - 1) + bitlen y) * inverse (2^nat (bitlen x - 1))"
        unfolding real_of_int_le_iff[symmetric] by auto
      hence "real y \<le> real x * (2^nat (int (n - 1) + bitlen y) / (2^nat (bitlen x - 1)))" 
        unfolding mult_assoc divide_inverse by auto
      also have "\<dots> = real x * (2^(nat (int (n - 1) + bitlen y) - nat (bitlen x - 1)))" using power_diff[of "2::real", OF _ len_less] by auto
      finally have "y \<le> x * 2^?l" unfolding exp_eq unfolding real_of_int_le_iff[symmetric] by auto
      thus ?thesis using zdiv_greater_zero[OF `0 < y`] by auto
    qed

    from real_of_int_div4[of "?X" y]
    have "real (?X div y) \<le> (real x / real y) * 2^?l" unfolding real_of_int_mult times_divide_eq_left real_of_int_power real_numeral .
    also have "\<dots> < 1/2 * 2^?l" using `real x / real y < 1/2` by (rule mult_strict_right_mono, auto)
    finally have "?X div y * 2 < 2^?l" unfolding real_of_int_less_iff[of _ "2^?l", symmetric] by auto
    hence "?X div y + 1 < 2^?l" using `0 < ?X div y` by auto
    hence "real (?X div y + 1) * inverse (2^?l) < 2^?l * inverse (2^?l)"
      unfolding real_of_int_less_iff[of _ "2^?l", symmetric] real_of_int_power real_numeral
      by (rule mult_strict_right_mono, auto)
    hence "real (?X div y + 1) * inverse (2^?l) < 1" by auto
    thus ?thesis unfolding rapprox_posrat_def Let_def normfloat real_of_float_simp if_not_P[OF False]
      unfolding pow2_minus pow2_int minus_minus by auto
  qed
qed

lemma approx_rat_pattern: fixes P and ps :: "nat * int * int"
  assumes Y: "\<And>y prec x. \<lbrakk>y = 0; ps = (prec, x, 0)\<rbrakk> \<Longrightarrow> P" 
  and A: "\<And>x y prec. \<lbrakk>0 \<le> x; 0 < y; ps = (prec, x, y)\<rbrakk> \<Longrightarrow> P"
  and B: "\<And>x y prec. \<lbrakk>x < 0; 0 < y; ps = (prec, x, y)\<rbrakk> \<Longrightarrow> P"
  and C: "\<And>x y prec. \<lbrakk>x < 0; y < 0; ps = (prec, x, y)\<rbrakk> \<Longrightarrow> P"
  and D: "\<And>x y prec. \<lbrakk>0 \<le> x; y < 0; ps = (prec, x, y)\<rbrakk> \<Longrightarrow> P"
  shows P
proof -
  obtain prec x y where [simp]: "ps = (prec, x, y)" by (cases ps) auto
  from Y have "y = 0 \<Longrightarrow> P" by auto
  moreover {
    assume "0 < y"
    have P
    proof (cases "0 \<le> x")
      case True
      with A and `0 < y` show P by auto
    next
      case False
      with B and `0 < y` show P by auto
    qed
  } 
  moreover {
    assume "y < 0"
    have P
    proof (cases "0 \<le> x")
      case True
      with D and `y < 0` show P by auto
    next
      case False
      with C and `y < 0` show P by auto
    qed
  }
  ultimately show P by (cases "y = 0 \<or> 0 < y \<or> y < 0") auto
qed

function lapprox_rat :: "nat \<Rightarrow> int \<Rightarrow> int \<Rightarrow> float"
where
  "y = 0 \<Longrightarrow> lapprox_rat prec x y = 0"
| "0 \<le> x \<Longrightarrow> 0 < y \<Longrightarrow> lapprox_rat prec x y = lapprox_posrat prec x y"
| "x < 0 \<Longrightarrow> 0 < y \<Longrightarrow> lapprox_rat prec x y = - (rapprox_posrat prec (-x) y)"
| "x < 0 \<Longrightarrow> y < 0 \<Longrightarrow> lapprox_rat prec x y = lapprox_posrat prec (-x) (-y)"
| "0 \<le> x \<Longrightarrow> y < 0 \<Longrightarrow> lapprox_rat prec x y = - (rapprox_posrat prec x (-y))"
apply simp_all by (rule approx_rat_pattern)
termination by lexicographic_order

lemma compute_lapprox_rat[code]:
      "lapprox_rat prec x y = (if y = 0 then 0 else if 0 \<le> x then (if 0 < y then lapprox_posrat prec x y else - (rapprox_posrat prec x (-y))) 
                                                             else (if 0 < y then - (rapprox_posrat prec (-x) y) else lapprox_posrat prec (-x) (-y)))"
  by auto
            
lemma lapprox_rat: "real (lapprox_rat prec x y) \<le> real x / real y"
proof -      
  have h[rule_format]: "! a b b'. b' \<le> b \<longrightarrow> a \<le> b' \<longrightarrow> a \<le> (b::real)" by auto
  show ?thesis
    apply (case_tac "y = 0")
    apply simp
    apply (case_tac "0 \<le> x \<and> 0 < y")
    apply (simp add: lapprox_posrat)
    apply (case_tac "x < 0 \<and> 0 < y")
    apply simp
    apply (subst minus_le_iff)   
    apply (rule h[OF rapprox_posrat])
    apply (simp_all)
    apply (case_tac "x < 0 \<and> y < 0")
    apply simp
    apply (rule h[OF _ lapprox_posrat])
    apply (simp_all)
    apply (case_tac "0 \<le> x \<and> y < 0")
    apply (simp)
    apply (subst minus_le_iff)   
    apply (rule h[OF rapprox_posrat])
    apply simp_all
    apply arith
    done
qed

lemma lapprox_rat_bottom: assumes "0 \<le> x" and "0 < y"
  shows "real (x div y) \<le> real (lapprox_rat n x y)" 
  unfolding lapprox_rat.simps(2)[OF assms]  using lapprox_posrat_bottom[OF `0<y`] .

function rapprox_rat :: "nat \<Rightarrow> int \<Rightarrow> int \<Rightarrow> float"
where
  "y = 0 \<Longrightarrow> rapprox_rat prec x y = 0"
| "0 \<le> x \<Longrightarrow> 0 < y \<Longrightarrow> rapprox_rat prec x y = rapprox_posrat prec x y"
| "x < 0 \<Longrightarrow> 0 < y \<Longrightarrow> rapprox_rat prec x y = - (lapprox_posrat prec (-x) y)"
| "x < 0 \<Longrightarrow> y < 0 \<Longrightarrow> rapprox_rat prec x y = rapprox_posrat prec (-x) (-y)"
| "0 \<le> x \<Longrightarrow> y < 0 \<Longrightarrow> rapprox_rat prec x y = - (lapprox_posrat prec x (-y))"
apply simp_all by (rule approx_rat_pattern)
termination by lexicographic_order

lemma compute_rapprox_rat[code]:
      "rapprox_rat prec x y = (if y = 0 then 0 else if 0 \<le> x then (if 0 < y then rapprox_posrat prec x y else - (lapprox_posrat prec x (-y))) else 
                                                                  (if 0 < y then - (lapprox_posrat prec (-x) y) else rapprox_posrat prec (-x) (-y)))"
  by auto

lemma rapprox_rat: "real x / real y \<le> real (rapprox_rat prec x y)"
proof -      
  have h[rule_format]: "! a b b'. b' \<le> b \<longrightarrow> a \<le> b' \<longrightarrow> a \<le> (b::real)" by auto
  show ?thesis
    apply (case_tac "y = 0")
    apply simp
    apply (case_tac "0 \<le> x \<and> 0 < y")
    apply (simp add: rapprox_posrat)
    apply (case_tac "x < 0 \<and> 0 < y")
    apply simp
    apply (subst le_minus_iff)   
    apply (rule h[OF _ lapprox_posrat])
    apply (simp_all)
    apply (case_tac "x < 0 \<and> y < 0")
    apply simp
    apply (rule h[OF rapprox_posrat])
    apply (simp_all)
    apply (case_tac "0 \<le> x \<and> y < 0")
    apply (simp)
    apply (subst le_minus_iff)   
    apply (rule h[OF _ lapprox_posrat])
    apply simp_all
    apply arith
    done
qed

lemma rapprox_rat_le1: assumes "0 \<le> x" and "0 < y" and "x \<le> y"
  shows "real (rapprox_rat n x y) \<le> 1"
  unfolding rapprox_rat.simps(2)[OF `0 \<le> x` `0 < y`] using rapprox_posrat_le1[OF assms] .

lemma rapprox_rat_neg: assumes "x < 0" and "0 < y"
  shows "real (rapprox_rat n x y) \<le> 0"
  unfolding rapprox_rat.simps(3)[OF assms] using lapprox_posrat_nonneg[of "-x" y n] assms by auto

lemma rapprox_rat_nonneg_neg: assumes "0 \<le> x" and "y < 0"
  shows "real (rapprox_rat n x y) \<le> 0"
  unfolding rapprox_rat.simps(5)[OF assms] using lapprox_posrat_nonneg[of x "-y" n] assms by auto

lemma rapprox_rat_nonpos_pos: assumes "x \<le> 0" and "0 < y"
  shows "real (rapprox_rat n x y) \<le> 0"
proof (cases "x = 0") 
  case True
  hence "0 \<le> x" by auto show ?thesis
    unfolding rapprox_rat.simps(2)[OF `0 \<le> x` `0 < y`]
    unfolding True rapprox_posrat_def Let_def
    by auto
next
  case False
  hence "x < 0" using assms by auto
  show ?thesis using rapprox_rat_neg[OF `x < 0` `0 < y`] .
qed

fun float_divl :: "nat \<Rightarrow> float \<Rightarrow> float \<Rightarrow> float"
where
  "float_divl prec (Float m1 s1) (Float m2 s2) = 
    (let
       l = lapprox_rat prec m1 m2;
       f = Float 1 (s1 - s2)
     in
       f * l)"     

lemma float_divl: "real (float_divl prec x y) \<le> real x / real y"
  using lapprox_rat[of prec "mantissa x" "mantissa y"]
  by (cases x y rule: float.exhaust[case_product float.exhaust])
     (simp split: split_if_asm
           add: real_of_float_simp pow2_diff field_simps le_divide_eq mult_less_0_iff zero_less_mult_iff)

lemma float_divl_lower_bound: assumes "0 \<le> x" and "0 < y" shows "0 \<le> float_divl prec x y"
proof (cases x, cases y)
  fix xm xe ym ye :: int
  assume x_eq: "x = Float xm xe" and y_eq: "y = Float ym ye"
  have "0 \<le> xm"
    using `0 \<le> x`[unfolded x_eq le_float_def real_of_float_simp real_of_float_0 zero_le_mult_iff]
    by auto
  have "0 < ym"
    using `0 < y`[unfolded y_eq less_float_def real_of_float_simp real_of_float_0 zero_less_mult_iff]
    by auto

  have "\<And>n. 0 \<le> real (Float 1 n)"
    unfolding real_of_float_simp using zero_le_pow2 by auto
  moreover have "0 \<le> real (lapprox_rat prec xm ym)"
    apply (rule order_trans[OF _ lapprox_rat_bottom[OF `0 \<le> xm` `0 < ym`]])
    apply (auto simp add: `0 \<le> xm` pos_imp_zdiv_nonneg_iff[OF `0 < ym`])
    done
  ultimately show "0 \<le> float_divl prec x y"
    unfolding x_eq y_eq float_divl.simps Let_def le_float_def real_of_float_0
    by (auto intro!: mult_nonneg_nonneg)
qed

lemma float_divl_pos_less1_bound:
  assumes "0 < x" and "x < 1" and "0 < prec"
  shows "1 \<le> float_divl prec 1 x"
proof (cases x)
  case (Float m e)
  from `0 < x` `x < 1` have "0 < m" "e < 0"
    using float_pos_m_pos float_pos_less1_e_neg unfolding Float by auto
  let ?b = "nat (bitlen m)" and ?e = "nat (-e)"
  have "1 \<le> m" and "m \<noteq> 0" using `0 < m` by auto
  with bitlen_bounds[OF `0 < m`] have "m < 2^?b" and "(2::int) \<le> 2^?b" by auto
  hence "1 \<le> bitlen m" using power_le_imp_le_exp[of "2::int" 1 ?b] by auto
  hence pow_split: "nat (int prec + bitlen m - 1) = (prec - 1) + ?b" using `0 < prec` by auto
  
  have pow_not0: "\<And>x. (2::real)^x \<noteq> 0" by auto

  from float_less1_mantissa_bound `0 < x` `x < 1` Float 
  have "m < 2^?e" by auto
  with bitlen_bounds[OF `0 < m`, THEN conjunct1] have "(2::int)^nat (bitlen m - 1) < 2^?e"
    by (rule order_le_less_trans)
  from power_less_imp_less_exp[OF _ this]
  have "bitlen m \<le> - e" by auto
  hence "(2::real)^?b \<le> 2^?e" by auto
  hence "(2::real)^?b * inverse (2^?b) \<le> 2^?e * inverse (2^?b)"
    by (rule mult_right_mono) auto
  hence "(1::real) \<le> 2^?e * inverse (2^?b)" by auto
  also
  let ?d = "real (2 ^ nat (int prec + bitlen m - 1) div m) * inverse (2 ^ nat (int prec + bitlen m - 1))"
  {
    have "2^(prec - 1) * m \<le> 2^(prec - 1) * 2^?b"
      using `m < 2^?b`[THEN less_imp_le] by (rule mult_left_mono) auto
    also have "\<dots> = 2 ^ nat (int prec + bitlen m - 1)"
      unfolding pow_split power_add by auto
    finally have "2^(prec - 1) * m div m \<le> 2 ^ nat (int prec + bitlen m - 1) div m"
      using `0 < m` by (rule zdiv_mono1)
    hence "2^(prec - 1) \<le> 2 ^ nat (int prec + bitlen m - 1) div m"
      unfolding div_mult_self2_is_id[OF `m \<noteq> 0`] .
    hence "2^(prec - 1) * inverse (2 ^ nat (int prec + bitlen m - 1)) \<le> ?d"
      unfolding real_of_int_le_iff[of "2^(prec - 1)", symmetric] by auto
  }
  from mult_left_mono[OF this [unfolded pow_split power_add inverse_mult_distrib mult_assoc[symmetric] right_inverse[OF pow_not0] mult_1_left], of "2^?e"]
  have "2^?e * inverse (2^?b) \<le> 2^?e * ?d" unfolding pow_split power_add by auto
  finally have "1 \<le> 2^?e * ?d" .
  
  have e_nat: "0 - e = int (nat (-e))" using `e < 0` by auto
  have "bitlen 1 = 1" using bitlen.simps by auto
  
  show ?thesis 
    unfolding one_float_def Float float_divl.simps Let_def
      lapprox_rat.simps(2)[OF zero_le_one `0 < m`]
      lapprox_posrat_def `bitlen 1 = 1`
    unfolding le_float_def real_of_float_mult normfloat real_of_float_simp
      pow2_minus pow2_int e_nat
    using `1 \<le> 2^?e * ?d` by (auto simp add: pow2_def)
qed

fun float_divr :: "nat \<Rightarrow> float \<Rightarrow> float \<Rightarrow> float"
where
  "float_divr prec (Float m1 s1) (Float m2 s2) = 
    (let
       r = rapprox_rat prec m1 m2;
       f = Float 1 (s1 - s2)
     in
       f * r)"  

lemma float_divr: "real x / real y \<le> real (float_divr prec x y)"
  using rapprox_rat[of "mantissa x" "mantissa y" prec]
  by (cases x y rule: float.exhaust[case_product float.exhaust])
     (simp split: split_if_asm
           add: real_of_float_simp pow2_diff field_simps divide_le_eq mult_less_0_iff zero_less_mult_iff)

lemma float_divr_pos_less1_lower_bound: assumes "0 < x" and "x < 1" shows "1 \<le> float_divr prec 1 x"
proof -
  have "1 \<le> 1 / real x" using `0 < x` and `x < 1` unfolding less_float_def by auto
  also have "\<dots> \<le> real (float_divr prec 1 x)" using float_divr[where x=1 and y=x] by auto
  finally show ?thesis unfolding le_float_def by auto
qed

lemma float_divr_nonpos_pos_upper_bound: assumes "x \<le> 0" and "0 < y" shows "float_divr prec x y \<le> 0"
proof (cases x, cases y)
  fix xm xe ym ye :: int
  assume x_eq: "x = Float xm xe" and y_eq: "y = Float ym ye"
  have "xm \<le> 0" using `x \<le> 0`[unfolded x_eq le_float_def real_of_float_simp real_of_float_0 mult_le_0_iff] by auto
  have "0 < ym" using `0 < y`[unfolded y_eq less_float_def real_of_float_simp real_of_float_0 zero_less_mult_iff] by auto

  have "\<And>n. 0 \<le> real (Float 1 n)" unfolding real_of_float_simp using zero_le_pow2 by auto
  moreover have "real (rapprox_rat prec xm ym) \<le> 0" using rapprox_rat_nonpos_pos[OF `xm \<le> 0` `0 < ym`] .
  ultimately show "float_divr prec x y \<le> 0"
    unfolding x_eq y_eq float_divr.simps Let_def le_float_def real_of_float_0 real_of_float_mult by (auto intro!: mult_nonneg_nonpos)
qed

lemma float_divr_nonneg_neg_upper_bound: assumes "0 \<le> x" and "y < 0" shows "float_divr prec x y \<le> 0"
proof (cases x, cases y)
  fix xm xe ym ye :: int
  assume x_eq: "x = Float xm xe" and y_eq: "y = Float ym ye"
  have "0 \<le> xm" using `0 \<le> x`[unfolded x_eq le_float_def real_of_float_simp real_of_float_0 zero_le_mult_iff] by auto
  have "ym < 0" using `y < 0`[unfolded y_eq less_float_def real_of_float_simp real_of_float_0 mult_less_0_iff] by auto
  hence "0 < - ym" by auto

  have "\<And>n. 0 \<le> real (Float 1 n)" unfolding real_of_float_simp using zero_le_pow2 by auto
  moreover have "real (rapprox_rat prec xm ym) \<le> 0" using rapprox_rat_nonneg_neg[OF `0 \<le> xm` `ym < 0`] .
  ultimately show "float_divr prec x y \<le> 0"
    unfolding x_eq y_eq float_divr.simps Let_def le_float_def real_of_float_0 real_of_float_mult by (auto intro!: mult_nonneg_nonpos)
qed

primrec round_down :: "nat \<Rightarrow> float \<Rightarrow> float" where
"round_down prec (Float m e) = (let d = bitlen m - int prec in
     if 0 < d then let P = 2^nat d ; n = m div P in Float n (e + d)
              else Float m e)"

primrec round_up :: "nat \<Rightarrow> float \<Rightarrow> float" where
"round_up prec (Float m e) = (let d = bitlen m - int prec in
  if 0 < d then let P = 2^nat d ; n = m div P ; r = m mod P in Float (n + (if r = 0 then 0 else 1)) (e + d) 
           else Float m e)"

lemma round_up: "real x \<le> real (round_up prec x)"
proof (cases x)
  case (Float m e)
  let ?d = "bitlen m - int prec"
  let ?p = "(2::int)^nat ?d"
  have "0 < ?p" by auto
  show "?thesis"
  proof (cases "0 < ?d")
    case True
    hence pow_d: "pow2 ?d = real ?p" using pow2_int[symmetric] by simp
    show ?thesis
    proof (cases "m mod ?p = 0")
      case True
      have m: "m = m div ?p * ?p + 0" unfolding True[symmetric] using mod_div_equality [symmetric] .
      have "real (Float m e) = real (Float (m div ?p) (e + ?d))" unfolding real_of_float_simp arg_cong[OF m, of real]
        by (auto simp add: pow2_add `0 < ?d` pow_d)
      thus ?thesis
        unfolding Float round_up.simps Let_def if_P[OF `m mod ?p = 0`] if_P[OF `0 < ?d`]
        by auto
    next
      case False
      have "m = m div ?p * ?p + m mod ?p" unfolding mod_div_equality ..
      also have "\<dots> \<le> (m div ?p + 1) * ?p" unfolding left_distrib mult_1 by (rule add_left_mono, rule pos_mod_bound[OF `0 < ?p`, THEN less_imp_le])
      finally have "real (Float m e) \<le> real (Float (m div ?p + 1) (e + ?d))" unfolding real_of_float_simp add_commute[of e]
        unfolding pow2_add mult_assoc[symmetric] real_of_int_le_iff[of m, symmetric]
        by (auto intro!: mult_mono simp add: pow2_add `0 < ?d` pow_d)
      thus ?thesis
        unfolding Float round_up.simps Let_def if_not_P[OF `\<not> m mod ?p = 0`] if_P[OF `0 < ?d`] .
    qed
  next
    case False
    show ?thesis
      unfolding Float round_up.simps Let_def if_not_P[OF False] .. 
  qed
qed

lemma round_down: "real (round_down prec x) \<le> real x"
proof (cases x)
  case (Float m e)
  let ?d = "bitlen m - int prec"
  let ?p = "(2::int)^nat ?d"
  have "0 < ?p" by auto
  show "?thesis"
  proof (cases "0 < ?d")
    case True
    hence pow_d: "pow2 ?d = real ?p" using pow2_int[symmetric] by simp
    have "m div ?p * ?p \<le> m div ?p * ?p + m mod ?p" by (auto simp add: pos_mod_bound[OF `0 < ?p`, THEN less_imp_le])
    also have "\<dots> \<le> m" unfolding mod_div_equality ..
    finally have "real (Float (m div ?p) (e + ?d)) \<le> real (Float m e)" unfolding real_of_float_simp add_commute[of e]
      unfolding pow2_add mult_assoc[symmetric] real_of_int_le_iff[of _ m, symmetric]
      by (auto intro!: mult_mono simp add: pow2_add `0 < ?d` pow_d)
    thus ?thesis
      unfolding Float round_down.simps Let_def if_P[OF `0 < ?d`] .
  next
    case False
    show ?thesis
      unfolding Float round_down.simps Let_def if_not_P[OF False] .. 
  qed
qed

definition lb_mult :: "nat \<Rightarrow> float \<Rightarrow> float \<Rightarrow> float" where
  "lb_mult prec x y =
    (case normfloat (x * y) of Float m e \<Rightarrow>
      let
        l = bitlen m - int prec
      in if l > 0 then Float (m div (2^nat l)) (e + l)
                  else Float m e)"

definition ub_mult :: "nat \<Rightarrow> float \<Rightarrow> float \<Rightarrow> float" where
  "ub_mult prec x y =
    (case normfloat (x * y) of Float m e \<Rightarrow>
      let
        l = bitlen m - int prec
      in if l > 0 then Float (m div (2^nat l) + 1) (e + l)
                  else Float m e)"

lemma lb_mult: "real (lb_mult prec x y) \<le> real (x * y)"
proof (cases "normfloat (x * y)")
  case (Float m e)
  hence "odd m \<or> (m = 0 \<and> e = 0)" by (rule normfloat_imp_odd_or_zero)
  let ?l = "bitlen m - int prec"
  have "real (lb_mult prec x y) \<le> real (normfloat (x * y))"
  proof (cases "?l > 0")
    case False thus ?thesis unfolding lb_mult_def Float Let_def float.cases by auto
  next
    case True
    have "real (m div 2^(nat ?l)) * pow2 ?l \<le> real m"
    proof -
      have "real (m div 2^(nat ?l)) * pow2 ?l = real (2^(nat ?l) * (m div 2^(nat ?l)))" unfolding real_of_int_mult real_of_int_power real_numeral unfolding pow2_int[symmetric] 
        using `?l > 0` by auto
      also have "\<dots> \<le> real (2^(nat ?l) * (m div 2^(nat ?l)) + m mod 2^(nat ?l))" unfolding real_of_int_add by auto
      also have "\<dots> = real m" unfolding zmod_zdiv_equality[symmetric] ..
      finally show ?thesis by auto
    qed
    thus ?thesis unfolding lb_mult_def Float Let_def float.cases if_P[OF True] real_of_float_simp pow2_add mult_commute mult_assoc by auto
  qed
  also have "\<dots> = real (x * y)" unfolding normfloat ..
  finally show ?thesis .
qed

lemma ub_mult: "real (x * y) \<le> real (ub_mult prec x y)"
proof (cases "normfloat (x * y)")
  case (Float m e)
  hence "odd m \<or> (m = 0 \<and> e = 0)" by (rule normfloat_imp_odd_or_zero)
  let ?l = "bitlen m - int prec"
  have "real (x * y) = real (normfloat (x * y))" unfolding normfloat ..
  also have "\<dots> \<le> real (ub_mult prec x y)"
  proof (cases "?l > 0")
    case False thus ?thesis unfolding ub_mult_def Float Let_def float.cases by auto
  next
    case True
    have "real m \<le> real (m div 2^(nat ?l) + 1) * pow2 ?l"
    proof -
      have "m mod 2^(nat ?l) < 2^(nat ?l)" by (rule pos_mod_bound) auto
      hence mod_uneq: "real (m mod 2^(nat ?l)) \<le> 1 * 2^(nat ?l)" unfolding mult_1 real_of_int_less_iff[symmetric] by auto
      
      have "real m = real (2^(nat ?l) * (m div 2^(nat ?l)) + m mod 2^(nat ?l))" unfolding zmod_zdiv_equality[symmetric] ..
      also have "\<dots> = real (m div 2^(nat ?l)) * 2^(nat ?l) + real (m mod 2^(nat ?l))" unfolding real_of_int_add by auto
      also have "\<dots> \<le> (real (m div 2^(nat ?l)) + 1) * 2^(nat ?l)" unfolding left_distrib using mod_uneq by auto
      finally show ?thesis unfolding pow2_int[symmetric] using True by auto
    qed
    thus ?thesis unfolding ub_mult_def Float Let_def float.cases if_P[OF True] real_of_float_simp pow2_add mult_commute mult_assoc by auto
  qed
  finally show ?thesis .
qed

primrec float_abs :: "float \<Rightarrow> float" where
  "float_abs (Float m e) = Float \<bar>m\<bar> e"

instantiation float :: abs
begin
definition abs_float_def: "\<bar>x\<bar> = float_abs x"
instance ..
end

lemma real_of_float_abs: "real \<bar>x :: float\<bar> = \<bar>real x\<bar>" 
proof (cases x)
  case (Float m e)
  have "\<bar>real m\<bar> * pow2 e = \<bar>real m * pow2 e\<bar>" unfolding abs_mult by auto
  thus ?thesis unfolding Float abs_float_def float_abs.simps real_of_float_simp by auto
qed

primrec floor_fl :: "float \<Rightarrow> float" where
  "floor_fl (Float m e) = (if 0 \<le> e then Float m e
                                  else Float (m div (2 ^ (nat (-e)))) 0)"

lemma floor_fl: "real (floor_fl x) \<le> real x"
proof (cases x)
  case (Float m e)
  show ?thesis
  proof (cases "0 \<le> e")
    case False
    hence me_eq: "pow2 (-e) = pow2 (int (nat (-e)))" by auto
    have "real (Float (m div (2 ^ (nat (-e)))) 0) = real (m div 2 ^ (nat (-e)))" unfolding real_of_float_simp by auto
    also have "\<dots> \<le> real m / real ((2::int) ^ (nat (-e)))" using real_of_int_div4 .
    also have "\<dots> = real m * inverse (2 ^ (nat (-e)))" unfolding real_of_int_power real_numeral divide_inverse ..
    also have "\<dots> = real (Float m e)" unfolding real_of_float_simp me_eq pow2_int pow2_neg[of e] ..
    finally show ?thesis unfolding Float floor_fl.simps if_not_P[OF `\<not> 0 \<le> e`] .
  next
    case True thus ?thesis unfolding Float by auto
  qed
qed

lemma floor_pos_exp: assumes floor: "Float m e = floor_fl x" shows "0 \<le> e"
proof (cases x)
  case (Float mx me)
  from floor[unfolded Float floor_fl.simps] show ?thesis by (cases "0 \<le> me", auto)
qed

declare floor_fl.simps[simp del]

primrec ceiling_fl :: "float \<Rightarrow> float" where
  "ceiling_fl (Float m e) = (if 0 \<le> e then Float m e
                                    else Float (m div (2 ^ (nat (-e))) + 1) 0)"

lemma ceiling_fl: "real x \<le> real (ceiling_fl x)"
proof (cases x)
  case (Float m e)
  show ?thesis
  proof (cases "0 \<le> e")
    case False
    hence me_eq: "pow2 (-e) = pow2 (int (nat (-e)))" by auto
    have "real (Float m e) = real m * inverse (2 ^ (nat (-e)))" unfolding real_of_float_simp me_eq pow2_int pow2_neg[of e] ..
    also have "\<dots> = real m / real ((2::int) ^ (nat (-e)))" unfolding real_of_int_power real_numeral divide_inverse ..
    also have "\<dots> \<le> 1 + real (m div 2 ^ (nat (-e)))" using real_of_int_div3[unfolded diff_le_eq] .
    also have "\<dots> = real (Float (m div (2 ^ (nat (-e))) + 1) 0)" unfolding real_of_float_simp by auto
    finally show ?thesis unfolding Float ceiling_fl.simps if_not_P[OF `\<not> 0 \<le> e`] .
  next
    case True thus ?thesis unfolding Float by auto
  qed
qed

declare ceiling_fl.simps[simp del]

definition lb_mod :: "nat \<Rightarrow> float \<Rightarrow> float \<Rightarrow> float \<Rightarrow> float" where
  "lb_mod prec x ub lb = x - ceiling_fl (float_divr prec x lb) * ub"

definition ub_mod :: "nat \<Rightarrow> float \<Rightarrow> float \<Rightarrow> float \<Rightarrow> float" where
  "ub_mod prec x ub lb = x - floor_fl (float_divl prec x ub) * lb"

lemma lb_mod: fixes k :: int assumes "0 \<le> real x" and "real k * y \<le> real x" (is "?k * y \<le> ?x")
  assumes "0 < real lb" "real lb \<le> y" (is "?lb \<le> y") "y \<le> real ub" (is "y \<le> ?ub")
  shows "real (lb_mod prec x ub lb) \<le> ?x - ?k * y"
proof -
  have "?lb \<le> ?ub" using assms by auto
  have "0 \<le> ?lb" and "?lb \<noteq> 0" using assms by auto
  have "?k * y \<le> ?x" using assms by auto
  also have "\<dots> \<le> ?x / ?lb * ?ub" by (metis mult_left_mono[OF `?lb \<le> ?ub` `0 \<le> ?x`] divide_right_mono[OF _ `0 \<le> ?lb` ] times_divide_eq_left nonzero_mult_divide_cancel_right[OF `?lb \<noteq> 0`])
  also have "\<dots> \<le> real (ceiling_fl (float_divr prec x lb)) * ?ub" by (metis mult_right_mono order_trans `0 \<le> ?lb` `?lb \<le> ?ub` float_divr ceiling_fl)
  finally show ?thesis unfolding lb_mod_def real_of_float_sub real_of_float_mult by auto
qed

lemma ub_mod:
  fixes k :: int and x :: float
  assumes "0 \<le> real x" and "real x \<le> real k * y" (is "?x \<le> ?k * y")
  assumes "0 < real lb" "real lb \<le> y" (is "?lb \<le> y") "y \<le> real ub" (is "y \<le> ?ub")
  shows "?x - ?k * y \<le> real (ub_mod prec x ub lb)"
proof -
  have "?lb \<le> ?ub" using assms by auto
  hence "0 \<le> ?lb" and "0 \<le> ?ub" and "?ub \<noteq> 0" using assms by auto
  have "real (floor_fl (float_divl prec x ub)) * ?lb \<le> ?x / ?ub * ?lb" by (metis mult_right_mono order_trans `0 \<le> ?lb` `?lb \<le> ?ub` float_divl floor_fl)
  also have "\<dots> \<le> ?x" by (metis mult_left_mono[OF `?lb \<le> ?ub` `0 \<le> ?x`] divide_right_mono[OF _ `0 \<le> ?ub` ] times_divide_eq_left nonzero_mult_divide_cancel_right[OF `?ub \<noteq> 0`])
  also have "\<dots> \<le> ?k * y" using assms by auto
  finally show ?thesis unfolding ub_mod_def real_of_float_sub real_of_float_mult by auto
qed

lemma le_float_def'[code]: "f \<le> g = (case f - g of Float a b \<Rightarrow> a \<le> 0)"
proof -
  have le_transfer: "(f \<le> g) = (real (f - g) \<le> 0)" by (auto simp add: le_float_def)
  from float_split[of "f - g"] obtain a b where f_diff_g: "f - g = Float a b" by auto
  with le_transfer have le_transfer': "f \<le> g = (real (Float a b) \<le> 0)" by simp
  show ?thesis by (simp add: le_transfer' f_diff_g float_le_zero)
qed

lemma less_float_def'[code]: "f < g = (case f - g of Float a b \<Rightarrow> a < 0)"
proof -
  have less_transfer: "(f < g) = (real (f - g) < 0)" by (auto simp add: less_float_def)
  from float_split[of "f - g"] obtain a b where f_diff_g: "f - g = Float a b" by auto
  with less_transfer have less_transfer': "f < g = (real (Float a b) < 0)" by simp
  show ?thesis by (simp add: less_transfer' f_diff_g float_less_zero)
qed

end
