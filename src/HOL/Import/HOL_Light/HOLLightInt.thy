(*  Title:      HOL/Import/HOL_Light/HOLLightInt.thy
    Author:     Cezary Kaliszyk
*)

header {* Compatibility theorems for HOL Light integers *}

theory HOLLightInt imports Main Real GCD begin

fun int_coprime where "int_coprime ((a :: int), (b :: int)) = coprime a b"

lemma DEF_int_coprime:
  "int_coprime = (\<lambda>u. \<exists>x y. ((fst u) * x) + ((snd u) * y) = int 1)"
  apply (auto simp add: fun_eq_iff)
  apply (metis bezout_int mult_commute)
  by (metis coprime_divisors_nat dvd_triv_left gcd_1_int gcd_add2_int)

lemma INT_FORALL_POS:
  "(\<forall>n. P (int n)) = (\<forall>i\<ge>(int 0). P i)"
  by (auto, drule_tac x="nat i" in spec) simp

lemma INT_LT_DISCRETE:
  "(x < y) = (x + int 1 \<le> y)"
  by auto

lemma INT_ABS_MUL_1:
  "(abs (x * y) = int 1) = (abs x = int 1 \<and> abs y = int 1)"
  by simp (metis dvd_mult_right zdvd1_eq abs_zmult_eq_1 abs_mult mult_1_right)

lemma dest_int_rep:
  "\<exists>(n :: nat). real (i :: int) = real n \<or> real i = - real n"
  by (metis (full_types) of_int_of_nat real_eq_of_int real_of_nat_def)

lemma DEF_int_add:
  "op + = (\<lambda>u ua. floor (real u + real ua))"
  by simp

lemma DEF_int_sub:
  "op - = (\<lambda>u ua. floor (real u - real ua))"
  by simp

lemma DEF_int_mul:
  "op * = (\<lambda>u ua. floor (real u * real ua))"
  by (metis floor_real_of_int real_of_int_mult)

lemma DEF_int_abs:
  "abs = (\<lambda>u. floor (abs (real u)))"
  by (metis floor_real_of_int real_of_int_abs)

lemma DEF_int_sgn:
  "sgn = (\<lambda>u. floor (sgn (real u)))"
  by (simp add: sgn_if fun_eq_iff)

lemma int_sgn_th:
  "real (sgn (x :: int)) = sgn (real x)"
  by (simp add: sgn_if)

lemma DEF_int_max:
  "max = (\<lambda>u ua. floor (max (real u) (real ua)))"
  by (metis floor_real_of_int real_of_int_le_iff sup_absorb1 sup_commute sup_max linorder_linear)

lemma int_max_th:
  "real (max (x :: int) y) = max (real x) (real y)"
  by (metis min_max.le_iff_sup min_max.sup_absorb1 real_of_int_le_iff linorder_linear)

lemma DEF_int_min:
  "min = (\<lambda>u ua. floor (min (real u) (real ua)))"
  by (metis floor_real_of_int inf_absorb1 inf_absorb2 inf_int_def inf_real_def real_of_int_le_iff linorder_linear)

lemma int_min_th:
  "real (min (x :: int) y) = min (real x) (real y)"
  by (metis inf_absorb1 inf_absorb2 inf_int_def inf_real_def real_of_int_le_iff linorder_linear)

lemma INT_IMAGE:
  "(\<exists>n. x = int n) \<or> (\<exists>n. x = - int n)"
  by (metis of_int_eq_id id_def of_int_of_nat)

lemma DEF_int_pow:
  "op ^ = (\<lambda>u ua. floor (real u ^ ua))"
  by (simp add: floor_power)

lemma DEF_int_divides:
  "op dvd = (\<lambda>(u :: int) ua. \<exists>x. ua = u * x)"
  by (metis dvdE dvdI)

lemma DEF_int_divides':
  "(a :: int) dvd b = (\<exists>x. b = a * x)"
  by (metis dvdE dvdI)

definition "int_mod (u :: int) ua ub = (u dvd (ua - ub))"

lemma int_mod_def':
  "int_mod = (\<lambda>u ua ub. (u dvd (ua - ub)))"
  by (simp add: int_mod_def [abs_def])

lemma int_congruent:
  "\<forall>x xa xb. int_mod xb x xa = (\<exists>d. x - xa = xb * d)"
  unfolding int_mod_def'
  by (auto simp add: DEF_int_divides')

lemma int_congruent':
  "\<forall>(x :: int) y n. (n dvd x - y) = (\<exists>d. x - y = n * d)"
  using int_congruent[unfolded int_mod_def] .

fun int_gcd where
  "int_gcd ((a :: int), (b :: int)) = gcd a b"

definition "hl_mod (k\<Colon>int) (l\<Colon>int) = (if 0 \<le> l then k mod l else k mod - l)"

lemma hl_mod_nonneg:
  "b \<noteq> 0 \<Longrightarrow> hl_mod a b \<ge> 0"
  by (simp add: hl_mod_def)

lemma hl_mod_lt_abs:
  "b \<noteq> 0 \<Longrightarrow> hl_mod a b < abs b"
  by (simp add: hl_mod_def)

definition "hl_div k l = (if 0 \<le> l then k div l else -(k div (-l)))"

lemma hl_mod_div:
  "n \<noteq> (0\<Colon>int) \<Longrightarrow> m = hl_div m n * n + hl_mod m n"
  unfolding hl_div_def hl_mod_def
  by auto (metis zmod_zdiv_equality mult_commute mult_minus_left)

lemma sth:
  "(\<forall>(x :: int) y z. x + (y + z) = x + y + z) \<and>
   (\<forall>(x :: int) y. x + y = y + x) \<and>
   (\<forall>(x :: int). int 0 + x = x) \<and>
   (\<forall>(x :: int) y z. x * (y * z) = x * y * z) \<and>
   (\<forall>(x :: int) y. x * y = y * x) \<and>
   (\<forall>(x :: int). int 1 * x = x) \<and>
   (\<forall>(x :: int). int 0 * x = int 0) \<and>
   (\<forall>(x :: int) y z. x * (y + z) = x * y + x * z) \<and>
   (\<forall>(x :: int). x ^ 0 = int 1) \<and> (\<forall>(x :: int) n. x ^ Suc n = x * x ^ n)"
  by (simp_all add: right_distrib)

lemma INT_DIVISION:
  "n ~= int 0 \<Longrightarrow> m = hl_div m n * n + hl_mod m n \<and> int 0 \<le> hl_mod m n \<and> hl_mod m n < abs n"
  by (auto simp add: hl_mod_nonneg hl_mod_lt_abs hl_mod_div)

lemma INT_DIVMOD_EXIST_0:
  "\<exists>q r. if n = int 0 then q = int 0 \<and> r = m
         else int 0 \<le> r \<and> r < abs n \<and> m = q * n + r"
  apply (rule_tac x="hl_div m n" in exI)
  apply (rule_tac x="hl_mod m n" in exI)
  apply (auto simp add: hl_mod_nonneg hl_mod_lt_abs hl_mod_div)
  unfolding hl_div_def hl_mod_def
  by auto

lemma DEF_div:
  "hl_div = (SOME q. \<exists>r. \<forall>m n. if n = int 0 then q m n = int 0 \<and> r m n = m
     else (int 0) \<le> (r m n) \<and> (r m n) < (abs n) \<and> m = ((q m n) * n) + (r m n))"
  apply (rule some_equality[symmetric])
  apply (rule_tac x="hl_mod" in exI)
  apply (auto simp add: fun_eq_iff hl_mod_nonneg hl_mod_lt_abs hl_mod_div)
  apply (simp add: hl_div_def)
  apply (simp add: hl_mod_def)
  apply (drule_tac x="x" in spec)
  apply (drule_tac x="xa" in spec)
  apply (case_tac "0 = xa")
  apply (simp add: hl_mod_def hl_div_def)
  apply (case_tac "xa > 0")
  apply (simp add: hl_mod_def hl_div_def)
  apply (metis comm_semiring_1_class.normalizing_semiring_rules(24) div_mult_self2 not_less_iff_gr_or_eq order_less_le add_0 zdiv_eq_0_iff mult_commute)
  apply (simp add: hl_mod_def hl_div_def)
  by (metis add.comm_neutral add_pos_nonneg div_mult_self1 less_minus_iff minus_add minus_add_cancel minus_minus mult_zero_right not_square_less_zero zdiv_eq_0_iff div_minus_right)

lemma DEF_rem:
  "hl_mod = (SOME r. \<forall>m n. if n = int 0 then
     (if 0 \<le> n then m div n else - (m div - n)) = int 0 \<and> r m n = m
     else int 0 \<le> r m n \<and> r m n < abs n \<and>
            m = (if 0 \<le> n then m div n else - (m div - n)) * n + r m n)"
  apply (rule some_equality[symmetric])
  apply (fold hl_div_def)
  apply (auto simp add: fun_eq_iff hl_mod_nonneg hl_mod_lt_abs hl_mod_div)
  apply (simp add: hl_div_def)
  apply (simp add: hl_mod_def)
  apply (drule_tac x="x" in spec)
  apply (drule_tac x="xa" in spec)
  apply (case_tac "0 = xa")
  apply (simp add: hl_mod_def hl_div_def)
  apply (case_tac "xa > 0")
  apply (simp add: hl_mod_def hl_div_def)
  apply (metis add_left_cancel mod_div_equality)
  apply (simp add: hl_mod_def hl_div_def)
  by (metis minus_mult_right mod_mult_self2 mod_pos_pos_trivial add_commute zminus_zmod mod_minus_right mult_commute)

lemma DEF_int_gcd:
  "int_gcd = (SOME d. \<forall>a b. (int 0) \<le> (d (a, b)) \<and> (d (a, b)) dvd a \<and>
       (d (a, b)) dvd b \<and> (\<exists>x y. d (a, b) = (a * x) + (b * y)))"
  apply (rule some_equality[symmetric])
  apply auto
  apply (metis bezout_int mult_commute)
  apply (auto simp add: fun_eq_iff)
  apply (drule_tac x="a" in spec)
  apply (drule_tac x="b" in spec)
  using gcd_greatest_int zdvd_antisym_nonneg
  by auto

definition "eqeq x y (r :: 'a \<Rightarrow> 'b \<Rightarrow> bool) = r x y"

lemma INT_INTEGRAL:
  "(\<forall>x. int 0 * x = int 0) \<and>
   (\<forall>(x :: int) y z. (x + y = x + z) = (y = z)) \<and>
   (\<forall>(w :: int) x y z. (w * y + x * z = w * z + x * y) = (w = x \<or> y = z))"
  by (auto simp add: crossproduct_eq)

end

