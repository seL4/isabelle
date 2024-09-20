(*
  File:     HOL/Library/Real_Mod.thy
  Authors:  Manuel Eberl, University of Innsbruck
*)
section \<open>Modulo and congruence on the reals\<close>
theory Real_Mod
  imports Complex_Main
begin

(* MOVED TO HOL-Library ON 20.03.2024 *)

definition rmod :: "real \<Rightarrow> real \<Rightarrow> real" (infixl \<open>rmod\<close> 70) where
  "x rmod y = x - \<bar>y\<bar> * of_int \<lfloor>x / \<bar>y\<bar>\<rfloor>"

lemma rmod_conv_frac: "y \<noteq> 0 \<Longrightarrow> x rmod y = frac (x / \<bar>y\<bar>) * \<bar>y\<bar>"
  by (simp add: rmod_def frac_def algebra_simps)

lemma rmod_conv_frac': "x rmod y = (if y = 0 then x else frac (x / \<bar>y\<bar>) * \<bar>y\<bar>)"
  by (simp add: rmod_def frac_def algebra_simps)

lemma rmod_rmod [simp]: "(x rmod y) rmod y = x rmod y"
  by (simp add: rmod_conv_frac')

lemma rmod_0_right [simp]: "x rmod 0 = x"
  by (simp add: rmod_def)

lemma rmod_less: "m > 0 \<Longrightarrow> x rmod m < m"
  by (simp add: rmod_conv_frac' frac_lt_1)

lemma rmod_less_abs: "m \<noteq> 0 \<Longrightarrow> x rmod m < \<bar>m\<bar>"
  by (simp add: rmod_conv_frac' frac_lt_1)

lemma rmod_le: "m > 0 \<Longrightarrow> x rmod m \<le> m"
  by (intro less_imp_le rmod_less)

lemma rmod_nonneg: "m \<noteq> 0 \<Longrightarrow> x rmod m \<ge> 0"
  unfolding rmod_def
  by (metis abs_le_zero_iff diff_ge_0_iff_ge floor_divide_lower linorder_not_le mult.commute)

lemma rmod_unique:
  assumes "z \<in> {0..<\<bar>y\<bar>}" "x = z + of_int n * y"
  shows   "x rmod y = z"
proof -
  have "(x - z) / y = of_int n"
    using assms by auto
  hence "(x - z) / \<bar>y\<bar> = of_int ((if y > 0 then 1 else -1) * n)"
    using assms(1) by (cases y "0 :: real" rule: linorder_cases) (auto split: if_splits)
  also have "\<dots> \<in> \<int>"
    by auto
  finally have "frac (x / \<bar>y\<bar>) = z / \<bar>y\<bar>"
    using assms(1) by (subst frac_unique_iff) (auto simp: field_simps)
  thus ?thesis
    using assms(1) by (auto simp: rmod_conv_frac')
qed

lemma rmod_0 [simp]: "0 rmod z = 0"
  by (simp add: rmod_def)

lemma rmod_add: "(x rmod z + y rmod z) rmod z = (x + y) rmod z"
proof (cases "z = 0")
  case [simp]: False
  show ?thesis
  proof (rule sym, rule rmod_unique)
    define n where "n = (if z > 0 then 1 else -1) * (\<lfloor>x / \<bar>z\<bar>\<rfloor> + \<lfloor>y / \<bar>z\<bar>\<rfloor> +
       \<lfloor>(x + y - (\<bar>z\<bar> * real_of_int \<lfloor>x / \<bar>z\<bar>\<rfloor> + \<bar>z\<bar> * real_of_int \<lfloor>y / \<bar>z\<bar>\<rfloor>)) / \<bar>z\<bar>\<rfloor>)"
    show "x + y = (x rmod z + y rmod z) rmod z + real_of_int n * z"
      by (simp add: rmod_def algebra_simps n_def)
  qed (auto simp: rmod_less_abs rmod_nonneg)
qed auto

lemma rmod_diff: "(x rmod z - y rmod z) rmod z = (x - y) rmod z"
proof (cases "z = 0")
  case [simp]: False
  show ?thesis
  proof (rule sym, rule rmod_unique)
    define n where "n = (if z > 0 then 1 else -1) * (\<lfloor>x / \<bar>z\<bar>\<rfloor> +
      \<lfloor>(x + \<bar>z\<bar> * real_of_int \<lfloor>y / \<bar>z\<bar>\<rfloor> - (y + \<bar>z\<bar> * real_of_int \<lfloor>x / \<bar>z\<bar>\<rfloor>)) / \<bar>z\<bar>\<rfloor> - \<lfloor>y / \<bar>z\<bar>\<rfloor>)"
    show "x - y = (x rmod z - y rmod z) rmod z + real_of_int n * z"
      by (simp add: rmod_def algebra_simps n_def)
  qed (auto simp: rmod_less_abs rmod_nonneg)
qed auto

lemma rmod_self [simp]: "x rmod x = 0"
  by (cases x "0 :: real" rule: linorder_cases) (auto simp: rmod_conv_frac)

lemma rmod_self_multiple_int [simp]: "(of_int n * x) rmod x = 0"
  by (cases x "0 :: real" rule: linorder_cases) (auto simp: rmod_conv_frac)

lemma rmod_self_multiple_nat [simp]: "(of_nat n * x) rmod x = 0"
  by (cases x "0 :: real" rule: linorder_cases) (auto simp: rmod_conv_frac)

lemma rmod_self_multiple_numeral [simp]: "(numeral n * x) rmod x = 0"
  by (cases x "0 :: real" rule: linorder_cases) (auto simp: rmod_conv_frac)

lemma rmod_self_multiple_int' [simp]: "(x * of_int n) rmod x = 0"
  by (cases x "0 :: real" rule: linorder_cases) (auto simp: rmod_conv_frac)

lemma rmod_self_multiple_nat' [simp]: "(x * of_nat n) rmod x = 0"
  by (cases x "0 :: real" rule: linorder_cases) (auto simp: rmod_conv_frac)

lemma rmod_self_multiple_numeral' [simp]: "(x * numeral n) rmod x = 0"
  by (cases x "0 :: real" rule: linorder_cases) (auto simp: rmod_conv_frac)

lemma rmod_idem [simp]: "x \<in> {0..<\<bar>y\<bar>} \<Longrightarrow> x rmod y = x"
  by (rule rmod_unique[of _ _ _ 0]) auto



definition rcong :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> bool" (\<open>(1[_ = _] '(' rmod _'))\<close>) where
  "[x = y] (rmod m) \<longleftrightarrow> x rmod m = y rmod m"

named_theorems rcong_intros

lemma rcong_0_right [simp]: "[x = y] (rmod 0) \<longleftrightarrow> x = y"
  by (simp add: rcong_def)

lemma rcong_0_iff: "[x = 0] (rmod m) \<longleftrightarrow> x rmod m = 0"
  and rcong_0_iff': "[0 = x] (rmod m) \<longleftrightarrow> x rmod m = 0"
  by (simp_all add: rcong_def)

lemma rcong_refl [simp, intro!, rcong_intros]: "[x = x] (rmod m)"
  by (simp add: rcong_def)

lemma rcong_sym: "[y = x] (rmod m) \<Longrightarrow> [x = y] (rmod m)"
  by (simp add: rcong_def)

lemma rcong_sym_iff: "[y = x] (rmod m) \<longleftrightarrow> [x = y] (rmod m)"
  unfolding rcong_def by (simp add: eq_commute del: rmod_idem)

lemma rcong_trans [trans]: "[x = y] (rmod m) \<Longrightarrow> [y = z] (rmod m) \<Longrightarrow> [x = z] (rmod m)"
  by (simp add: rcong_def)

lemma rcong_add [rcong_intros]:
  "[a = b] (rmod m) \<Longrightarrow> [c = d] (rmod m) \<Longrightarrow> [a + c = b + d] (rmod m)"
  unfolding rcong_def using rmod_add by metis

lemma rcong_diff [rcong_intros]:
  "[a = b] (rmod m) \<Longrightarrow> [c = d] (rmod m) \<Longrightarrow> [a - c = b - d] (rmod m)"
  unfolding rcong_def using rmod_diff by metis

lemma rcong_uminus [rcong_intros]:
  "[a = b] (rmod m) \<Longrightarrow> [-a = -b] (rmod m)"
  using rcong_diff[of 0 0 m a b] by simp

lemma rcong_uminus_uminus_iff [simp]: "[-x = -y] (rmod m) \<longleftrightarrow> [x = y] (rmod m)"
  using rcong_uminus minus_minus by metis

lemma rcong_uminus_left_iff: "[-x = y] (rmod m) \<longleftrightarrow> [x = -y] (rmod m)"
  using rcong_uminus minus_minus by metis

lemma rcong_add_right_cancel [simp]: "[a + c = b + c] (rmod m) \<longleftrightarrow> [a = b] (rmod m)"
  using rcong_add[of a b m c c] rcong_add[of "a + c" "b + c" m "-c" "-c"] by auto

lemma rcong_add_left_cancel [simp]: "[c + a = c + b] (rmod m) \<longleftrightarrow> [a = b] (rmod m)"
  by (subst (1 2) add.commute) simp

lemma rcong_diff_right_cancel [simp]: "[a - c = b - c] (rmod m) \<longleftrightarrow> [a = b] (rmod m)"
  by (metis rcong_add_left_cancel uminus_add_conv_diff)

lemma rcong_diff_left_cancel [simp]: "[c - a = c - b] (rmod m) \<longleftrightarrow> [a = b] (rmod m)"
  by (metis minus_diff_eq rcong_diff_right_cancel rcong_uminus_uminus_iff)

lemma rcong_rmod_right_iff [simp]: "[a = (b rmod m)] (rmod m) \<longleftrightarrow> [a = b] (rmod m)"
  and rcong_rmod_left_iff [simp]: "[(a rmod m) = b] (rmod m) \<longleftrightarrow> [a = b] (rmod m)"
  by (simp_all add: rcong_def)

lemma rcong_rmod_left [rcong_intros]: "[a = b] (rmod m) \<Longrightarrow> [(a rmod m) = b] (rmod m)"
  and rcong_rmod_right [rcong_intros]: "[a = b] (rmod m) \<Longrightarrow> [a = (b rmod m)] (rmod m)"
  by simp_all

lemma rcong_mult_of_int_0_left_left [rcong_intros]: "[0 = of_int n * m] (rmod m)"
  and rcong_mult_of_int_0_right_left [rcong_intros]: "[0 = m * of_int n] (rmod m)"
  and rcong_mult_of_int_0_left_right [rcong_intros]: "[of_int n * m = 0] (rmod m)"
  and rcong_mult_of_int_0_right_right [rcong_intros]: "[m * of_int n = 0] (rmod m)"
  by (simp_all add: rcong_def)

lemma rcong_altdef: "[a = b] (rmod m) \<longleftrightarrow> (\<exists>n. b = a + of_int n * m)"
proof (cases "m = 0")
  case False
  show ?thesis
  proof
    assume "[a = b] (rmod m)"
    hence "[a - b = b - b] (rmod m)"
      by (intro rcong_intros)
    hence "(a - b) rmod m = 0"
      by (simp add: rcong_def)
    then obtain n where "of_int n = (a - b) / \<bar>m\<bar>"
      using False by (auto simp: rmod_conv_frac elim!: Ints_cases)
    thus "\<exists>n. b = a + of_int n * m" using False
      by (intro exI[of _ "if m > 0 then -n else n"]) (auto simp: field_simps)
  next
    assume "\<exists>n. b = a + of_int n * m"
    then obtain n where n: "b = a + of_int n * m"
      by auto
    have "[a + 0 = a + of_int n * m] (rmod m)"
      by (intro rcong_intros)
    with n show "[a = b] (rmod m)"
      by simp
  qed
qed auto

lemma rcong_conv_diff_rmod_eq_0: "[x = y] (rmod m) \<longleftrightarrow> (x - y) rmod m = 0"
  by (metis cancel_comm_monoid_add_class.diff_cancel rcong_0_iff rcong_diff_right_cancel)

lemma rcong_imp_eq:
  assumes "[x = y] (rmod m)" "\<bar>x - y\<bar> < \<bar>m\<bar>"
  shows   "x = y"
proof -
  from assms obtain n where n: "y = x + of_int n * m"
    unfolding rcong_altdef by blast
  have "of_int \<bar>n\<bar> * \<bar>m\<bar> = \<bar>x - y\<bar>"
    by (simp add: n abs_mult)
  also have "\<dots> < 1 * \<bar>m\<bar>"
    using assms(2) by simp
  finally have "n = 0"
    by (subst (asm) mult_less_cancel_right) auto
  with n show ?thesis
    by simp
qed

lemma rcong_mult_modulus:
  assumes "[a = b] (rmod (m / c))" "c \<noteq> 0"
  shows   "[a * c = b * c] (rmod m)"
proof -
  from assms obtain k where k: "b = a + of_int k * (m / c)"
    by (auto simp: rcong_altdef)
  have "b * c = (a + of_int k * (m / c)) * c"
    by (simp only: k)
  also have "\<dots> = a * c + of_int k * m"
    using assms(2) by (auto simp: divide_simps)
  finally show ?thesis
    unfolding rcong_altdef by blast
qed

lemma rcong_divide_modulus:
  assumes "[a = b] (rmod (m * c))" "c \<noteq> 0"
  shows   "[a / c = b / c] (rmod m)"
  using rcong_mult_modulus[of a b m "1 / c"] assms by (auto simp: field_simps)

end