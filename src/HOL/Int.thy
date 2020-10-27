(*  Title:      HOL/Int.thy
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Author:     Tobias Nipkow, Florian Haftmann, TU Muenchen
*)

section \<open>The Integers as Equivalence Classes over Pairs of Natural Numbers\<close>

theory Int
  imports Equiv_Relations Power Quotient Fun_Def
begin

subsection \<open>Definition of integers as a quotient type\<close>

definition intrel :: "(nat \<times> nat) \<Rightarrow> (nat \<times> nat) \<Rightarrow> bool"
  where "intrel = (\<lambda>(x, y) (u, v). x + v = u + y)"

lemma intrel_iff [simp]: "intrel (x, y) (u, v) \<longleftrightarrow> x + v = u + y"
  by (simp add: intrel_def)

quotient_type int = "nat \<times> nat" / "intrel"
  morphisms Rep_Integ Abs_Integ
proof (rule equivpI)
  show "reflp intrel" by (auto simp: reflp_def)
  show "symp intrel" by (auto simp: symp_def)
  show "transp intrel" by (auto simp: transp_def)
qed

lemma eq_Abs_Integ [case_names Abs_Integ, cases type: int]:
  "(\<And>x y. z = Abs_Integ (x, y) \<Longrightarrow> P) \<Longrightarrow> P"
  by (induct z) auto


subsection \<open>Integers form a commutative ring\<close>

instantiation int :: comm_ring_1
begin

lift_definition zero_int :: "int" is "(0, 0)" .

lift_definition one_int :: "int" is "(1, 0)" .

lift_definition plus_int :: "int \<Rightarrow> int \<Rightarrow> int"
  is "\<lambda>(x, y) (u, v). (x + u, y + v)"
  by clarsimp

lift_definition uminus_int :: "int \<Rightarrow> int"
  is "\<lambda>(x, y). (y, x)"
  by clarsimp

lift_definition minus_int :: "int \<Rightarrow> int \<Rightarrow> int"
  is "\<lambda>(x, y) (u, v). (x + v, y + u)"
  by clarsimp

lift_definition times_int :: "int \<Rightarrow> int \<Rightarrow> int"
  is "\<lambda>(x, y) (u, v). (x*u + y*v, x*v + y*u)"
proof (clarsimp)
  fix s t u v w x y z :: nat
  assume "s + v = u + t" and "w + z = y + x"
  then have "(s + v) * w + (u + t) * x + u * (w + z) + v * (y + x) =
    (u + t) * w + (s + v) * x + u * (y + x) + v * (w + z)"
    by simp
  then show "(s * w + t * x) + (u * z + v * y) = (u * y + v * z) + (s * x + t * w)"
    by (simp add: algebra_simps)
qed

instance
  by standard (transfer; clarsimp simp: algebra_simps)+

end

abbreviation int :: "nat \<Rightarrow> int"
  where "int \<equiv> of_nat"

lemma int_def: "int n = Abs_Integ (n, 0)"
  by (induct n) (simp add: zero_int.abs_eq, simp add: one_int.abs_eq plus_int.abs_eq)

lemma int_transfer [transfer_rule]:
  includes lifting_syntax
  shows "rel_fun (=) pcr_int (\<lambda>n. (n, 0)) int"
  by (simp add: rel_fun_def int.pcr_cr_eq cr_int_def int_def)

lemma int_diff_cases: obtains (diff) m n where "z = int m - int n"
  by transfer clarsimp


subsection \<open>Integers are totally ordered\<close>

instantiation int :: linorder
begin

lift_definition less_eq_int :: "int \<Rightarrow> int \<Rightarrow> bool"
  is "\<lambda>(x, y) (u, v). x + v \<le> u + y"
  by auto

lift_definition less_int :: "int \<Rightarrow> int \<Rightarrow> bool"
  is "\<lambda>(x, y) (u, v). x + v < u + y"
  by auto

instance
  by standard (transfer, force)+

end

instantiation int :: distrib_lattice
begin

definition "(inf :: int \<Rightarrow> int \<Rightarrow> int) = min"

definition "(sup :: int \<Rightarrow> int \<Rightarrow> int) = max"

instance
  by standard (auto simp add: inf_int_def sup_int_def max_min_distrib2)

end

subsection \<open>Ordering properties of arithmetic operations\<close>

instance int :: ordered_cancel_ab_semigroup_add
proof
  fix i j k :: int
  show "i \<le> j \<Longrightarrow> k + i \<le> k + j"
    by transfer clarsimp
qed

text \<open>Strict Monotonicity of Multiplication.\<close>

text \<open>Strict, in 1st argument; proof is by induction on \<open>k > 0\<close>.\<close>
lemma zmult_zless_mono2_lemma: "i < j \<Longrightarrow> 0 < k \<Longrightarrow> int k * i < int k * j"
  for i j :: int
proof (induct k)
  case 0
  then show ?case by simp
next
  case (Suc k)
  then show ?case
    by (cases "k = 0") (simp_all add: distrib_right add_strict_mono)
qed

lemma zero_le_imp_eq_int:
  assumes "k \<ge> (0::int)" shows "\<exists>n. k = int n"
proof -
  have "b \<le> a \<Longrightarrow> \<exists>n::nat. a = n + b" for a b
    by (rule_tac x="a - b" in exI) simp
  with assms show ?thesis
    by transfer auto
qed

lemma zero_less_imp_eq_int:
  assumes "k > (0::int)" shows "\<exists>n>0. k = int n"
proof -
  have "b < a \<Longrightarrow> \<exists>n::nat. n>0 \<and> a = n + b" for a b
    by (rule_tac x="a - b" in exI) simp
  with assms show ?thesis
    by transfer auto
qed

lemma zmult_zless_mono2: "i < j \<Longrightarrow> 0 < k \<Longrightarrow> k * i < k * j"
  for i j k :: int
  by (drule zero_less_imp_eq_int) (auto simp add: zmult_zless_mono2_lemma)


text \<open>The integers form an ordered integral domain.\<close>

instantiation int :: linordered_idom
begin

definition zabs_def: "\<bar>i::int\<bar> = (if i < 0 then - i else i)"

definition zsgn_def: "sgn (i::int) = (if i = 0 then 0 else if 0 < i then 1 else - 1)"

instance
proof
  fix i j k :: int
  show "i < j \<Longrightarrow> 0 < k \<Longrightarrow> k * i < k * j"
    by (rule zmult_zless_mono2)
  show "\<bar>i\<bar> = (if i < 0 then -i else i)"
    by (simp only: zabs_def)
  show "sgn (i::int) = (if i=0 then 0 else if 0<i then 1 else - 1)"
    by (simp only: zsgn_def)
qed

end

lemma zless_imp_add1_zle: "w < z \<Longrightarrow> w + 1 \<le> z"
  for w z :: int
  by transfer clarsimp

lemma zless_iff_Suc_zadd: "w < z \<longleftrightarrow> (\<exists>n. z = w + int (Suc n))"
  for w z :: int
proof -
  have "\<And>a b c d. a + d < c + b \<Longrightarrow> \<exists>n. c + b = Suc (a + n + d)"
    by (rule_tac x="c+b - Suc(a+d)" in exI) arith
  then show ?thesis
    by transfer auto
qed

lemma zabs_less_one_iff [simp]: "\<bar>z\<bar> < 1 \<longleftrightarrow> z = 0" (is "?lhs \<longleftrightarrow> ?rhs")
  for z :: int
proof
  assume ?rhs
  then show ?lhs by simp
next
  assume ?lhs
  with zless_imp_add1_zle [of "\<bar>z\<bar>" 1] have "\<bar>z\<bar> + 1 \<le> 1" by simp
  then have "\<bar>z\<bar> \<le> 0" by simp
  then show ?rhs by simp
qed


subsection \<open>Embedding of the Integers into any \<open>ring_1\<close>: \<open>of_int\<close>\<close>

context ring_1
begin

lift_definition of_int :: "int \<Rightarrow> 'a"
  is "\<lambda>(i, j). of_nat i - of_nat j"
  by (clarsimp simp add: diff_eq_eq eq_diff_eq diff_add_eq
      of_nat_add [symmetric] simp del: of_nat_add)

lemma of_int_0 [simp]: "of_int 0 = 0"
  by transfer simp

lemma of_int_1 [simp]: "of_int 1 = 1"
  by transfer simp

lemma of_int_add [simp]: "of_int (w + z) = of_int w + of_int z"
  by transfer (clarsimp simp add: algebra_simps)

lemma of_int_minus [simp]: "of_int (- z) = - (of_int z)"
  by (transfer fixing: uminus) clarsimp

lemma of_int_diff [simp]: "of_int (w - z) = of_int w - of_int z"
  using of_int_add [of w "- z"] by simp

lemma of_int_mult [simp]: "of_int (w*z) = of_int w * of_int z"
  by (transfer fixing: times) (clarsimp simp add: algebra_simps)

lemma mult_of_int_commute: "of_int x * y = y * of_int x"
  by (transfer fixing: times) (auto simp: algebra_simps mult_of_nat_commute)

text \<open>Collapse nested embeddings.\<close>
lemma of_int_of_nat_eq [simp]: "of_int (int n) = of_nat n"
  by (induct n) auto

lemma of_int_numeral [simp, code_post]: "of_int (numeral k) = numeral k"
  by (simp add: of_nat_numeral [symmetric] of_int_of_nat_eq [symmetric])

lemma of_int_neg_numeral [code_post]: "of_int (- numeral k) = - numeral k"
  by simp

lemma of_int_power [simp]: "of_int (z ^ n) = of_int z ^ n"
  by (induct n) simp_all

lemma of_int_of_bool [simp]:
  "of_int (of_bool P) = of_bool P"
  by auto

end

context ring_char_0
begin

lemma of_int_eq_iff [simp]: "of_int w = of_int z \<longleftrightarrow> w = z"
  by transfer (clarsimp simp add: algebra_simps of_nat_add [symmetric] simp del: of_nat_add)

text \<open>Special cases where either operand is zero.\<close>
lemma of_int_eq_0_iff [simp]: "of_int z = 0 \<longleftrightarrow> z = 0"
  using of_int_eq_iff [of z 0] by simp

lemma of_int_0_eq_iff [simp]: "0 = of_int z \<longleftrightarrow> z = 0"
  using of_int_eq_iff [of 0 z] by simp

lemma of_int_eq_1_iff [iff]: "of_int z = 1 \<longleftrightarrow> z = 1"
  using of_int_eq_iff [of z 1] by simp

lemma numeral_power_eq_of_int_cancel_iff [simp]:
  "numeral x ^ n = of_int y \<longleftrightarrow> numeral x ^ n = y"
  using of_int_eq_iff[of "numeral x ^ n" y, unfolded of_int_numeral of_int_power] .

lemma of_int_eq_numeral_power_cancel_iff [simp]:
  "of_int y = numeral x ^ n \<longleftrightarrow> y = numeral x ^ n"
  using numeral_power_eq_of_int_cancel_iff [of x n y] by (metis (mono_tags))

lemma neg_numeral_power_eq_of_int_cancel_iff [simp]:
  "(- numeral x) ^ n = of_int y \<longleftrightarrow> (- numeral x) ^ n = y"
  using of_int_eq_iff[of "(- numeral x) ^ n" y]
  by simp

lemma of_int_eq_neg_numeral_power_cancel_iff [simp]:
  "of_int y = (- numeral x) ^ n \<longleftrightarrow> y = (- numeral x) ^ n"
  using neg_numeral_power_eq_of_int_cancel_iff[of x n y] by (metis (mono_tags))

lemma of_int_eq_of_int_power_cancel_iff[simp]: "(of_int b) ^ w = of_int x \<longleftrightarrow> b ^ w = x"
  by (metis of_int_power of_int_eq_iff)

lemma of_int_power_eq_of_int_cancel_iff[simp]: "of_int x = (of_int b) ^ w \<longleftrightarrow> x = b ^ w"
  by (metis of_int_eq_of_int_power_cancel_iff)

end

context linordered_idom
begin

text \<open>Every \<open>linordered_idom\<close> has characteristic zero.\<close>
subclass ring_char_0 ..

lemma of_int_le_iff [simp]: "of_int w \<le> of_int z \<longleftrightarrow> w \<le> z"
  by (transfer fixing: less_eq)
    (clarsimp simp add: algebra_simps of_nat_add [symmetric] simp del: of_nat_add)

lemma of_int_less_iff [simp]: "of_int w < of_int z \<longleftrightarrow> w < z"
  by (simp add: less_le order_less_le)

lemma of_int_0_le_iff [simp]: "0 \<le> of_int z \<longleftrightarrow> 0 \<le> z"
  using of_int_le_iff [of 0 z] by simp

lemma of_int_le_0_iff [simp]: "of_int z \<le> 0 \<longleftrightarrow> z \<le> 0"
  using of_int_le_iff [of z 0] by simp

lemma of_int_0_less_iff [simp]: "0 < of_int z \<longleftrightarrow> 0 < z"
  using of_int_less_iff [of 0 z] by simp

lemma of_int_less_0_iff [simp]: "of_int z < 0 \<longleftrightarrow> z < 0"
  using of_int_less_iff [of z 0] by simp

lemma of_int_1_le_iff [simp]: "1 \<le> of_int z \<longleftrightarrow> 1 \<le> z"
  using of_int_le_iff [of 1 z] by simp

lemma of_int_le_1_iff [simp]: "of_int z \<le> 1 \<longleftrightarrow> z \<le> 1"
  using of_int_le_iff [of z 1] by simp

lemma of_int_1_less_iff [simp]: "1 < of_int z \<longleftrightarrow> 1 < z"
  using of_int_less_iff [of 1 z] by simp

lemma of_int_less_1_iff [simp]: "of_int z < 1 \<longleftrightarrow> z < 1"
  using of_int_less_iff [of z 1] by simp

lemma of_int_pos: "z > 0 \<Longrightarrow> of_int z > 0"
  by simp

lemma of_int_nonneg: "z \<ge> 0 \<Longrightarrow> of_int z \<ge> 0"
  by simp

lemma of_int_abs [simp]: "of_int \<bar>x\<bar> = \<bar>of_int x\<bar>"
  by (auto simp add: abs_if)

lemma of_int_lessD:
  assumes "\<bar>of_int n\<bar> < x"
  shows "n = 0 \<or> x > 1"
proof (cases "n = 0")
  case True
  then show ?thesis by simp
next
  case False
  then have "\<bar>n\<bar> \<noteq> 0" by simp
  then have "\<bar>n\<bar> > 0" by simp
  then have "\<bar>n\<bar> \<ge> 1"
    using zless_imp_add1_zle [of 0 "\<bar>n\<bar>"] by simp
  then have "\<bar>of_int n\<bar> \<ge> 1"
    unfolding of_int_1_le_iff [of "\<bar>n\<bar>", symmetric] by simp
  then have "1 < x" using assms by (rule le_less_trans)
  then show ?thesis ..
qed

lemma of_int_leD:
  assumes "\<bar>of_int n\<bar> \<le> x"
  shows "n = 0 \<or> 1 \<le> x"
proof (cases "n = 0")
  case True
  then show ?thesis by simp
next
  case False
  then have "\<bar>n\<bar> \<noteq> 0" by simp
  then have "\<bar>n\<bar> > 0" by simp
  then have "\<bar>n\<bar> \<ge> 1"
    using zless_imp_add1_zle [of 0 "\<bar>n\<bar>"] by simp
  then have "\<bar>of_int n\<bar> \<ge> 1"
    unfolding of_int_1_le_iff [of "\<bar>n\<bar>", symmetric] by simp
  then have "1 \<le> x" using assms by (rule order_trans)
  then show ?thesis ..
qed

lemma numeral_power_le_of_int_cancel_iff [simp]:
  "numeral x ^ n \<le> of_int a \<longleftrightarrow> numeral x ^ n \<le> a"
  by (metis (mono_tags) local.of_int_eq_numeral_power_cancel_iff of_int_le_iff)

lemma of_int_le_numeral_power_cancel_iff [simp]:
  "of_int a \<le> numeral x ^ n \<longleftrightarrow> a \<le> numeral x ^ n"
  by (metis (mono_tags) local.numeral_power_eq_of_int_cancel_iff of_int_le_iff)

lemma numeral_power_less_of_int_cancel_iff [simp]:
  "numeral x ^ n < of_int a \<longleftrightarrow> numeral x ^ n < a"
  by (metis (mono_tags) local.of_int_eq_numeral_power_cancel_iff of_int_less_iff)

lemma of_int_less_numeral_power_cancel_iff [simp]:
  "of_int a < numeral x ^ n \<longleftrightarrow> a < numeral x ^ n"
  by (metis (mono_tags) local.of_int_eq_numeral_power_cancel_iff of_int_less_iff)

lemma neg_numeral_power_le_of_int_cancel_iff [simp]:
  "(- numeral x) ^ n \<le> of_int a \<longleftrightarrow> (- numeral x) ^ n \<le> a"
  by (metis (mono_tags) of_int_le_iff of_int_neg_numeral of_int_power)

lemma of_int_le_neg_numeral_power_cancel_iff [simp]:
  "of_int a \<le> (- numeral x) ^ n \<longleftrightarrow> a \<le> (- numeral x) ^ n"
  by (metis (mono_tags) of_int_le_iff of_int_neg_numeral of_int_power)

lemma neg_numeral_power_less_of_int_cancel_iff [simp]:
  "(- numeral x) ^ n < of_int a \<longleftrightarrow> (- numeral x) ^ n < a"
  using of_int_less_iff[of "(- numeral x) ^ n" a]
  by simp

lemma of_int_less_neg_numeral_power_cancel_iff [simp]:
  "of_int a < (- numeral x) ^ n \<longleftrightarrow> a < (- numeral x::int) ^ n"
  using of_int_less_iff[of a "(- numeral x) ^ n"]
  by simp

lemma of_int_le_of_int_power_cancel_iff[simp]: "(of_int b) ^ w \<le> of_int x \<longleftrightarrow> b ^ w \<le> x"
  by (metis (mono_tags) of_int_le_iff of_int_power)

lemma of_int_power_le_of_int_cancel_iff[simp]: "of_int x \<le> (of_int b) ^ w\<longleftrightarrow> x \<le> b ^ w"
  by (metis (mono_tags) of_int_le_iff of_int_power)

lemma of_int_less_of_int_power_cancel_iff[simp]: "(of_int b) ^ w < of_int x \<longleftrightarrow> b ^ w < x"
  by (metis (mono_tags) of_int_less_iff of_int_power)

lemma of_int_power_less_of_int_cancel_iff[simp]: "of_int x < (of_int b) ^ w\<longleftrightarrow> x < b ^ w"
  by (metis (mono_tags) of_int_less_iff of_int_power)

lemma of_int_max: "of_int (max x y) = max (of_int x) (of_int y)"
  by (auto simp: max_def)

lemma of_int_min: "of_int (min x y) = min (of_int x) (of_int y)"
  by (auto simp: min_def)

end

context division_ring
begin

lemmas mult_inverse_of_int_commute =
  mult_commute_imp_mult_inverse_commute[OF mult_of_int_commute]

end

text \<open>Comparisons involving \<^term>\<open>of_int\<close>.\<close>

lemma of_int_eq_numeral_iff [iff]: "of_int z = (numeral n :: 'a::ring_char_0) \<longleftrightarrow> z = numeral n"
  using of_int_eq_iff by fastforce

lemma of_int_le_numeral_iff [simp]:
  "of_int z \<le> (numeral n :: 'a::linordered_idom) \<longleftrightarrow> z \<le> numeral n"
  using of_int_le_iff [of z "numeral n"] by simp

lemma of_int_numeral_le_iff [simp]:
  "(numeral n :: 'a::linordered_idom) \<le> of_int z \<longleftrightarrow> numeral n \<le> z"
  using of_int_le_iff [of "numeral n"] by simp

lemma of_int_less_numeral_iff [simp]:
  "of_int z < (numeral n :: 'a::linordered_idom) \<longleftrightarrow> z < numeral n"
  using of_int_less_iff [of z "numeral n"] by simp

lemma of_int_numeral_less_iff [simp]:
  "(numeral n :: 'a::linordered_idom) < of_int z \<longleftrightarrow> numeral n < z"
  using of_int_less_iff [of "numeral n" z] by simp

lemma of_nat_less_of_int_iff: "(of_nat n::'a::linordered_idom) < of_int x \<longleftrightarrow> int n < x"
  by (metis of_int_of_nat_eq of_int_less_iff)

lemma of_int_eq_id [simp]: "of_int = id"
proof
  show "of_int z = id z" for z
    by (cases z rule: int_diff_cases) simp
qed

instance int :: no_top
proof
  show "\<And>x::int. \<exists>y. x < y"
    by (rule_tac x="x + 1" in exI) simp
qed

instance int :: no_bot
proof
  show "\<And>x::int. \<exists>y. y < x"
    by (rule_tac x="x - 1" in exI) simp
qed


subsection \<open>Magnitude of an Integer, as a Natural Number: \<open>nat\<close>\<close>

lift_definition nat :: "int \<Rightarrow> nat" is "\<lambda>(x, y). x - y"
  by auto

lemma nat_int [simp]: "nat (int n) = n"
  by transfer simp

lemma int_nat_eq [simp]: "int (nat z) = (if 0 \<le> z then z else 0)"
  by transfer clarsimp

lemma nat_0_le: "0 \<le> z \<Longrightarrow> int (nat z) = z"
  by simp

lemma nat_le_0 [simp]: "z \<le> 0 \<Longrightarrow> nat z = 0"
  by transfer clarsimp

lemma nat_le_eq_zle: "0 < w \<or> 0 \<le> z \<Longrightarrow> nat w \<le> nat z \<longleftrightarrow> w \<le> z"
  by transfer (clarsimp, arith)

text \<open>An alternative condition is \<^term>\<open>0 \<le> w\<close>.\<close>
lemma nat_mono_iff: "0 < z \<Longrightarrow> nat w < nat z \<longleftrightarrow> w < z"
  by (simp add: nat_le_eq_zle linorder_not_le [symmetric])

lemma nat_less_eq_zless: "0 \<le> w \<Longrightarrow> nat w < nat z \<longleftrightarrow> w < z"
  by (simp add: nat_le_eq_zle linorder_not_le [symmetric])

lemma zless_nat_conj [simp]: "nat w < nat z \<longleftrightarrow> 0 < z \<and> w < z"
  by transfer (clarsimp, arith)

lemma nonneg_int_cases:
  assumes "0 \<le> k"
  obtains n where "k = int n"
proof -
  from assms have "k = int (nat k)"
    by simp
  then show thesis
    by (rule that)
qed

lemma pos_int_cases:
  assumes "0 < k"
  obtains n where "k = int n" and "n > 0"
proof -
  from assms have "0 \<le> k"
    by simp
  then obtain n where "k = int n"
    by (rule nonneg_int_cases)
  moreover have "n > 0"
    using \<open>k = int n\<close> assms by simp
  ultimately show thesis
    by (rule that)
qed

lemma nonpos_int_cases:
  assumes "k \<le> 0"
  obtains n where "k = - int n"
proof -
  from assms have "- k \<ge> 0"
    by simp
  then obtain n where "- k = int n"
    by (rule nonneg_int_cases)
  then have "k = - int n"
    by simp
  then show thesis
    by (rule that)
qed

lemma neg_int_cases:
  assumes "k < 0"
  obtains n where "k = - int n" and "n > 0"
proof -
  from assms have "- k > 0"
    by simp
  then obtain n where "- k = int n" and "- k > 0"
    by (blast elim: pos_int_cases)
  then have "k = - int n" and "n > 0"
    by simp_all
  then show thesis
    by (rule that)
qed

lemma nat_eq_iff: "nat w = m \<longleftrightarrow> (if 0 \<le> w then w = int m else m = 0)"
  by transfer (clarsimp simp add: le_imp_diff_is_add)

lemma nat_eq_iff2: "m = nat w \<longleftrightarrow> (if 0 \<le> w then w = int m else m = 0)"
  using nat_eq_iff [of w m] by auto

lemma nat_0 [simp]: "nat 0 = 0"
  by (simp add: nat_eq_iff)

lemma nat_1 [simp]: "nat 1 = Suc 0"
  by (simp add: nat_eq_iff)

lemma nat_numeral [simp]: "nat (numeral k) = numeral k"
  by (simp add: nat_eq_iff)

lemma nat_neg_numeral [simp]: "nat (- numeral k) = 0"
  by simp

lemma nat_2: "nat 2 = Suc (Suc 0)"
  by simp

lemma nat_less_iff: "0 \<le> w \<Longrightarrow> nat w < m \<longleftrightarrow> w < of_nat m"
  by transfer (clarsimp, arith)

lemma nat_le_iff: "nat x \<le> n \<longleftrightarrow> x \<le> int n"
  by transfer (clarsimp simp add: le_diff_conv)

lemma nat_mono: "x \<le> y \<Longrightarrow> nat x \<le> nat y"
  by transfer auto

lemma nat_0_iff[simp]: "nat i = 0 \<longleftrightarrow> i \<le> 0"
  for i :: int
  by transfer clarsimp

lemma int_eq_iff: "of_nat m = z \<longleftrightarrow> m = nat z \<and> 0 \<le> z"
  by (auto simp add: nat_eq_iff2)

lemma zero_less_nat_eq [simp]: "0 < nat z \<longleftrightarrow> 0 < z"
  using zless_nat_conj [of 0] by auto

lemma nat_add_distrib: "0 \<le> z \<Longrightarrow> 0 \<le> z' \<Longrightarrow> nat (z + z') = nat z + nat z'"
  by transfer clarsimp

lemma nat_diff_distrib': "0 \<le> x \<Longrightarrow> 0 \<le> y \<Longrightarrow> nat (x - y) = nat x - nat y"
  by transfer clarsimp

lemma nat_diff_distrib: "0 \<le> z' \<Longrightarrow> z' \<le> z \<Longrightarrow> nat (z - z') = nat z - nat z'"
  by (rule nat_diff_distrib') auto

lemma nat_zminus_int [simp]: "nat (- int n) = 0"
  by transfer simp

lemma le_nat_iff: "k \<ge> 0 \<Longrightarrow> n \<le> nat k \<longleftrightarrow> int n \<le> k"
  by transfer auto

lemma zless_nat_eq_int_zless: "m < nat z \<longleftrightarrow> int m < z"
  by transfer (clarsimp simp add: less_diff_conv)

lemma (in ring_1) of_nat_nat [simp]: "0 \<le> z \<Longrightarrow> of_nat (nat z) = of_int z"
  by transfer (clarsimp simp add: of_nat_diff)

lemma diff_nat_numeral [simp]: "(numeral v :: nat) - numeral v' = nat (numeral v - numeral v')"
  by (simp only: nat_diff_distrib' zero_le_numeral nat_numeral)

lemma nat_abs_triangle_ineq:
  "nat \<bar>k + l\<bar> \<le> nat \<bar>k\<bar> + nat \<bar>l\<bar>"
  by (simp add: nat_add_distrib [symmetric] nat_le_eq_zle abs_triangle_ineq)

lemma nat_of_bool [simp]:
  "nat (of_bool P) = of_bool P"
  by auto

lemma split_nat [arith_split]: "P (nat i) \<longleftrightarrow> ((\<forall>n. i = int n \<longrightarrow> P n) \<and> (i < 0 \<longrightarrow> P 0))"
  (is "?P = (?L \<and> ?R)")
  for i :: int
proof (cases "i < 0")
  case True
  then show ?thesis
    by auto
next
  case False
  have "?P = ?L"
  proof
    assume ?P
    then show ?L using False by auto
  next
    assume ?L
    moreover from False have "int (nat i) = i"
      by (simp add: not_less)
    ultimately show ?P
      by simp
  qed
  with False show ?thesis by simp
qed

lemma all_nat: "(\<forall>x. P x) \<longleftrightarrow> (\<forall>x\<ge>0. P (nat x))"
  by (auto split: split_nat)

lemma ex_nat: "(\<exists>x. P x) \<longleftrightarrow> (\<exists>x. 0 \<le> x \<and> P (nat x))"
proof
  assume "\<exists>x. P x"
  then obtain x where "P x" ..
  then have "int x \<ge> 0 \<and> P (nat (int x))" by simp
  then show "\<exists>x\<ge>0. P (nat x)" ..
next
  assume "\<exists>x\<ge>0. P (nat x)"
  then show "\<exists>x. P x" by auto
qed


text \<open>For termination proofs:\<close>
lemma measure_function_int[measure_function]: "is_measure (nat \<circ> abs)" ..


subsection \<open>Lemmas about the Function \<^term>\<open>of_nat\<close> and Orderings\<close>

lemma negative_zless_0: "- (int (Suc n)) < (0 :: int)"
  by (simp add: order_less_le del: of_nat_Suc)

lemma negative_zless [iff]: "- (int (Suc n)) < int m"
  by (rule negative_zless_0 [THEN order_less_le_trans], simp)

lemma negative_zle_0: "- int n \<le> 0"
  by (simp add: minus_le_iff)

lemma negative_zle [iff]: "- int n \<le> int m"
  by (rule order_trans [OF negative_zle_0 of_nat_0_le_iff])

lemma not_zle_0_negative [simp]: "\<not> 0 \<le> - int (Suc n)"
  by (subst le_minus_iff) (simp del: of_nat_Suc)

lemma int_zle_neg: "int n \<le> - int m \<longleftrightarrow> n = 0 \<and> m = 0"
  by transfer simp

lemma not_int_zless_negative [simp]: "\<not> int n < - int m"
  by (simp add: linorder_not_less)

lemma negative_eq_positive [simp]: "- int n = of_nat m \<longleftrightarrow> n = 0 \<and> m = 0"
  by (force simp add: order_eq_iff [of "- of_nat n"] int_zle_neg)

lemma zle_iff_zadd: "w \<le> z \<longleftrightarrow> (\<exists>n. z = w + int n)"
  (is "?lhs \<longleftrightarrow> ?rhs")
proof
  assume ?rhs
  then show ?lhs by auto
next
  assume ?lhs
  then have "0 \<le> z - w" by simp
  then obtain n where "z - w = int n"
    using zero_le_imp_eq_int [of "z - w"] by blast
  then have "z = w + int n" by simp
  then show ?rhs ..
qed

lemma zadd_int_left: "int m + (int n + z) = int (m + n) + z"
  by simp

text \<open>
  This version is proved for all ordered rings, not just integers!
  It is proved here because attribute \<open>arith_split\<close> is not available
  in theory \<open>Rings\<close>.
  But is it really better than just rewriting with \<open>abs_if\<close>?
\<close>
lemma abs_split [arith_split, no_atp]: "P \<bar>a\<bar> \<longleftrightarrow> (0 \<le> a \<longrightarrow> P a) \<and> (a < 0 \<longrightarrow> P (- a))"
  for a :: "'a::linordered_idom"
  by (force dest: order_less_le_trans simp add: abs_if linorder_not_less)

lemma negD:
  assumes "x < 0" shows "\<exists>n. x = - (int (Suc n))"
proof -
  have "\<And>a b. a < b \<Longrightarrow> \<exists>n. Suc (a + n) = b"
    by (rule_tac x="b - Suc a" in exI) arith
  with assms show ?thesis
    by transfer auto
qed


subsection \<open>Cases and induction\<close>

text \<open>
  Now we replace the case analysis rule by a more conventional one:
  whether an integer is negative or not.
\<close>

text \<open>This version is symmetric in the two subgoals.\<close>
lemma int_cases2 [case_names nonneg nonpos, cases type: int]:
  "(\<And>n. z = int n \<Longrightarrow> P) \<Longrightarrow> (\<And>n. z = - (int n) \<Longrightarrow> P) \<Longrightarrow> P"
  by (cases "z < 0") (auto simp add: linorder_not_less dest!: negD nat_0_le [THEN sym])

text \<open>This is the default, with a negative case.\<close>
lemma int_cases [case_names nonneg neg, cases type: int]:
  assumes pos: "\<And>n. z = int n \<Longrightarrow> P" and neg: "\<And>n. z = - (int (Suc n)) \<Longrightarrow> P"
  shows P
proof (cases "z < 0")
  case True
  with neg show ?thesis
    by (blast dest!: negD)
next
  case False
  with pos show ?thesis
    by (force simp add: linorder_not_less dest: nat_0_le [THEN sym])
qed

lemma int_cases3 [case_names zero pos neg]:
  fixes k :: int
  assumes "k = 0 \<Longrightarrow> P" and "\<And>n. k = int n \<Longrightarrow> n > 0 \<Longrightarrow> P"
    and "\<And>n. k = - int n \<Longrightarrow> n > 0 \<Longrightarrow> P"
  shows "P"
proof (cases k "0::int" rule: linorder_cases)
  case equal
  with assms(1) show P by simp
next
  case greater
  then have *: "nat k > 0" by simp
  moreover from * have "k = int (nat k)" by auto
  ultimately show P using assms(2) by blast
next
  case less
  then have *: "nat (- k) > 0" by simp
  moreover from * have "k = - int (nat (- k))" by auto
  ultimately show P using assms(3) by blast
qed

lemma int_of_nat_induct [case_names nonneg neg, induct type: int]:
  "(\<And>n. P (int n)) \<Longrightarrow> (\<And>n. P (- (int (Suc n)))) \<Longrightarrow> P z"
  by (cases z) auto

lemma sgn_mult_dvd_iff [simp]:
  "sgn r * l dvd k \<longleftrightarrow> l dvd k \<and> (r = 0 \<longrightarrow> k = 0)" for k l r :: int
  by (cases r rule: int_cases3) auto

lemma mult_sgn_dvd_iff [simp]:
  "l * sgn r dvd k \<longleftrightarrow> l dvd k \<and> (r = 0 \<longrightarrow> k = 0)" for k l r :: int
  using sgn_mult_dvd_iff [of r l k] by (simp add: ac_simps)

lemma dvd_sgn_mult_iff [simp]:
  "l dvd sgn r * k \<longleftrightarrow> l dvd k \<or> r = 0" for k l r :: int
  by (cases r rule: int_cases3) simp_all

lemma dvd_mult_sgn_iff [simp]:
  "l dvd k * sgn r \<longleftrightarrow> l dvd k \<or> r = 0" for k l r :: int
  using dvd_sgn_mult_iff [of l r k] by (simp add: ac_simps)

lemma int_sgnE:
  fixes k :: int
  obtains n and l where "k = sgn l * int n"
proof -
  have "k = sgn k * int (nat \<bar>k\<bar>)"
    by (simp add: sgn_mult_abs)
  then show ?thesis ..
qed


subsubsection \<open>Binary comparisons\<close>

text \<open>Preliminaries\<close>

lemma le_imp_0_less:
  fixes z :: int
  assumes le: "0 \<le> z"
  shows "0 < 1 + z"
proof -
  have "0 \<le> z" by fact
  also have "\<dots> < z + 1" by (rule less_add_one)
  also have "\<dots> = 1 + z" by (simp add: ac_simps)
  finally show "0 < 1 + z" .
qed

lemma odd_less_0_iff: "1 + z + z < 0 \<longleftrightarrow> z < 0"
  for z :: int
proof (cases z)
  case (nonneg n)
  then show ?thesis
    by (simp add: linorder_not_less add.assoc add_increasing le_imp_0_less [THEN order_less_imp_le])
next
  case (neg n)
  then show ?thesis
    by (simp del: of_nat_Suc of_nat_add of_nat_1
        add: algebra_simps of_nat_1 [where 'a=int, symmetric] of_nat_add [symmetric])
qed


subsubsection \<open>Comparisons, for Ordered Rings\<close>

lemma odd_nonzero: "1 + z + z \<noteq> 0"
  for z :: int
proof (cases z)
  case (nonneg n)
  have le: "0 \<le> z + z"
    by (simp add: nonneg add_increasing)
  then show ?thesis
    using le_imp_0_less [OF le] by (auto simp: ac_simps)
next
  case (neg n)
  show ?thesis
  proof
    assume eq: "1 + z + z = 0"
    have "0 < 1 + (int n + int n)"
      by (simp add: le_imp_0_less add_increasing)
    also have "\<dots> = - (1 + z + z)"
      by (simp add: neg add.assoc [symmetric])
    also have "\<dots> = 0" by (simp add: eq)
    finally have "0<0" ..
    then show False by blast
  qed
qed


subsection \<open>The Set of Integers\<close>

context ring_1
begin

definition Ints :: "'a set"  ("\<int>")
  where "\<int> = range of_int"

lemma Ints_of_int [simp]: "of_int z \<in> \<int>"
  by (simp add: Ints_def)

lemma Ints_of_nat [simp]: "of_nat n \<in> \<int>"
  using Ints_of_int [of "of_nat n"] by simp

lemma Ints_0 [simp]: "0 \<in> \<int>"
  using Ints_of_int [of "0"] by simp

lemma Ints_1 [simp]: "1 \<in> \<int>"
  using Ints_of_int [of "1"] by simp

lemma Ints_numeral [simp]: "numeral n \<in> \<int>"
  by (subst of_nat_numeral [symmetric], rule Ints_of_nat)

lemma Ints_add [simp]: "a \<in> \<int> \<Longrightarrow> b \<in> \<int> \<Longrightarrow> a + b \<in> \<int>"
  by (force simp add: Ints_def simp flip: of_int_add intro: range_eqI)

lemma Ints_minus [simp]: "a \<in> \<int> \<Longrightarrow> -a \<in> \<int>"
  by (force simp add: Ints_def simp flip: of_int_minus intro: range_eqI)

lemma minus_in_Ints_iff: "-x \<in> \<int> \<longleftrightarrow> x \<in> \<int>"
  using Ints_minus[of x] Ints_minus[of "-x"] by auto

lemma Ints_diff [simp]: "a \<in> \<int> \<Longrightarrow> b \<in> \<int> \<Longrightarrow> a - b \<in> \<int>"
  by (force simp add: Ints_def simp flip: of_int_diff intro: range_eqI)

lemma Ints_mult [simp]: "a \<in> \<int> \<Longrightarrow> b \<in> \<int> \<Longrightarrow> a * b \<in> \<int>"
  by (force simp add: Ints_def simp flip: of_int_mult intro: range_eqI)

lemma Ints_power [simp]: "a \<in> \<int> \<Longrightarrow> a ^ n \<in> \<int>"
  by (induct n) simp_all

lemma Ints_cases [cases set: Ints]:
  assumes "q \<in> \<int>"
  obtains (of_int) z where "q = of_int z"
  unfolding Ints_def
proof -
  from \<open>q \<in> \<int>\<close> have "q \<in> range of_int" unfolding Ints_def .
  then obtain z where "q = of_int z" ..
  then show thesis ..
qed

lemma Ints_induct [case_names of_int, induct set: Ints]:
  "q \<in> \<int> \<Longrightarrow> (\<And>z. P (of_int z)) \<Longrightarrow> P q"
  by (rule Ints_cases) auto

lemma Nats_subset_Ints: "\<nat> \<subseteq> \<int>"
  unfolding Nats_def Ints_def
  by (rule subsetI, elim imageE, hypsubst, subst of_int_of_nat_eq[symmetric], rule imageI) simp_all

lemma Nats_altdef1: "\<nat> = {of_int n |n. n \<ge> 0}"
proof (intro subsetI equalityI)
  fix x :: 'a
  assume "x \<in> {of_int n |n. n \<ge> 0}"
  then obtain n where "x = of_int n" "n \<ge> 0"
    by (auto elim!: Ints_cases)
  then have "x = of_nat (nat n)"
    by (subst of_nat_nat) simp_all
  then show "x \<in> \<nat>"
    by simp
next
  fix x :: 'a
  assume "x \<in> \<nat>"
  then obtain n where "x = of_nat n"
    by (auto elim!: Nats_cases)
  then have "x = of_int (int n)" by simp
  also have "int n \<ge> 0" by simp
  then have "of_int (int n) \<in> {of_int n |n. n \<ge> 0}" by blast
  finally show "x \<in> {of_int n |n. n \<ge> 0}" .
qed

end

lemma (in linordered_idom) Ints_abs [simp]:
  shows "a \<in> \<int> \<Longrightarrow> abs a \<in> \<int>"
  by (auto simp: abs_if)

lemma (in linordered_idom) Nats_altdef2: "\<nat> = {n \<in> \<int>. n \<ge> 0}"
proof (intro subsetI equalityI)
  fix x :: 'a
  assume "x \<in> {n \<in> \<int>. n \<ge> 0}"
  then obtain n where "x = of_int n" "n \<ge> 0"
    by (auto elim!: Ints_cases)
  then have "x = of_nat (nat n)"
    by (subst of_nat_nat) simp_all
  then show "x \<in> \<nat>"
    by simp
qed (auto elim!: Nats_cases)

lemma (in idom_divide) of_int_divide_in_Ints: 
  "of_int a div of_int b \<in> \<int>" if "b dvd a"
proof -
  from that obtain c where "a = b * c" ..
  then show ?thesis
    by (cases "of_int b = 0") simp_all
qed

text \<open>The premise involving \<^term>\<open>Ints\<close> prevents \<^term>\<open>a = 1/2\<close>.\<close>

lemma Ints_double_eq_0_iff:
  fixes a :: "'a::ring_char_0"
  assumes in_Ints: "a \<in> \<int>"
  shows "a + a = 0 \<longleftrightarrow> a = 0"
    (is "?lhs \<longleftrightarrow> ?rhs")
proof -
  from in_Ints have "a \<in> range of_int"
    unfolding Ints_def [symmetric] .
  then obtain z where a: "a = of_int z" ..
  show ?thesis
  proof
    assume ?rhs
    then show ?lhs by simp
  next
    assume ?lhs
    with a have "of_int (z + z) = (of_int 0 :: 'a)" by simp
    then have "z + z = 0" by (simp only: of_int_eq_iff)
    then have "z = 0" by (simp only: double_zero)
    with a show ?rhs by simp
  qed
qed

lemma Ints_odd_nonzero:
  fixes a :: "'a::ring_char_0"
  assumes in_Ints: "a \<in> \<int>"
  shows "1 + a + a \<noteq> 0"
proof -
  from in_Ints have "a \<in> range of_int"
    unfolding Ints_def [symmetric] .
  then obtain z where a: "a = of_int z" ..
  show ?thesis
  proof
    assume "1 + a + a = 0"
    with a have "of_int (1 + z + z) = (of_int 0 :: 'a)" by simp
    then have "1 + z + z = 0" by (simp only: of_int_eq_iff)
    with odd_nonzero show False by blast
  qed
qed

lemma Nats_numeral [simp]: "numeral w \<in> \<nat>"
  using of_nat_in_Nats [of "numeral w"] by simp

lemma Ints_odd_less_0:
  fixes a :: "'a::linordered_idom"
  assumes in_Ints: "a \<in> \<int>"
  shows "1 + a + a < 0 \<longleftrightarrow> a < 0"
proof -
  from in_Ints have "a \<in> range of_int"
    unfolding Ints_def [symmetric] .
  then obtain z where a: "a = of_int z" ..
  with a have "1 + a + a < 0 \<longleftrightarrow> of_int (1 + z + z) < (of_int 0 :: 'a)"
    by simp
  also have "\<dots> \<longleftrightarrow> z < 0"
    by (simp only: of_int_less_iff odd_less_0_iff)
  also have "\<dots> \<longleftrightarrow> a < 0"
    by (simp add: a)
  finally show ?thesis .
qed


subsection \<open>\<^term>\<open>sum\<close> and \<^term>\<open>prod\<close>\<close>

context semiring_1
begin

lemma of_nat_sum [simp]:
  "of_nat (sum f A) = (\<Sum>x\<in>A. of_nat (f x))"
  by (induction A rule: infinite_finite_induct) auto

end

context ring_1
begin

lemma of_int_sum [simp]:
  "of_int (sum f A) = (\<Sum>x\<in>A. of_int (f x))"
  by (induction A rule: infinite_finite_induct) auto

end

context comm_semiring_1
begin

lemma of_nat_prod [simp]:
  "of_nat (prod f A) = (\<Prod>x\<in>A. of_nat (f x))"
  by (induction A rule: infinite_finite_induct) auto

end

context comm_ring_1
begin

lemma of_int_prod [simp]:
  "of_int (prod f A) = (\<Prod>x\<in>A. of_int (f x))"
  by (induction A rule: infinite_finite_induct) auto

end


subsection \<open>Setting up simplification procedures\<close>

ML_file \<open>Tools/int_arith.ML\<close>

declaration \<open>K (
  Lin_Arith.add_discrete_type \<^type_name>\<open>Int.int\<close>
  #> Lin_Arith.add_lessD @{thm zless_imp_add1_zle}
  #> Lin_Arith.add_inj_thms @{thms of_nat_le_iff [THEN iffD2] of_nat_eq_iff [THEN iffD2]}
  #> Lin_Arith.add_inj_const (\<^const_name>\<open>of_nat\<close>, \<^typ>\<open>nat \<Rightarrow> int\<close>)
  #> Lin_Arith.add_simps
      @{thms of_int_0 of_int_1 of_int_add of_int_mult of_int_numeral of_int_neg_numeral nat_0 nat_1 diff_nat_numeral nat_numeral
      neg_less_iff_less
      True_implies_equals
      distrib_left [where a = "numeral v" for v]
      distrib_left [where a = "- numeral v" for v]
      div_by_1 div_0
      times_divide_eq_right times_divide_eq_left
      minus_divide_left [THEN sym] minus_divide_right [THEN sym]
      add_divide_distrib diff_divide_distrib
      of_int_minus of_int_diff
      of_int_of_nat_eq}
  #> Lin_Arith.add_simprocs [Int_Arith.zero_one_idom_simproc]
)\<close>

simproc_setup fast_arith
  ("(m::'a::linordered_idom) < n" |
    "(m::'a::linordered_idom) \<le> n" |
    "(m::'a::linordered_idom) = n") =
  \<open>K Lin_Arith.simproc\<close>


subsection\<open>More Inequality Reasoning\<close>

lemma zless_add1_eq: "w < z + 1 \<longleftrightarrow> w < z \<or> w = z"
  for w z :: int
  by arith

lemma add1_zle_eq: "w + 1 \<le> z \<longleftrightarrow> w < z"
  for w z :: int
  by arith

lemma zle_diff1_eq [simp]: "w \<le> z - 1 \<longleftrightarrow> w < z"
  for w z :: int
  by arith

lemma zle_add1_eq_le [simp]: "w < z + 1 \<longleftrightarrow> w \<le> z"
  for w z :: int
  by arith

lemma int_one_le_iff_zero_less: "1 \<le> z \<longleftrightarrow> 0 < z"
  for z :: int
  by arith

lemma Ints_nonzero_abs_ge1:
  fixes x:: "'a :: linordered_idom"
    assumes "x \<in> Ints" "x \<noteq> 0"
    shows "1 \<le> abs x"
proof (rule Ints_cases [OF \<open>x \<in> Ints\<close>])
  fix z::int
  assume "x = of_int z"
    with \<open>x \<noteq> 0\<close> 
  show "1 \<le> \<bar>x\<bar>"
    apply (auto simp add: abs_if)
    by (metis diff_0 of_int_1 of_int_le_iff of_int_minus zle_diff1_eq)
qed
  
lemma Ints_nonzero_abs_less1:
  fixes x:: "'a :: linordered_idom"
  shows "\<lbrakk>x \<in> Ints; abs x < 1\<rbrakk> \<Longrightarrow> x = 0"
    using Ints_nonzero_abs_ge1 [of x] by auto

lemma Ints_eq_abs_less1:
  fixes x:: "'a :: linordered_idom"
  shows "\<lbrakk>x \<in> Ints; y \<in> Ints\<rbrakk> \<Longrightarrow> x = y \<longleftrightarrow> abs (x-y) < 1"
  using eq_iff_diff_eq_0 by (fastforce intro: Ints_nonzero_abs_less1)
 

subsection \<open>The functions \<^term>\<open>nat\<close> and \<^term>\<open>int\<close>\<close>

text \<open>Simplify the term \<^term>\<open>w + - z\<close>.\<close>

lemma one_less_nat_eq [simp]: "Suc 0 < nat z \<longleftrightarrow> 1 < z"
  using zless_nat_conj [of 1 z] by auto

lemma int_eq_iff_numeral [simp]:
  "int m = numeral v \<longleftrightarrow> m = numeral v"
  by (simp add: int_eq_iff)

lemma nat_abs_int_diff:
  "nat \<bar>int a - int b\<bar> = (if a \<le> b then b - a else a - b)"
  by auto

lemma nat_int_add: "nat (int a + int b) = a + b"
  by auto

context ring_1
begin

lemma of_int_of_nat [nitpick_simp]:
  "of_int k = (if k < 0 then - of_nat (nat (- k)) else of_nat (nat k))"
proof (cases "k < 0")
  case True
  then have "0 \<le> - k" by simp
  then have "of_nat (nat (- k)) = of_int (- k)" by (rule of_nat_nat)
  with True show ?thesis by simp
next
  case False
  then show ?thesis by (simp add: not_less)
qed

end

lemma transfer_rule_of_int:
  includes lifting_syntax
  fixes R :: "'a::ring_1 \<Rightarrow> 'b::ring_1 \<Rightarrow> bool"
  assumes [transfer_rule]: "R 0 0" "R 1 1"
    "(R ===> R ===> R) (+) (+)"
    "(R ===> R) uminus uminus"
  shows "((=) ===> R) of_int of_int"
proof -
  note assms
  note transfer_rule_of_nat [transfer_rule]
  have [transfer_rule]: "((=) ===> R) of_nat of_nat"
    by transfer_prover
  show ?thesis
    by (unfold of_int_of_nat [abs_def]) transfer_prover
qed

lemma nat_mult_distrib:
  fixes z z' :: int
  assumes "0 \<le> z"
  shows "nat (z * z') = nat z * nat z'"
proof (cases "0 \<le> z'")
  case False
  with assms have "z * z' \<le> 0"
    by (simp add: not_le mult_le_0_iff)
  then have "nat (z * z') = 0" by simp
  moreover from False have "nat z' = 0" by simp
  ultimately show ?thesis by simp
next
  case True
  with assms have ge_0: "z * z' \<ge> 0" by (simp add: zero_le_mult_iff)
  show ?thesis
    by (rule injD [of "of_nat :: nat \<Rightarrow> int", OF inj_of_nat])
      (simp only: of_nat_mult of_nat_nat [OF True]
         of_nat_nat [OF assms] of_nat_nat [OF ge_0], simp)
qed

lemma nat_mult_distrib_neg:
  assumes "z \<le> (0::int)" shows "nat (z * z') = nat (- z) * nat (- z')" (is "?L = ?R")
proof -
  have "?L = nat (- z * - z')"
    using assms by auto
  also have "... = ?R"
    by (rule nat_mult_distrib) (use assms in auto)
  finally show ?thesis .
qed

lemma nat_abs_mult_distrib: "nat \<bar>w * z\<bar> = nat \<bar>w\<bar> * nat \<bar>z\<bar>"
  by (cases "z = 0 \<or> w = 0")
    (auto simp add: abs_if nat_mult_distrib [symmetric]
      nat_mult_distrib_neg [symmetric] mult_less_0_iff)

lemma int_in_range_abs [simp]: "int n \<in> range abs"
proof (rule range_eqI)
  show "int n = \<bar>int n\<bar>" by simp
qed

lemma range_abs_Nats [simp]: "range abs = (\<nat> :: int set)"
proof -
  have "\<bar>k\<bar> \<in> \<nat>" for k :: int
    by (cases k) simp_all
  moreover have "k \<in> range abs" if "k \<in> \<nat>" for k :: int
    using that by induct simp
  ultimately show ?thesis by blast
qed

lemma Suc_nat_eq_nat_zadd1: "0 \<le> z \<Longrightarrow> Suc (nat z) = nat (1 + z)"
  for z :: int
  by (rule sym) (simp add: nat_eq_iff)

lemma diff_nat_eq_if:
  "nat z - nat z' =
    (if z' < 0 then nat z
     else
      let d = z - z'
      in if d < 0 then 0 else nat d)"
  by (simp add: Let_def nat_diff_distrib [symmetric])

lemma nat_numeral_diff_1 [simp]: "numeral v - (1::nat) = nat (numeral v - 1)"
  using diff_nat_numeral [of v Num.One] by simp


subsection \<open>Induction principles for int\<close>

text \<open>Well-founded segments of the integers.\<close>

definition int_ge_less_than :: "int \<Rightarrow> (int \<times> int) set"
  where "int_ge_less_than d = {(z', z). d \<le> z' \<and> z' < z}"

lemma wf_int_ge_less_than: "wf (int_ge_less_than d)"
proof -
  have "int_ge_less_than d \<subseteq> measure (\<lambda>z. nat (z - d))"
    by (auto simp add: int_ge_less_than_def)
  then show ?thesis
    by (rule wf_subset [OF wf_measure])
qed

text \<open>
  This variant looks odd, but is typical of the relations suggested
  by RankFinder.\<close>

definition int_ge_less_than2 :: "int \<Rightarrow> (int \<times> int) set"
  where "int_ge_less_than2 d = {(z',z). d \<le> z \<and> z' < z}"

lemma wf_int_ge_less_than2: "wf (int_ge_less_than2 d)"
proof -
  have "int_ge_less_than2 d \<subseteq> measure (\<lambda>z. nat (1 + z - d))"
    by (auto simp add: int_ge_less_than2_def)
  then show ?thesis
    by (rule wf_subset [OF wf_measure])
qed

(* `set:int': dummy construction *)
theorem int_ge_induct [case_names base step, induct set: int]:
  fixes i :: int
  assumes ge: "k \<le> i"
    and base: "P k"
    and step: "\<And>i. k \<le> i \<Longrightarrow> P i \<Longrightarrow> P (i + 1)"
  shows "P i"
proof -
  have "\<And>i::int. n = nat (i - k) \<Longrightarrow> k \<le> i \<Longrightarrow> P i" for n
  proof (induct n)
    case 0
    then have "i = k" by arith
    with base show "P i" by simp
  next
    case (Suc n)
    then have "n = nat ((i - 1) - k)" by arith
    moreover have k: "k \<le> i - 1" using Suc.prems by arith
    ultimately have "P (i - 1)" by (rule Suc.hyps)
    from step [OF k this] show ?case by simp
  qed
  with ge show ?thesis by fast
qed

(* `set:int': dummy construction *)
theorem int_gr_induct [case_names base step, induct set: int]:
  fixes i k :: int
  assumes "k < i" "P (k + 1)" "\<And>i. k < i \<Longrightarrow> P i \<Longrightarrow> P (i + 1)"
  shows "P i"
proof -
  have "k+1 \<le> i"
    using assms by auto
  then show ?thesis
    by (induction i rule: int_ge_induct) (auto simp: assms)
qed

theorem int_le_induct [consumes 1, case_names base step]:
  fixes i k :: int
  assumes le: "i \<le> k"
    and base: "P k"
    and step: "\<And>i. i \<le> k \<Longrightarrow> P i \<Longrightarrow> P (i - 1)"
  shows "P i"
proof -
  have "\<And>i::int. n = nat(k-i) \<Longrightarrow> i \<le> k \<Longrightarrow> P i" for n
  proof (induct n)
    case 0
    then have "i = k" by arith
    with base show "P i" by simp
  next
    case (Suc n)
    then have "n = nat (k - (i + 1))" by arith
    moreover have k: "i + 1 \<le> k" using Suc.prems by arith
    ultimately have "P (i + 1)" by (rule Suc.hyps)
    from step[OF k this] show ?case by simp
  qed
  with le show ?thesis by fast
qed

theorem int_less_induct [consumes 1, case_names base step]:
  fixes i k :: int
  assumes "i < k" "P (k - 1)" "\<And>i. i < k \<Longrightarrow> P i \<Longrightarrow> P (i - 1)"
  shows "P i"
proof -
  have "i \<le> k-1"
    using assms by auto
  then show ?thesis
    by (induction i rule: int_le_induct) (auto simp: assms)
qed

theorem int_induct [case_names base step1 step2]:
  fixes k :: int
  assumes base: "P k"
    and step1: "\<And>i. k \<le> i \<Longrightarrow> P i \<Longrightarrow> P (i + 1)"
    and step2: "\<And>i. k \<ge> i \<Longrightarrow> P i \<Longrightarrow> P (i - 1)"
  shows "P i"
proof -
  have "i \<le> k \<or> i \<ge> k" by arith
  then show ?thesis
  proof
    assume "i \<ge> k"
    then show ?thesis
      using base by (rule int_ge_induct) (fact step1)
  next
    assume "i \<le> k"
    then show ?thesis
      using base by (rule int_le_induct) (fact step2)
  qed
qed


subsection \<open>Intermediate value theorems\<close>

lemma nat_ivt_aux: 
  "\<lbrakk>\<forall>i<n. \<bar>f (Suc i) - f i\<bar> \<le> 1; f 0 \<le> k; k \<le> f n\<rbrakk> \<Longrightarrow> \<exists>i \<le> n. f i = k"
  for m n :: nat and k :: int
proof (induct n)
  case (Suc n)
  show ?case
  proof (cases "k = f (Suc n)")
    case False
    with Suc have "k \<le> f n"
      by auto
    with Suc show ?thesis
      by (auto simp add: abs_if split: if_split_asm intro: le_SucI)
  qed (use Suc in auto)
qed auto

lemma nat_intermed_int_val:
  fixes m n :: nat and k :: int
  assumes "\<forall>i. m \<le> i \<and> i < n \<longrightarrow> \<bar>f (Suc i) - f i\<bar> \<le> 1" "m \<le> n" "f m \<le> k" "k \<le> f n"
  shows "\<exists>i. m \<le> i \<and> i \<le> n \<and> f i = k"
proof -
  obtain i where "i \<le> n - m" "k = f (m + i)"
    using nat_ivt_aux [of "n - m" "f \<circ> plus m" k] assms by auto
  with assms show ?thesis
    by (rule_tac x = "m + i" in exI) auto
qed

lemma nat0_intermed_int_val:
  "\<exists>i\<le>n. f i = k"
  if "\<forall>i<n. \<bar>f (i + 1) - f i\<bar> \<le> 1" "f 0 \<le> k" "k \<le> f n"
  for n :: nat and k :: int
  using nat_intermed_int_val [of 0 n f k] that by auto


subsection \<open>Products and 1, by T. M. Rasmussen\<close>

lemma abs_zmult_eq_1:
  fixes m n :: int
  assumes mn: "\<bar>m * n\<bar> = 1"
  shows "\<bar>m\<bar> = 1"
proof -
  from mn have 0: "m \<noteq> 0" "n \<noteq> 0" by auto
  have "\<not> 2 \<le> \<bar>m\<bar>"
  proof
    assume "2 \<le> \<bar>m\<bar>"
    then have "2 * \<bar>n\<bar> \<le> \<bar>m\<bar> * \<bar>n\<bar>" by (simp add: mult_mono 0)
    also have "\<dots> = \<bar>m * n\<bar>" by (simp add: abs_mult)
    also from mn have "\<dots> = 1" by simp
    finally have "2 * \<bar>n\<bar> \<le> 1" .
    with 0 show "False" by arith
  qed
  with 0 show ?thesis by auto
qed

lemma pos_zmult_eq_1_iff_lemma: "m * n = 1 \<Longrightarrow> m = 1 \<or> m = - 1"
  for m n :: int
  using abs_zmult_eq_1 [of m n] by arith

lemma pos_zmult_eq_1_iff:
  fixes m n :: int
  assumes "0 < m"
  shows "m * n = 1 \<longleftrightarrow> m = 1 \<and> n = 1"
proof -
  from assms have "m * n = 1 \<Longrightarrow> m = 1"
    by (auto dest: pos_zmult_eq_1_iff_lemma)
  then show ?thesis
    by (auto dest: pos_zmult_eq_1_iff_lemma)
qed

lemma zmult_eq_1_iff: "m * n = 1 \<longleftrightarrow> (m = 1 \<and> n = 1) \<or> (m = - 1 \<and> n = - 1)" (is "?L = ?R")
  for m n :: int
proof
  assume L: ?L show ?R
    using pos_zmult_eq_1_iff_lemma [OF L] L by force
qed auto

lemma infinite_UNIV_int [simp]: "\<not> finite (UNIV::int set)"
proof
  assume "finite (UNIV::int set)"
  moreover have "inj (\<lambda>i::int. 2 * i)"
    by (rule injI) simp
  ultimately have "surj (\<lambda>i::int. 2 * i)"
    by (rule finite_UNIV_inj_surj)
  then obtain i :: int where "1 = 2 * i" by (rule surjE)
  then show False by (simp add: pos_zmult_eq_1_iff)
qed


subsection \<open>The divides relation\<close>

lemma zdvd_antisym_nonneg: "0 \<le> m \<Longrightarrow> 0 \<le> n \<Longrightarrow> m dvd n \<Longrightarrow> n dvd m \<Longrightarrow> m = n"
  for m n :: int
  by (auto simp add: dvd_def mult.assoc zero_le_mult_iff zmult_eq_1_iff)

lemma zdvd_antisym_abs:
  fixes a b :: int
  assumes "a dvd b" and "b dvd a"
  shows "\<bar>a\<bar> = \<bar>b\<bar>"
proof (cases "a = 0")
  case True
  with assms show ?thesis by simp
next
  case False
  from \<open>a dvd b\<close> obtain k where k: "b = a * k"
    unfolding dvd_def by blast
  from \<open>b dvd a\<close> obtain k' where k': "a = b * k'"
    unfolding dvd_def by blast
  from k k' have "a = a * k * k'" by simp
  with mult_cancel_left1[where c="a" and b="k*k'"] have kk': "k * k' = 1"
    using \<open>a \<noteq> 0\<close> by (simp add: mult.assoc)
  then have "k = 1 \<and> k' = 1 \<or> k = -1 \<and> k' = -1"
    by (simp add: zmult_eq_1_iff)
  with k k' show ?thesis by auto
qed

lemma zdvd_zdiffD: "k dvd m - n \<Longrightarrow> k dvd n \<Longrightarrow> k dvd m"
  for k m n :: int
  using dvd_add_right_iff [of k "- n" m] by simp

lemma zdvd_reduce: "k dvd n + k * m \<longleftrightarrow> k dvd n"
  for k m n :: int
  using dvd_add_times_triv_right_iff [of k n m] by (simp add: ac_simps)

lemma dvd_imp_le_int:
  fixes d i :: int
  assumes "i \<noteq> 0" and "d dvd i"
  shows "\<bar>d\<bar> \<le> \<bar>i\<bar>"
proof -
  from \<open>d dvd i\<close> obtain k where "i = d * k" ..
  with \<open>i \<noteq> 0\<close> have "k \<noteq> 0" by auto
  then have "1 \<le> \<bar>k\<bar>" and "0 \<le> \<bar>d\<bar>" by auto
  then have "\<bar>d\<bar> * 1 \<le> \<bar>d\<bar> * \<bar>k\<bar>" by (rule mult_left_mono)
  with \<open>i = d * k\<close> show ?thesis by (simp add: abs_mult)
qed

lemma zdvd_not_zless:
  fixes m n :: int
  assumes "0 < m" and "m < n"
  shows "\<not> n dvd m"
proof
  from assms have "0 < n" by auto
  assume "n dvd m" then obtain k where k: "m = n * k" ..
  with \<open>0 < m\<close> have "0 < n * k" by auto
  with \<open>0 < n\<close> have "0 < k" by (simp add: zero_less_mult_iff)
  with k \<open>0 < n\<close> \<open>m < n\<close> have "n * k < n * 1" by simp
  with \<open>0 < n\<close> \<open>0 < k\<close> show False unfolding mult_less_cancel_left by auto
qed

lemma zdvd_mult_cancel:
  fixes k m n :: int
  assumes d: "k * m dvd k * n"
    and "k \<noteq> 0"
  shows "m dvd n"
proof -
  from d obtain h where h: "k * n = k * m * h"
    unfolding dvd_def by blast
  have "n = m * h"
  proof (rule ccontr)
    assume "\<not> ?thesis"
    with \<open>k \<noteq> 0\<close> have "k * n \<noteq> k * (m * h)" by simp
    with h show False
      by (simp add: mult.assoc)
  qed
  then show ?thesis by simp
qed

lemma int_dvd_int_iff [simp]:
  "int m dvd int n \<longleftrightarrow> m dvd n"
proof -
  have "m dvd n" if "int n = int m * k" for k
  proof (cases k)
    case (nonneg q)
    with that have "n = m * q"
      by (simp del: of_nat_mult add: of_nat_mult [symmetric])
    then show ?thesis ..
  next
    case (neg q)
    with that have "int n = int m * (- int (Suc q))"
      by simp
    also have "\<dots> = - (int m * int (Suc q))"
      by (simp only: mult_minus_right)
    also have "\<dots> = - int (m * Suc q)"
      by (simp only: of_nat_mult [symmetric])
    finally have "- int (m * Suc q) = int n" ..
    then show ?thesis
      by (simp only: negative_eq_positive) auto
  qed
  then show ?thesis by (auto simp add: dvd_def)
qed

lemma dvd_nat_abs_iff [simp]:
  "n dvd nat \<bar>k\<bar> \<longleftrightarrow> int n dvd k"
proof -
  have "n dvd nat \<bar>k\<bar> \<longleftrightarrow> int n dvd int (nat \<bar>k\<bar>)"
    by (simp only: int_dvd_int_iff)
  then show ?thesis
    by simp
qed

lemma nat_abs_dvd_iff [simp]:
  "nat \<bar>k\<bar> dvd n \<longleftrightarrow> k dvd int n"
proof -
  have "nat \<bar>k\<bar> dvd n \<longleftrightarrow> int (nat \<bar>k\<bar>) dvd int n"
    by (simp only: int_dvd_int_iff)
  then show ?thesis
    by simp
qed

lemma zdvd1_eq [simp]: "x dvd 1 \<longleftrightarrow> \<bar>x\<bar> = 1" (is "?lhs \<longleftrightarrow> ?rhs")
  for x :: int
proof
  assume ?lhs
  then have "nat \<bar>x\<bar> dvd nat \<bar>1\<bar>"
    by (simp only: nat_abs_dvd_iff) simp
  then have "nat \<bar>x\<bar> = 1"
    by simp
  then show ?rhs
    by (cases "x < 0") simp_all
next
  assume ?rhs
  then have "x = 1 \<or> x = - 1"
    by auto
  then show ?lhs
    by (auto intro: dvdI)
qed

lemma zdvd_mult_cancel1:
  fixes m :: int
  assumes mp: "m \<noteq> 0"
  shows "m * n dvd m \<longleftrightarrow> \<bar>n\<bar> = 1"
    (is "?lhs \<longleftrightarrow> ?rhs")
proof
  assume ?rhs
  then show ?lhs
    by (cases "n > 0") (auto simp add: minus_equation_iff)
next
  assume ?lhs
  then have "m * n dvd m * 1" by simp
  from zdvd_mult_cancel[OF this mp] show ?rhs
    by (simp only: zdvd1_eq)
qed

lemma nat_dvd_iff: "nat z dvd m \<longleftrightarrow> (if 0 \<le> z then z dvd int m else m = 0)"
  using nat_abs_dvd_iff [of z m] by (cases "z \<ge> 0") auto

lemma eq_nat_nat_iff: "0 \<le> z \<Longrightarrow> 0 \<le> z' \<Longrightarrow> nat z = nat z' \<longleftrightarrow> z = z'"
  by (auto elim: nonneg_int_cases)

lemma nat_power_eq: "0 \<le> z \<Longrightarrow> nat (z ^ n) = nat z ^ n"
  by (induct n) (simp_all add: nat_mult_distrib)

lemma numeral_power_eq_nat_cancel_iff [simp]:
  "numeral x ^ n = nat y \<longleftrightarrow> numeral x ^ n = y"
  using nat_eq_iff2 by auto

lemma nat_eq_numeral_power_cancel_iff [simp]:
  "nat y = numeral x ^ n \<longleftrightarrow> y = numeral x ^ n"
  using numeral_power_eq_nat_cancel_iff[of x n y]
  by (metis (mono_tags))

lemma numeral_power_le_nat_cancel_iff [simp]:
  "numeral x ^ n \<le> nat a \<longleftrightarrow> numeral x ^ n \<le> a"
  using nat_le_eq_zle[of "numeral x ^ n" a]
  by (auto simp: nat_power_eq)

lemma nat_le_numeral_power_cancel_iff [simp]:
  "nat a \<le> numeral x ^ n \<longleftrightarrow> a \<le> numeral x ^ n"
  by (simp add: nat_le_iff)

lemma numeral_power_less_nat_cancel_iff [simp]:
  "numeral x ^ n < nat a \<longleftrightarrow> numeral x ^ n < a"
  using nat_less_eq_zless[of "numeral x ^ n" a]
  by (auto simp: nat_power_eq)

lemma nat_less_numeral_power_cancel_iff [simp]:
  "nat a < numeral x ^ n \<longleftrightarrow> a < numeral x ^ n"
  using nat_less_eq_zless[of a "numeral x ^ n"]
  by (cases "a < 0") (auto simp: nat_power_eq less_le_trans[where y=0])

lemma zdvd_imp_le: "z \<le> n" if "z dvd n" "0 < n" for n z :: int
proof (cases n)
  case (nonneg n)
  show ?thesis
    by (cases z) (use nonneg dvd_imp_le that in auto)
qed (use that in auto)

lemma zdvd_period:
  fixes a d :: int
  assumes "a dvd d"
  shows "a dvd (x + t) \<longleftrightarrow> a dvd ((x + c * d) + t)"
    (is "?lhs \<longleftrightarrow> ?rhs")
proof -
  from assms have "a dvd (x + t) \<longleftrightarrow> a dvd ((x + t) + c * d)"
    by (simp add: dvd_add_left_iff)
  then show ?thesis
    by (simp add: ac_simps)
qed


subsection \<open>Powers with integer exponents\<close>

text \<open>
  The following allows writing powers with an integer exponent. While the type signature
  is very generic, most theorems will assume that the underlying type is a division ring or
  a field.

  The notation `powi' is inspired by the `powr' notation for real/complex exponentiation.
\<close>
definition power_int :: "'a :: {inverse, power} \<Rightarrow> int \<Rightarrow> 'a" (infixr "powi" 80) where
  "power_int x n = (if n \<ge> 0 then x ^ nat n else inverse x ^ (nat (-n)))"

lemma power_int_0_right [simp]: "power_int x 0 = 1"
  and power_int_1_right [simp]:
        "power_int (y :: 'a :: {power, inverse, monoid_mult}) 1 = y"
  and power_int_minus1_right [simp]:
        "power_int (y :: 'a :: {power, inverse, monoid_mult}) (-1) = inverse y"
  by (simp_all add: power_int_def)

lemma power_int_of_nat [simp]: "power_int x (int n) = x ^ n"
  by (simp add: power_int_def)

lemma power_int_numeral [simp]: "power_int x (numeral n) = x ^ numeral n"
  by (simp add: power_int_def)

lemma int_cases4 [case_names nonneg neg]:
  fixes m :: int
  obtains n where "m = int n" | n where "n > 0" "m = -int n"
proof (cases "m \<ge> 0")
  case True
  thus ?thesis using that(1)[of "nat m"] by auto
next
  case False
  thus ?thesis using that(2)[of "nat (-m)"] by auto
qed


context
  assumes "SORT_CONSTRAINT('a::division_ring)"
begin

lemma power_int_minus: "power_int (x::'a) (-n) = inverse (power_int x n)"
  by (auto simp: power_int_def power_inverse)

lemma power_int_eq_0_iff [simp]: "power_int (x::'a) n = 0 \<longleftrightarrow> x = 0 \<and> n \<noteq> 0"
  by (auto simp: power_int_def)

lemma power_int_0_left_If: "power_int (0 :: 'a) m = (if m = 0 then 1 else 0)"
  by (auto simp: power_int_def)

lemma power_int_0_left [simp]: "m \<noteq> 0 \<Longrightarrow> power_int (0 :: 'a) m = 0"
  by (simp add: power_int_0_left_If)

lemma power_int_1_left [simp]: "power_int 1 n = (1 :: 'a :: division_ring)"
  by (auto simp: power_int_def) 

lemma power_diff_conv_inverse: "x \<noteq> 0 \<Longrightarrow> m \<le> n \<Longrightarrow> (x :: 'a) ^ (n - m) = x ^ n * inverse x ^ m"
  by (simp add: field_simps flip: power_add)

lemma power_mult_inverse_distrib: "x ^ m * inverse (x :: 'a) = inverse x * x ^ m"
proof (cases "x = 0")
  case [simp]: False
  show ?thesis
  proof (cases m)
    case (Suc m')
    have "x ^ Suc m' * inverse x = x ^ m'"
      by (subst power_Suc2) (auto simp: mult.assoc)
    also have "\<dots> = inverse x * x ^ Suc m'"
      by (subst power_Suc) (auto simp: mult.assoc [symmetric])
    finally show ?thesis using Suc by simp
  qed auto
qed auto

lemma power_mult_power_inverse_commute:
  "x ^ m * inverse (x :: 'a) ^ n = inverse x ^ n * x ^ m"
proof (induction n)
  case (Suc n)
  have "x ^ m * inverse x ^ Suc n = (x ^ m * inverse x ^ n) * inverse x"
    by (simp only: power_Suc2 mult.assoc)
  also have "x ^ m * inverse x ^ n = inverse x ^ n * x ^ m"
    by (rule Suc)
  also have "\<dots> * inverse x = (inverse x ^ n * inverse x) * x ^ m"
    by (simp add: mult.assoc power_mult_inverse_distrib)
  also have "\<dots> = inverse x ^ (Suc n) * x ^ m"
    by (simp only: power_Suc2)
  finally show ?case .
qed auto

lemma power_int_add:
  assumes "x \<noteq> 0 \<or> m + n \<noteq> 0"
  shows   "power_int (x::'a) (m + n) = power_int x m * power_int x n"
proof (cases "x = 0")
  case True
  thus ?thesis using assms by (auto simp: power_int_0_left_If)
next
  case [simp]: False
  show ?thesis
  proof (cases m n rule: int_cases4[case_product int_cases4])
    case (nonneg_nonneg a b)
    thus ?thesis
      by (auto simp: power_int_def nat_add_distrib power_add)
  next
    case (nonneg_neg a b)
    thus ?thesis
      by (auto simp: power_int_def nat_diff_distrib not_le power_diff_conv_inverse
                     power_mult_power_inverse_commute)
  next
    case (neg_nonneg a b)
    thus ?thesis
      by (auto simp: power_int_def nat_diff_distrib not_le power_diff_conv_inverse
                     power_mult_power_inverse_commute)    
  next
    case (neg_neg a b)
    thus ?thesis
      by (auto simp: power_int_def nat_add_distrib add.commute simp flip: power_add)
  qed
qed

lemma power_int_add_1:
  assumes "x \<noteq> 0 \<or> m \<noteq> -1"
  shows   "power_int (x::'a) (m + 1) = power_int x m * x"
  using assms by (subst power_int_add) auto

lemma power_int_add_1':
  assumes "x \<noteq> 0 \<or> m \<noteq> -1"
  shows   "power_int (x::'a) (m + 1) = x * power_int x m"
  using assms by (subst add.commute, subst power_int_add) auto

lemma power_int_commutes: "power_int (x :: 'a) n * x = x * power_int x n"
  by (cases "x = 0") (auto simp flip: power_int_add_1 power_int_add_1')

lemma power_int_inverse [field_simps, field_split_simps, divide_simps]:
  "power_int (inverse (x :: 'a)) n = inverse (power_int x n)"
  by (auto simp: power_int_def power_inverse)

lemma power_int_mult: "power_int (x :: 'a) (m * n) = power_int (power_int x m) n"
  by (auto simp: power_int_def zero_le_mult_iff simp flip: power_mult power_inverse nat_mult_distrib)

end

context
  assumes "SORT_CONSTRAINT('a::field)"
begin

lemma power_int_diff:
  assumes "x \<noteq> 0 \<or> m \<noteq> n"
  shows   "power_int (x::'a) (m - n) = power_int x m / power_int x n"
  using power_int_add[of x m "-n"] assms by (auto simp: field_simps power_int_minus)

lemma power_int_minus_mult: "x \<noteq> 0 \<or> n \<noteq> 0 \<Longrightarrow> power_int (x :: 'a) (n - 1) * x = power_int x n"
  by (auto simp flip: power_int_add_1)  

lemma power_int_mult_distrib: "power_int (x * y :: 'a) m = power_int x m * power_int y m"
  by (auto simp: power_int_def power_mult_distrib)

lemmas power_int_mult_distrib_numeral1 = power_int_mult_distrib [where x = "numeral w" for w, simp]
lemmas power_int_mult_distrib_numeral2 = power_int_mult_distrib [where y = "numeral w" for w, simp]

lemma power_int_divide_distrib: "power_int (x / y :: 'a) m = power_int x m / power_int y m"
  using power_int_mult_distrib[of x "inverse y" m] unfolding power_int_inverse
  by (simp add: field_simps)

end


lemma power_int_add_numeral [simp]:
  "power_int x (numeral m) * power_int x (numeral n) = power_int x (numeral (m + n))"
  for x :: "'a :: division_ring"
  by (simp add: power_int_add [symmetric])

lemma power_int_add_numeral2 [simp]:
  "power_int x (numeral m) * (power_int x (numeral n) * b) = power_int x (numeral (m + n)) * b"
  for x :: "'a :: division_ring"
  by (simp add: mult.assoc [symmetric])

lemma power_int_mult_numeral [simp]:
  "power_int (power_int x (numeral m)) (numeral n) = power_int x (numeral (m * n))"
  for x :: "'a :: division_ring"
  by (simp only: numeral_mult power_int_mult)
  
lemma power_int_not_zero: "(x :: 'a :: division_ring) \<noteq> 0 \<or> n = 0 \<Longrightarrow> power_int x n \<noteq> 0"
  by (subst power_int_eq_0_iff) auto

lemma power_int_one_over [field_simps, field_split_simps, divide_simps]:
  "power_int (1 / x :: 'a :: division_ring) n = 1 / power_int x n"
  using power_int_inverse[of x] by (simp add: divide_inverse)


context
  assumes "SORT_CONSTRAINT('a :: linordered_field)"
begin

lemma power_int_numeral_neg_numeral [simp]:
  "power_int (numeral m) (-numeral n) = (inverse (numeral (Num.pow m n)) :: 'a)"
  by (simp add: power_int_minus)

lemma zero_less_power_int [simp]: "0 < (x :: 'a) \<Longrightarrow> 0 < power_int x n"
  by (auto simp: power_int_def)

lemma zero_le_power_int [simp]: "0 \<le> (x :: 'a) \<Longrightarrow> 0 \<le> power_int x n"
  by (auto simp: power_int_def)

lemma power_int_mono: "(x :: 'a) \<le> y \<Longrightarrow> n \<ge> 0 \<Longrightarrow> 0 \<le> x \<Longrightarrow> power_int x n \<le> power_int y n"
  by (cases n rule: int_cases4) (auto intro: power_mono)

lemma one_le_power_int [simp]: "1 \<le> (x :: 'a) \<Longrightarrow> n \<ge> 0 \<Longrightarrow> 1 \<le> power_int x n"
  using power_int_mono [of 1 x n] by simp

lemma power_int_le_one: "0 \<le> (x :: 'a) \<Longrightarrow> n \<ge> 0 \<Longrightarrow> x \<le> 1 \<Longrightarrow> power_int x n \<le> 1"
  using power_int_mono [of x 1 n] by simp

lemma power_int_le_imp_le_exp:
  assumes gt1: "1 < (x :: 'a :: linordered_field)"
  assumes "power_int x m \<le> power_int x n" "n \<ge> 0"
  shows   "m \<le> n"
proof (cases "m < 0")
  case True
  with \<open>n \<ge> 0\<close> show ?thesis by simp
next
  case False
  with assms have "x ^ nat m \<le> x ^ nat n"
    by (simp add: power_int_def)
  from gt1 and this show ?thesis
    using False \<open>n \<ge> 0\<close> by auto
qed

lemma power_int_le_imp_less_exp:
  assumes gt1: "1 < (x :: 'a :: linordered_field)"
  assumes "power_int x m < power_int x n" "n \<ge> 0"
  shows   "m < n"
proof (cases "m < 0")
  case True
  with \<open>n \<ge> 0\<close> show ?thesis by simp
next
  case False
  with assms have "x ^ nat m < x ^ nat n"
    by (simp add: power_int_def)
  from gt1 and this show ?thesis
    using False \<open>n \<ge> 0\<close> by auto
qed

lemma power_int_strict_mono:
  "(a :: 'a :: linordered_field) < b \<Longrightarrow> 0 \<le> a \<Longrightarrow> 0 < n \<Longrightarrow> power_int a n < power_int b n"
  by (auto simp: power_int_def intro!: power_strict_mono)

lemma power_int_mono_iff [simp]:
  fixes a b :: "'a :: linordered_field"
  shows "\<lbrakk>a \<ge> 0; b \<ge> 0; n > 0\<rbrakk> \<Longrightarrow> power_int a n \<le> power_int b n \<longleftrightarrow> a \<le> b"
  by (auto simp: power_int_def intro!: power_strict_mono)

lemma power_int_strict_increasing:
  fixes a :: "'a :: linordered_field"
  assumes "n < N" "1 < a"
  shows   "power_int a N > power_int a n"
proof -
  have *: "a ^ nat (N - n) > a ^ 0"
    using assms by (intro power_strict_increasing) auto
  have "power_int a N = power_int a n * power_int a (N - n)"
    using assms by (simp flip: power_int_add)
  also have "\<dots> > power_int a n * 1"
    using assms *
    by (intro mult_strict_left_mono zero_less_power_int) (auto simp: power_int_def)
  finally show ?thesis by simp
qed

lemma power_int_increasing:
  fixes a :: "'a :: linordered_field"
  assumes "n \<le> N" "a \<ge> 1"
  shows   "power_int a N \<ge> power_int a n"
proof -
  have *: "a ^ nat (N - n) \<ge> a ^ 0"
    using assms by (intro power_increasing) auto
  have "power_int a N = power_int a n * power_int a (N - n)"
    using assms by (simp flip: power_int_add)
  also have "\<dots> \<ge> power_int a n * 1"
    using assms * by (intro mult_left_mono) (auto simp: power_int_def)
  finally show ?thesis by simp
qed

lemma power_int_strict_decreasing:
  fixes a :: "'a :: linordered_field"
  assumes "n < N" "0 < a" "a < 1"
  shows   "power_int a N < power_int a n"
proof -
  have *: "a ^ nat (N - n) < a ^ 0"
    using assms by (intro power_strict_decreasing) auto
  have "power_int a N = power_int a n * power_int a (N - n)"
    using assms by (simp flip: power_int_add)
  also have "\<dots> < power_int a n * 1"
    using assms *
    by (intro mult_strict_left_mono zero_less_power_int) (auto simp: power_int_def)
  finally show ?thesis by simp
qed

lemma power_int_decreasing:
  fixes a :: "'a :: linordered_field"
  assumes "n \<le> N" "0 \<le> a" "a \<le> 1" "a \<noteq> 0 \<or> N \<noteq> 0 \<or> n = 0"
  shows   "power_int a N \<le> power_int a n"
proof (cases "a = 0")
  case False
  have *: "a ^ nat (N - n) \<le> a ^ 0"
    using assms by (intro power_decreasing) auto
  have "power_int a N = power_int a n * power_int a (N - n)"
    using assms False by (simp flip: power_int_add)
  also have "\<dots> \<le> power_int a n * 1"
    using assms * by (intro mult_left_mono) (auto simp: power_int_def)
  finally show ?thesis by simp
qed (use assms in \<open>auto simp: power_int_0_left_If\<close>)

lemma one_less_power_int: "1 < (a :: 'a) \<Longrightarrow> 0 < n \<Longrightarrow> 1 < power_int a n"
  using power_int_strict_increasing[of 0 n a] by simp

lemma power_int_abs: "\<bar>power_int a n :: 'a\<bar> = power_int \<bar>a\<bar> n"
  by (auto simp: power_int_def power_abs)

lemma power_int_sgn [simp]: "sgn (power_int a n :: 'a) = power_int (sgn a) n"
  by (auto simp: power_int_def)

lemma abs_power_int_minus [simp]: "\<bar>power_int (- a) n :: 'a\<bar> = \<bar>power_int a n\<bar>"
  by (simp add: power_int_abs)

lemma power_int_strict_antimono:
  assumes "(a :: 'a :: linordered_field) < b" "0 < a" "n < 0"
  shows   "power_int a n > power_int b n"
proof -
  have "inverse (power_int a (-n)) > inverse (power_int b (-n))"
    using assms by (intro less_imp_inverse_less power_int_strict_mono zero_less_power_int) auto
  thus ?thesis by (simp add: power_int_minus)
qed

lemma power_int_antimono:
  assumes "(a :: 'a :: linordered_field) \<le> b" "0 < a" "n < 0"
  shows   "power_int a n \<ge> power_int b n"
  using power_int_strict_antimono[of a b n] assms by (cases "a = b") auto

end


subsection \<open>Finiteness of intervals\<close>

lemma finite_interval_int1 [iff]: "finite {i :: int. a \<le> i \<and> i \<le> b}"
proof (cases "a \<le> b")
  case True
  then show ?thesis
  proof (induct b rule: int_ge_induct)
    case base
    have "{i. a \<le> i \<and> i \<le> a} = {a}" by auto
    then show ?case by simp
  next
    case (step b)
    then have "{i. a \<le> i \<and> i \<le> b + 1} = {i. a \<le> i \<and> i \<le> b} \<union> {b + 1}" by auto
    with step show ?case by simp
  qed
next
  case False
  then show ?thesis
    by (metis (lifting, no_types) Collect_empty_eq finite.emptyI order_trans)
qed

lemma finite_interval_int2 [iff]: "finite {i :: int. a \<le> i \<and> i < b}"
  by (rule rev_finite_subset[OF finite_interval_int1[of "a" "b"]]) auto

lemma finite_interval_int3 [iff]: "finite {i :: int. a < i \<and> i \<le> b}"
  by (rule rev_finite_subset[OF finite_interval_int1[of "a" "b"]]) auto

lemma finite_interval_int4 [iff]: "finite {i :: int. a < i \<and> i < b}"
  by (rule rev_finite_subset[OF finite_interval_int1[of "a" "b"]]) auto


subsection \<open>Configuration of the code generator\<close>

text \<open>Constructors\<close>

definition Pos :: "num \<Rightarrow> int"
  where [simp, code_abbrev]: "Pos = numeral"

definition Neg :: "num \<Rightarrow> int"
  where [simp, code_abbrev]: "Neg n = - (Pos n)"

code_datatype "0::int" Pos Neg


text \<open>Auxiliary operations.\<close>

definition dup :: "int \<Rightarrow> int"
  where [simp]: "dup k = k + k"

lemma dup_code [code]:
  "dup 0 = 0"
  "dup (Pos n) = Pos (Num.Bit0 n)"
  "dup (Neg n) = Neg (Num.Bit0 n)"
  by (simp_all add: numeral_Bit0)

definition sub :: "num \<Rightarrow> num \<Rightarrow> int"
  where [simp]: "sub m n = numeral m - numeral n"

lemma sub_code [code]:
  "sub Num.One Num.One = 0"
  "sub (Num.Bit0 m) Num.One = Pos (Num.BitM m)"
  "sub (Num.Bit1 m) Num.One = Pos (Num.Bit0 m)"
  "sub Num.One (Num.Bit0 n) = Neg (Num.BitM n)"
  "sub Num.One (Num.Bit1 n) = Neg (Num.Bit0 n)"
  "sub (Num.Bit0 m) (Num.Bit0 n) = dup (sub m n)"
  "sub (Num.Bit1 m) (Num.Bit1 n) = dup (sub m n)"
  "sub (Num.Bit1 m) (Num.Bit0 n) = dup (sub m n) + 1"
  "sub (Num.Bit0 m) (Num.Bit1 n) = dup (sub m n) - 1"
  by (simp_all only: sub_def dup_def numeral.simps Pos_def Neg_def numeral_BitM)

lemma sub_BitM_One_eq:
  \<open>(Num.sub (Num.BitM n) num.One) = 2 * (Num.sub n Num.One :: int)\<close>
  by (cases n) simp_all

text \<open>Implementations.\<close>

lemma one_int_code [code]: "1 = Pos Num.One"
  by simp

lemma plus_int_code [code]:
  "k + 0 = k"
  "0 + l = l"
  "Pos m + Pos n = Pos (m + n)"
  "Pos m + Neg n = sub m n"
  "Neg m + Pos n = sub n m"
  "Neg m + Neg n = Neg (m + n)"
  for k l :: int
  by simp_all

lemma uminus_int_code [code]:
  "uminus 0 = (0::int)"
  "uminus (Pos m) = Neg m"
  "uminus (Neg m) = Pos m"
  by simp_all

lemma minus_int_code [code]:
  "k - 0 = k"
  "0 - l = uminus l"
  "Pos m - Pos n = sub m n"
  "Pos m - Neg n = Pos (m + n)"
  "Neg m - Pos n = Neg (m + n)"
  "Neg m - Neg n = sub n m"
  for k l :: int
  by simp_all

lemma times_int_code [code]:
  "k * 0 = 0"
  "0 * l = 0"
  "Pos m * Pos n = Pos (m * n)"
  "Pos m * Neg n = Neg (m * n)"
  "Neg m * Pos n = Neg (m * n)"
  "Neg m * Neg n = Pos (m * n)"
  for k l :: int
  by simp_all

instantiation int :: equal
begin

definition "HOL.equal k l \<longleftrightarrow> k = (l::int)"

instance
  by standard (rule equal_int_def)

end

lemma equal_int_code [code]:
  "HOL.equal 0 (0::int) \<longleftrightarrow> True"
  "HOL.equal 0 (Pos l) \<longleftrightarrow> False"
  "HOL.equal 0 (Neg l) \<longleftrightarrow> False"
  "HOL.equal (Pos k) 0 \<longleftrightarrow> False"
  "HOL.equal (Pos k) (Pos l) \<longleftrightarrow> HOL.equal k l"
  "HOL.equal (Pos k) (Neg l) \<longleftrightarrow> False"
  "HOL.equal (Neg k) 0 \<longleftrightarrow> False"
  "HOL.equal (Neg k) (Pos l) \<longleftrightarrow> False"
  "HOL.equal (Neg k) (Neg l) \<longleftrightarrow> HOL.equal k l"
  by (auto simp add: equal)

lemma equal_int_refl [code nbe]: "HOL.equal k k \<longleftrightarrow> True"
  for k :: int
  by (fact equal_refl)

lemma less_eq_int_code [code]:
  "0 \<le> (0::int) \<longleftrightarrow> True"
  "0 \<le> Pos l \<longleftrightarrow> True"
  "0 \<le> Neg l \<longleftrightarrow> False"
  "Pos k \<le> 0 \<longleftrightarrow> False"
  "Pos k \<le> Pos l \<longleftrightarrow> k \<le> l"
  "Pos k \<le> Neg l \<longleftrightarrow> False"
  "Neg k \<le> 0 \<longleftrightarrow> True"
  "Neg k \<le> Pos l \<longleftrightarrow> True"
  "Neg k \<le> Neg l \<longleftrightarrow> l \<le> k"
  by simp_all

lemma less_int_code [code]:
  "0 < (0::int) \<longleftrightarrow> False"
  "0 < Pos l \<longleftrightarrow> True"
  "0 < Neg l \<longleftrightarrow> False"
  "Pos k < 0 \<longleftrightarrow> False"
  "Pos k < Pos l \<longleftrightarrow> k < l"
  "Pos k < Neg l \<longleftrightarrow> False"
  "Neg k < 0 \<longleftrightarrow> True"
  "Neg k < Pos l \<longleftrightarrow> True"
  "Neg k < Neg l \<longleftrightarrow> l < k"
  by simp_all

lemma nat_code [code]:
  "nat (Int.Neg k) = 0"
  "nat 0 = 0"
  "nat (Int.Pos k) = nat_of_num k"
  by (simp_all add: nat_of_num_numeral)

lemma (in ring_1) of_int_code [code]:
  "of_int (Int.Neg k) = - numeral k"
  "of_int 0 = 0"
  "of_int (Int.Pos k) = numeral k"
  by simp_all


text \<open>Serializer setup.\<close>

code_identifier
  code_module Int \<rightharpoonup> (SML) Arith and (OCaml) Arith and (Haskell) Arith

quickcheck_params [default_type = int]

hide_const (open) Pos Neg sub dup


text \<open>De-register \<open>int\<close> as a quotient type:\<close>

lifting_update int.lifting
lifting_forget int.lifting


subsection \<open>Duplicates\<close>

lemmas int_sum = of_nat_sum [where 'a=int]
lemmas int_prod = of_nat_prod [where 'a=int]
lemmas zle_int = of_nat_le_iff [where 'a=int]
lemmas int_int_eq = of_nat_eq_iff [where 'a=int]
lemmas nonneg_eq_int = nonneg_int_cases
lemmas double_eq_0_iff = double_zero

lemmas int_distrib =
  distrib_right [of z1 z2 w]
  distrib_left [of w z1 z2]
  left_diff_distrib [of z1 z2 w]
  right_diff_distrib [of w z1 z2]
  for z1 z2 w :: int

end

