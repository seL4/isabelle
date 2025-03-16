(*  Title:      HOL/Decision_Procs/Algebra_Aux.thy
    Author:     Stefan Berghofer
*)

section \<open>Things that can be added to the Algebra library\<close>

theory Algebra_Aux
  imports "HOL-Algebra.Ring"
begin

definition of_natural :: "('a, 'm) ring_scheme \<Rightarrow> nat \<Rightarrow> 'a" (\<open>\<guillemotleft>_\<guillemotright>\<^sub>\<nat>\<index>\<close>)
  where "\<guillemotleft>n\<guillemotright>\<^sub>\<nat>\<^bsub>R\<^esub> = ((\<oplus>\<^bsub>R\<^esub>) \<one>\<^bsub>R\<^esub> ^^ n) \<zero>\<^bsub>R\<^esub>"

definition of_integer :: "('a, 'm) ring_scheme \<Rightarrow> int \<Rightarrow> 'a" (\<open>\<guillemotleft>_\<guillemotright>\<index>\<close>)
  where "\<guillemotleft>i\<guillemotright>\<^bsub>R\<^esub> = (if 0 \<le> i then \<guillemotleft>nat i\<guillemotright>\<^sub>\<nat>\<^bsub>R\<^esub> else \<ominus>\<^bsub>R\<^esub> \<guillemotleft>nat (- i)\<guillemotright>\<^sub>\<nat>\<^bsub>R\<^esub>)"

context ring
begin

lemma of_nat_0 [simp]: "\<guillemotleft>0\<guillemotright>\<^sub>\<nat> = \<zero>"
  by (simp add: of_natural_def)

lemma of_nat_Suc [simp]: "\<guillemotleft>Suc n\<guillemotright>\<^sub>\<nat> = \<one> \<oplus> \<guillemotleft>n\<guillemotright>\<^sub>\<nat>"
  by (simp add: of_natural_def)

lemma of_int_0 [simp]: "\<guillemotleft>0\<guillemotright> = \<zero>"
  by (simp add: of_integer_def)

lemma of_nat_closed [simp]: "\<guillemotleft>n\<guillemotright>\<^sub>\<nat> \<in> carrier R"
  by (induct n) simp_all

lemma of_int_closed [simp]: "\<guillemotleft>i\<guillemotright> \<in> carrier R"
  by (simp add: of_integer_def)

lemma of_int_minus [simp]: "\<guillemotleft>- i\<guillemotright> = \<ominus> \<guillemotleft>i\<guillemotright>"
  by (simp add: of_integer_def)

lemma of_nat_add [simp]: "\<guillemotleft>m + n\<guillemotright>\<^sub>\<nat> = \<guillemotleft>m\<guillemotright>\<^sub>\<nat> \<oplus> \<guillemotleft>n\<guillemotright>\<^sub>\<nat>"
  by (induct m) (simp_all add: a_ac)

lemma of_nat_diff [simp]: "n \<le> m \<Longrightarrow> \<guillemotleft>m - n\<guillemotright>\<^sub>\<nat> = \<guillemotleft>m\<guillemotright>\<^sub>\<nat> \<ominus> \<guillemotleft>n\<guillemotright>\<^sub>\<nat>"
proof (induct m arbitrary: n)
  case 0
  then show ?case by (simp add: minus_eq)
next
  case Suc': (Suc m)
  show ?case
  proof (cases n)
    case 0
    then show ?thesis
      by (simp add: minus_eq)
  next
    case (Suc k)
    with Suc' have "\<guillemotleft>Suc m - Suc k\<guillemotright>\<^sub>\<nat> = \<guillemotleft>m\<guillemotright>\<^sub>\<nat> \<ominus> \<guillemotleft>k\<guillemotright>\<^sub>\<nat>" by simp
    also have "\<dots> = \<one> \<oplus> \<ominus> \<one> \<oplus> (\<guillemotleft>m\<guillemotright>\<^sub>\<nat> \<ominus> \<guillemotleft>k\<guillemotright>\<^sub>\<nat>)"
      by (simp add: r_neg)
    also have "\<dots> = \<guillemotleft>Suc m\<guillemotright>\<^sub>\<nat> \<ominus> \<guillemotleft>Suc k\<guillemotright>\<^sub>\<nat>"
      by (simp add: minus_eq minus_add a_ac)
    finally show ?thesis using Suc by simp
  qed
qed

lemma of_int_add [simp]: "\<guillemotleft>i + j\<guillemotright> = \<guillemotleft>i\<guillemotright> \<oplus> \<guillemotleft>j\<guillemotright>"
proof (cases "0 \<le> i")
  case True
  show ?thesis
  proof (cases "0 \<le> j")
    case True
    with \<open>0 \<le> i\<close> show ?thesis
      by (simp add: of_integer_def nat_add_distrib)
  next
    case False
    show ?thesis
    proof (cases "0 \<le> i + j")
      case True
      then have "\<guillemotleft>i + j\<guillemotright> = \<guillemotleft>nat (i - (- j))\<guillemotright>\<^sub>\<nat>"
        by (simp add: of_integer_def)
      also from True \<open>0 \<le> i\<close> \<open>\<not> 0 \<le> j\<close>
      have "nat (i - (- j)) = nat i - nat (- j)"
        by (simp add: nat_diff_distrib)
      finally show ?thesis using True \<open>0 \<le> i\<close> \<open>\<not> 0 \<le> j\<close>
        by (simp add: minus_eq of_integer_def)
    next
      case False
      then have "\<guillemotleft>i + j\<guillemotright> = \<ominus> \<guillemotleft>nat (- j - i)\<guillemotright>\<^sub>\<nat>"
        by (simp add: of_integer_def) (simp only: diff_conv_add_uminus add_ac)
      also from False \<open>0 \<le> i\<close> \<open>\<not> 0 \<le> j\<close>
      have "nat (- j - i) = nat (- j) - nat i"
        by (simp add: nat_diff_distrib)
      finally show ?thesis using False \<open>0 \<le> i\<close> \<open>\<not> 0 \<le> j\<close>
        by (simp add: minus_eq minus_add a_ac of_integer_def)
    qed
  qed
next
  case False
  show ?thesis
  proof (cases "0 \<le> j")
    case True
    show ?thesis
    proof (cases "0 \<le> i + j")
      case True
      then have "\<guillemotleft>i + j\<guillemotright> = \<guillemotleft>nat (j - (- i))\<guillemotright>\<^sub>\<nat>"
        by (simp add: of_integer_def add_ac)
      also from True \<open>\<not> 0 \<le> i\<close> \<open>0 \<le> j\<close>
      have "nat (j - (- i)) = nat j - nat (- i)"
        by (simp add: nat_diff_distrib)
      finally show ?thesis using True \<open>\<not> 0 \<le> i\<close> \<open>0 \<le> j\<close>
        by (simp add: minus_eq minus_add a_ac of_integer_def)
    next
      case False
      then have "\<guillemotleft>i + j\<guillemotright> = \<ominus> \<guillemotleft>nat (- i - j)\<guillemotright>\<^sub>\<nat>"
        by (simp add: of_integer_def)
      also from False \<open>\<not> 0 \<le> i\<close> \<open>0 \<le> j\<close>
      have "nat (- i - j) = nat (- i) - nat j"
        by (simp add: nat_diff_distrib)
      finally show ?thesis using False \<open>\<not> 0 \<le> i\<close> \<open>0 \<le> j\<close>
        by (simp add: minus_eq minus_add of_integer_def)
    qed
  next
    case False
    with \<open>\<not> 0 \<le> i\<close> show ?thesis
      by (simp add: of_integer_def nat_add_distrib minus_add diff_conv_add_uminus
          del: add_uminus_conv_diff uminus_add_conv_diff)
  qed
qed

lemma of_int_diff [simp]: "\<guillemotleft>i - j\<guillemotright> = \<guillemotleft>i\<guillemotright> \<ominus> \<guillemotleft>j\<guillemotright>"
  by (simp only: diff_conv_add_uminus of_int_add) (simp add: minus_eq)

lemma of_nat_mult [simp]: "\<guillemotleft>i * j\<guillemotright>\<^sub>\<nat> = \<guillemotleft>i\<guillemotright>\<^sub>\<nat> \<otimes> \<guillemotleft>j\<guillemotright>\<^sub>\<nat>"
  by (induct i) (simp_all add: l_distr)

lemma of_int_mult [simp]: "\<guillemotleft>i * j\<guillemotright> = \<guillemotleft>i\<guillemotright> \<otimes> \<guillemotleft>j\<guillemotright>"
proof (cases "0 \<le> i")
  case True
  show ?thesis
  proof (cases "0 \<le> j")
    case True
    with \<open>0 \<le> i\<close> show ?thesis
      by (simp add: of_integer_def nat_mult_distrib zero_le_mult_iff)
  next
    case False
    with \<open>0 \<le> i\<close> show ?thesis
      by (simp add: of_integer_def zero_le_mult_iff
        minus_mult_right nat_mult_distrib r_minus
        del: minus_mult_right [symmetric])
  qed
next
  case False
  show ?thesis
  proof (cases "0 \<le> j")
    case True
    with \<open>\<not> 0 \<le> i\<close> show ?thesis
      by (simp add: of_integer_def zero_le_mult_iff
        minus_mult_left nat_mult_distrib l_minus
        del: minus_mult_left [symmetric])
  next
    case False
    with \<open>\<not> 0 \<le> i\<close> show ?thesis
      by (simp add: of_integer_def zero_le_mult_iff
        minus_mult_minus [of i j, symmetric] nat_mult_distrib
        l_minus r_minus
        del: minus_mult_minus
        minus_mult_left [symmetric] minus_mult_right [symmetric])
  qed
qed

lemma of_int_1 [simp]: "\<guillemotleft>1\<guillemotright> = \<one>"
  by (simp add: of_integer_def)

lemma of_int_2: "\<guillemotleft>2\<guillemotright> = \<one> \<oplus> \<one>"
  by (simp add: of_integer_def numeral_2_eq_2)

lemma minus_0_r [simp]: "x \<in> carrier R \<Longrightarrow> x \<ominus> \<zero> = x"
  by (simp add: minus_eq)

lemma minus_0_l [simp]: "x \<in> carrier R \<Longrightarrow> \<zero> \<ominus> x = \<ominus> x"
  by (simp add: minus_eq)

lemma eq_diff0:
  assumes "x \<in> carrier R" "y \<in> carrier R"
  shows "x \<ominus> y = \<zero> \<longleftrightarrow> x = y"
proof
  assume "x \<ominus> y = \<zero>"
  with assms have "x \<oplus> (\<ominus> y \<oplus> y) = y"
    by (simp add: minus_eq a_assoc [symmetric])
  with assms show "x = y" by (simp add: l_neg)
next
  assume "x = y"
  with assms show "x \<ominus> y = \<zero>" by (simp add: minus_eq r_neg)
qed

lemma power2_eq_square: "x \<in> carrier R \<Longrightarrow> x [^] (2::nat) = x \<otimes> x"
  by (simp add: numeral_eq_Suc)

lemma eq_neg_iff_add_eq_0:
  assumes "x \<in> carrier R" "y \<in> carrier R"
  shows "x = \<ominus> y \<longleftrightarrow> x \<oplus> y = \<zero>"
proof
  assume "x = \<ominus> y"
  with assms show "x \<oplus> y = \<zero>" by (simp add: l_neg)
next
  assume "x \<oplus> y = \<zero>"
  with assms have "x \<oplus> (y \<oplus> \<ominus> y) = \<zero> \<oplus> \<ominus> y"
    by (simp add: a_assoc [symmetric])
  with assms show "x = \<ominus> y"
    by (simp add: r_neg)
qed

lemma neg_equal_iff_equal:
  assumes x: "x \<in> carrier R" and y: "y \<in> carrier R"
  shows "\<ominus> x = \<ominus> y \<longleftrightarrow> x = y"
proof
  assume "\<ominus> x = \<ominus> y"
  then have "\<ominus> (\<ominus> x) = \<ominus> (\<ominus> y)" by simp
  with x y show "x = y" by simp
next
  assume "x = y"
  then show "\<ominus> x = \<ominus> y" by simp
qed

lemma neg_equal_swap:
  assumes x: "x \<in> carrier R" and y: "y \<in> carrier R"
  shows "(\<ominus> x = y) = (x = \<ominus> y)"
  using assms neg_equal_iff_equal [of x "\<ominus> y"]
  by simp

lemma mult2: "x \<in> carrier R \<Longrightarrow> x \<oplus> x = \<guillemotleft>2\<guillemotright> \<otimes> x"
  by (simp add: of_int_2 l_distr)

end

lemma (in cring) of_int_power [simp]: "\<guillemotleft>i ^ n\<guillemotright> = \<guillemotleft>i\<guillemotright> [^] n"
  by (induct n) (simp_all add: m_ac)

definition cring_class_ops :: "'a::comm_ring_1 ring"
  where "cring_class_ops \<equiv> \<lparr>carrier = UNIV, mult = (*), one = 1, zero = 0, add = (+)\<rparr>"

lemma cring_class: "cring cring_class_ops"
  apply unfold_locales
  apply (auto simp add: cring_class_ops_def ring_distribs Units_def)
  apply (rule_tac x="- x" in exI)
  apply simp
  done

lemma carrier_class: "x \<in> carrier cring_class_ops"
  by (simp add: cring_class_ops_def)

lemma zero_class: "\<zero>\<^bsub>cring_class_ops\<^esub> = 0"
  by (simp add: cring_class_ops_def)

lemma one_class: "\<one>\<^bsub>cring_class_ops\<^esub> = 1"
  by (simp add: cring_class_ops_def)

lemma plus_class: "x \<oplus>\<^bsub>cring_class_ops\<^esub> y = x + y"
  by (simp add: cring_class_ops_def)

lemma times_class: "x \<otimes>\<^bsub>cring_class_ops\<^esub> y = x * y"
  by (simp add: cring_class_ops_def)

lemma uminus_class: "\<ominus>\<^bsub>cring_class_ops\<^esub> x = - x"
proof -
  have "(THE y::'a. x + y = 0 \<and> y + x = 0) = - x"
    by (rule the_equality) (simp_all add: eq_neg_iff_add_eq_0)
  then show ?thesis
    by (simp add: a_inv_def m_inv_def cring_class_ops_def)
qed

lemma minus_class: "x \<ominus>\<^bsub>cring_class_ops\<^esub> y = x - y"
  by (simp add: a_minus_def carrier_class plus_class uminus_class)

lemma power_class: "x [^]\<^bsub>cring_class_ops\<^esub> n = x ^ n"
  by (induct n) (simp_all add: one_class times_class
    monoid.nat_pow_0 [OF comm_monoid.axioms(1) [OF cring.axioms(2) [OF cring_class]]]
    monoid.nat_pow_Suc [OF comm_monoid.axioms(1) [OF cring.axioms(2) [OF cring_class]]])

lemma of_nat_class: "\<guillemotleft>n\<guillemotright>\<^sub>\<nat>\<^bsub>cring_class_ops\<^esub> = of_nat n"
  by (induct n) (simp_all add: cring_class_ops_def of_natural_def)

lemma of_int_class: "\<guillemotleft>i\<guillemotright>\<^bsub>cring_class_ops\<^esub> = of_int i"
  by (simp add: of_integer_def of_nat_class uminus_class)

lemmas class_simps = zero_class one_class plus_class minus_class uminus_class
  times_class power_class of_nat_class of_int_class carrier_class

interpretation cring_class: cring "cring_class_ops::'a::comm_ring_1 ring"
  rewrites "(\<zero>\<^bsub>cring_class_ops\<^esub>::'a) = 0"
    and "(\<one>\<^bsub>cring_class_ops\<^esub>::'a) = 1"
    and "(x::'a) \<oplus>\<^bsub>cring_class_ops\<^esub> y = x + y"
    and "(x::'a) \<otimes>\<^bsub>cring_class_ops\<^esub> y = x * y"
    and "\<ominus>\<^bsub>cring_class_ops\<^esub> (x::'a) = - x"
    and "(x::'a) \<ominus>\<^bsub>cring_class_ops\<^esub> y = x - y"
    and "(x::'a) [^]\<^bsub>cring_class_ops\<^esub> n = x ^ n"
    and "\<guillemotleft>n\<guillemotright>\<^sub>\<nat>\<^bsub>cring_class_ops\<^esub> = of_nat n"
    and "((\<guillemotleft>i\<guillemotright>\<^bsub>cring_class_ops\<^esub>)::'a) = of_int i"
    and "(Int.of_int (numeral m)::'a) = numeral m"
  by (simp_all add: cring_class class_simps)

lemma (in domain) nat_pow_eq_0_iff [simp]:
  "a \<in> carrier R \<Longrightarrow> (a [^] (n::nat) = \<zero>) = (a = \<zero> \<and> n \<noteq> 0)"
  by (induct n) (auto simp add: integral_iff)

lemma (in domain) square_eq_iff:
  assumes "x \<in> carrier R" "y \<in> carrier R"
  shows "(x \<otimes> x = y \<otimes> y) = (x = y \<or> x = \<ominus> y)"
proof
  assume "x \<otimes> x = y \<otimes> y"
  with assms have "(x \<ominus> y) \<otimes> (x \<oplus> y) = x \<otimes> y \<oplus> \<ominus> (x \<otimes> y) \<oplus> (y \<otimes> y \<oplus> \<ominus> (y \<otimes> y))"
    by (simp add: r_distr l_distr minus_eq r_minus m_comm a_ac)
  with assms show "x = y \<or> x = \<ominus> y"
    by (simp add: integral_iff eq_neg_iff_add_eq_0 eq_diff0 r_neg)
next
  assume "x = y \<or> x = \<ominus> y"
  with assms show "x \<otimes> x = y \<otimes> y"
    by (auto simp add: l_minus r_minus)
qed

definition m_div :: "('a, 'b) ring_scheme \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl \<open>\<oslash>\<index>\<close> 70)
  where "x \<oslash>\<^bsub>G\<^esub> y = (if y = \<zero>\<^bsub>G\<^esub> then \<zero>\<^bsub>G\<^esub> else x \<otimes>\<^bsub>G\<^esub> inv\<^bsub>G\<^esub> y)"

context field
begin

lemma inv_closed [simp]: "x \<in> carrier R \<Longrightarrow> x \<noteq> \<zero> \<Longrightarrow> inv x \<in> carrier R"
  by (simp add: field_Units)

lemma l_inv [simp]: "x \<in> carrier R \<Longrightarrow> x \<noteq> \<zero> \<Longrightarrow> inv x \<otimes> x = \<one>"
  by (simp add: field_Units)

lemma r_inv [simp]: "x \<in> carrier R \<Longrightarrow> x \<noteq> \<zero> \<Longrightarrow> x \<otimes> inv x = \<one>"
  by (simp add: field_Units)

lemma inverse_unique:
  assumes a: "a \<in> carrier R"
    and b: "b \<in> carrier R"
    and ab: "a \<otimes> b = \<one>"
  shows "inv a = b"
proof -
  from ab b have *: "a \<noteq> \<zero>"
    by (cases "a = \<zero>") simp_all
  with a have "inv a \<otimes> (a \<otimes> b) = inv a"
    by (simp add: ab)
  with a b * show ?thesis
    by (simp add: m_assoc [symmetric])
qed

lemma nonzero_inverse_inverse_eq: "a \<in> carrier R \<Longrightarrow> a \<noteq> \<zero> \<Longrightarrow> inv (inv a) = a"
  by (rule inverse_unique) simp_all

lemma inv_1 [simp]: "inv \<one> = \<one>"
  by (rule inverse_unique) simp_all

lemma nonzero_inverse_mult_distrib:
  assumes "a \<in> carrier R" "b \<in> carrier R"
    and "a \<noteq> \<zero>" "b \<noteq> \<zero>"
  shows "inv (a \<otimes> b) = inv b \<otimes> inv a"
proof -
  from assms have "a \<otimes> (b \<otimes> inv b) \<otimes> inv a = \<one>"
    by simp
  with assms have eq: "a \<otimes> b \<otimes> (inv b \<otimes> inv a) = \<one>"
    by (simp only: m_assoc m_closed inv_closed assms)
  from assms show ?thesis
    using inverse_unique [OF _ _ eq] by simp
qed

lemma nonzero_imp_inverse_nonzero:
  assumes "a \<in> carrier R" and "a \<noteq> \<zero>"
  shows "inv a \<noteq> \<zero>"
proof
  assume *: "inv a = \<zero>"
  from assms have **: "\<one> = a \<otimes> inv a"
    by simp
  also from assms have "\<dots> = \<zero>" by (simp add: *)
  finally have "\<one> = \<zero>" .
  then show False by (simp add: eq_commute)
qed

lemma nonzero_divide_divide_eq_left:
  "a \<in> carrier R \<Longrightarrow> b \<in> carrier R \<Longrightarrow> c \<in> carrier R \<Longrightarrow> b \<noteq> \<zero> \<Longrightarrow> c \<noteq> \<zero> \<Longrightarrow>
    a \<oslash> b \<oslash> c = a \<oslash> (b \<otimes> c)"
  by (simp add: m_div_def nonzero_inverse_mult_distrib m_ac integral_iff)

lemma nonzero_times_divide_eq:
  "a \<in> carrier R \<Longrightarrow> b \<in> carrier R \<Longrightarrow> c \<in> carrier R \<Longrightarrow> d \<in> carrier R \<Longrightarrow>
    b \<noteq> \<zero> \<Longrightarrow> d \<noteq> \<zero> \<Longrightarrow> (a \<oslash> b) \<otimes> (c \<oslash> d) = (a \<otimes> c) \<oslash> (b \<otimes> d)"
  by (simp add: m_div_def nonzero_inverse_mult_distrib m_ac integral_iff)

lemma nonzero_divide_divide_eq:
  "a \<in> carrier R \<Longrightarrow> b \<in> carrier R \<Longrightarrow> c \<in> carrier R \<Longrightarrow> d \<in> carrier R \<Longrightarrow>
    b \<noteq> \<zero> \<Longrightarrow> c \<noteq> \<zero> \<Longrightarrow> d \<noteq> \<zero> \<Longrightarrow> (a \<oslash> b) \<oslash> (c \<oslash> d) = (a \<otimes> d) \<oslash> (b \<otimes> c)"
  by (simp add: m_div_def nonzero_inverse_mult_distrib
    nonzero_imp_inverse_nonzero nonzero_inverse_inverse_eq m_ac integral_iff)

lemma divide_1 [simp]: "x \<in> carrier R \<Longrightarrow> x \<oslash> \<one> = x"
  by (simp add: m_div_def)

lemma add_frac_eq:
  assumes "x \<in> carrier R" "y \<in> carrier R" "z \<in> carrier R" "w \<in> carrier R"
    and "y \<noteq> \<zero>" "z \<noteq> \<zero>"
  shows "x \<oslash> y \<oplus> w \<oslash> z = (x \<otimes> z \<oplus> w \<otimes> y) \<oslash> (y \<otimes> z)"
proof -
  from assms
  have "x \<oslash> y \<oplus> w \<oslash> z = x \<otimes> inv y \<otimes> (z \<otimes> inv z) \<oplus> w \<otimes> inv z \<otimes> (y \<otimes> inv y)"
    by (simp add: m_div_def)
  also from assms have "\<dots> = (x \<otimes> z \<oplus> w \<otimes> y) \<oslash> (y \<otimes> z)"
    by (simp add: m_div_def nonzero_inverse_mult_distrib r_distr m_ac integral_iff del: r_inv)
  finally show ?thesis .
qed

lemma div_closed [simp]:
  "x \<in> carrier R \<Longrightarrow> y \<in> carrier R \<Longrightarrow> y \<noteq> \<zero> \<Longrightarrow> x \<oslash> y \<in> carrier R"
  by (simp add: m_div_def)

lemma minus_divide_left [simp]:
  "a \<in> carrier R \<Longrightarrow> b \<in> carrier R \<Longrightarrow> b \<noteq> \<zero> \<Longrightarrow> \<ominus> (a \<oslash> b) = \<ominus> a \<oslash> b"
  by (simp add: m_div_def l_minus)

lemma diff_frac_eq:
  assumes "x \<in> carrier R" "y \<in> carrier R" "z \<in> carrier R" "w \<in> carrier R"
    and "y \<noteq> \<zero>" "z \<noteq> \<zero>"
  shows "x \<oslash> y \<ominus> w \<oslash> z = (x \<otimes> z \<ominus> w \<otimes> y) \<oslash> (y \<otimes> z)"
  using assms by (simp add: minus_eq l_minus add_frac_eq)

lemma nonzero_mult_divide_mult_cancel_left [simp]:
  assumes "a \<in> carrier R" "b \<in> carrier R" "c \<in> carrier R"
    and "b \<noteq> \<zero>" "c \<noteq> \<zero>"
  shows "(c \<otimes> a) \<oslash> (c \<otimes> b) = a \<oslash> b"
proof -
  from assms have "(c \<otimes> a) \<oslash> (c \<otimes> b) = c \<otimes> a \<otimes> (inv b \<otimes> inv c)"
    by (simp add: m_div_def nonzero_inverse_mult_distrib integral_iff)
  also from assms have "\<dots> =  a \<otimes> inv b \<otimes> (inv c \<otimes> c)"
    by (simp add: m_ac)
  also from assms have "\<dots> =  a \<otimes> inv b"
    by simp
  finally show ?thesis
    using assms by (simp add: m_div_def)
qed

lemma times_divide_eq_left [simp]:
  "a \<in> carrier R \<Longrightarrow> b \<in> carrier R \<Longrightarrow> c \<in> carrier R \<Longrightarrow> c \<noteq> \<zero> \<Longrightarrow>
    (b \<oslash> c) \<otimes> a = b \<otimes> a \<oslash> c"
  by (simp add: m_div_def m_ac)

lemma times_divide_eq_right [simp]:
  "a \<in> carrier R \<Longrightarrow> b \<in> carrier R \<Longrightarrow> c \<in> carrier R \<Longrightarrow> c \<noteq> \<zero> \<Longrightarrow>
    a \<otimes> (b \<oslash> c) = a \<otimes> b \<oslash> c"
  by (simp add: m_div_def m_ac)

lemma nonzero_power_divide:
  "a \<in> carrier R \<Longrightarrow> b \<in> carrier R \<Longrightarrow> b \<noteq> \<zero> \<Longrightarrow>
    (a \<oslash> b) [^] (n::nat) = a [^] n \<oslash> b [^] n"
  by (induct n) (simp_all add: nonzero_divide_divide_eq_left)

lemma r_diff_distr:
  "x \<in> carrier R \<Longrightarrow> y \<in> carrier R \<Longrightarrow> z \<in> carrier R \<Longrightarrow>
    z \<otimes> (x \<ominus> y) = z \<otimes> x \<ominus> z \<otimes> y"
  by (simp add: minus_eq r_distr r_minus)

lemma divide_zero_left [simp]: "a \<in> carrier R \<Longrightarrow> a \<noteq> \<zero> \<Longrightarrow> \<zero> \<oslash> a = \<zero>"
  by (simp add: m_div_def)

lemma divide_self: "a \<in> carrier R \<Longrightarrow> a \<noteq> \<zero> \<Longrightarrow> a \<oslash> a = \<one>"
  by (simp add: m_div_def)

lemma divide_eq_0_iff:
  assumes "a \<in> carrier R" "b \<in> carrier R"
    and "b \<noteq> \<zero>"
  shows "a \<oslash> b = \<zero> \<longleftrightarrow> a = \<zero>"
proof
  assume "a = \<zero>"
  with assms show "a \<oslash> b = \<zero>" by simp
next
  assume "a \<oslash> b = \<zero>"
  with assms have "b \<otimes> (a \<oslash> b) = b \<otimes> \<zero>" by simp
  also from assms have "b \<otimes> (a \<oslash> b) = b \<otimes> a \<oslash> b" by simp
  also from assms have "b \<otimes> a = a \<otimes> b" by (simp add: m_comm)
  also from assms have "a \<otimes> b \<oslash> b = a \<otimes> (b \<oslash> b)" by simp
  also from assms have "b \<oslash> b = \<one>" by (simp add: divide_self)
  finally show "a = \<zero>" using assms by simp
qed

end

lemma field_class: "field (cring_class_ops::'a::field ring)"
  apply unfold_locales
    apply (simp_all add: cring_class_ops_def)
  using field_class.field_inverse by (force simp add: Units_def)

lemma div_class: "(x::'a::field) \<oslash>\<^bsub>cring_class_ops\<^esub> y = x / y"
  by (simp add: carrier_class class_simps cring_class.comm_inv_char
      field_class.field_divide_inverse m_div_def)

interpretation field_class: field "cring_class_ops::'a::field ring"
  rewrites "(\<zero>\<^bsub>cring_class_ops\<^esub>::'a) = 0"
    and "(\<one>\<^bsub>cring_class_ops\<^esub>::'a) = 1"
    and "(x::'a) \<oplus>\<^bsub>cring_class_ops\<^esub> y = x + y"
    and "(x::'a) \<otimes>\<^bsub>cring_class_ops\<^esub> y = x * y"
    and "\<ominus>\<^bsub>cring_class_ops\<^esub> (x::'a) = - x"
    and "(x::'a) \<ominus>\<^bsub>cring_class_ops\<^esub> y = x - y"
    and "(x::'a) [^]\<^bsub>cring_class_ops\<^esub> n = x ^ n"
    and "\<guillemotleft>n\<guillemotright>\<^sub>\<nat>\<^bsub>cring_class_ops\<^esub> = of_nat n"
    and "((\<guillemotleft>i\<guillemotright>\<^bsub>cring_class_ops\<^esub>)::'a) = of_int i"
    and "(x::'a) \<oslash>\<^bsub>cring_class_ops\<^esub> y = x / y"
    and "(Int.of_int (numeral m)::'a) = numeral m"
  by (simp_all add: field_class class_simps div_class)

end
