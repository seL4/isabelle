(*  Title:      HOL/Library/Extended_Real.thy
    Author:     Johannes Hölzl, TU München
    Author:     Robert Himmelmann, TU München
    Author:     Armin Heller, TU München
    Author:     Bogdan Grechuk, University of Edinburgh
*)

header {* Extended real number line *}

theory Extended_Real
imports Complex_Main Extended_Nat Liminf_Limsup
begin

text {*

For more lemmas about the extended real numbers go to
  @{file "~~/src/HOL/Multivariate_Analysis/Extended_Real_Limits.thy"}

*}

subsection {* Definition and basic properties *}

datatype ereal = ereal real | PInfty | MInfty

instantiation ereal :: uminus
begin

fun uminus_ereal where
  "- (ereal r) = ereal (- r)"
| "- PInfty = MInfty"
| "- MInfty = PInfty"

instance ..

end

instantiation ereal :: infinity
begin

definition "(\<infinity>::ereal) = PInfty"
instance ..

end

declare [[coercion "ereal :: real \<Rightarrow> ereal"]]

lemma ereal_uminus_uminus[simp]:
  fixes a :: ereal
  shows "- (- a) = a"
  by (cases a) simp_all

lemma
  shows PInfty_eq_infinity[simp]: "PInfty = \<infinity>"
    and MInfty_eq_minfinity[simp]: "MInfty = - \<infinity>"
    and MInfty_neq_PInfty[simp]: "\<infinity> \<noteq> - (\<infinity>::ereal)" "- \<infinity> \<noteq> (\<infinity>::ereal)"
    and MInfty_neq_ereal[simp]: "ereal r \<noteq> - \<infinity>" "- \<infinity> \<noteq> ereal r"
    and PInfty_neq_ereal[simp]: "ereal r \<noteq> \<infinity>" "\<infinity> \<noteq> ereal r"
    and PInfty_cases[simp]: "(case \<infinity> of ereal r \<Rightarrow> f r | PInfty \<Rightarrow> y | MInfty \<Rightarrow> z) = y"
    and MInfty_cases[simp]: "(case - \<infinity> of ereal r \<Rightarrow> f r | PInfty \<Rightarrow> y | MInfty \<Rightarrow> z) = z"
  by (simp_all add: infinity_ereal_def)

declare
  PInfty_eq_infinity[code_post]
  MInfty_eq_minfinity[code_post]

lemma [code_unfold]:
  "\<infinity> = PInfty"
  "- PInfty = MInfty"
  by simp_all

lemma inj_ereal[simp]: "inj_on ereal A"
  unfolding inj_on_def by auto

lemma ereal_cases[cases type: ereal]:
  obtains (real) r where "x = ereal r"
    | (PInf) "x = \<infinity>"
    | (MInf) "x = -\<infinity>"
  using assms by (cases x) auto

lemmas ereal2_cases = ereal_cases[case_product ereal_cases]
lemmas ereal3_cases = ereal2_cases[case_product ereal_cases]

lemma ereal_uminus_eq_iff[simp]:
  fixes a b :: ereal
  shows "-a = -b \<longleftrightarrow> a = b"
  by (cases rule: ereal2_cases[of a b]) simp_all

function of_ereal :: "ereal \<Rightarrow> real" where
  "of_ereal (ereal r) = r"
| "of_ereal \<infinity> = 0"
| "of_ereal (-\<infinity>) = 0"
  by (auto intro: ereal_cases)
termination by default (rule wf_empty)

defs (overloaded)
  real_of_ereal_def [code_unfold]: "real \<equiv> of_ereal"

lemma real_of_ereal[simp]:
  "real (- x :: ereal) = - (real x)"
  "real (ereal r) = r"
  "real (\<infinity>::ereal) = 0"
  by (cases x) (simp_all add: real_of_ereal_def)

lemma range_ereal[simp]: "range ereal = UNIV - {\<infinity>, -\<infinity>}"
proof safe
  fix x
  assume "x \<notin> range ereal" "x \<noteq> \<infinity>"
  then show "x = -\<infinity>"
    by (cases x) auto
qed auto

lemma ereal_range_uminus[simp]: "range uminus = (UNIV::ereal set)"
proof safe
  fix x :: ereal
  show "x \<in> range uminus"
    by (intro image_eqI[of _ _ "-x"]) auto
qed auto

instantiation ereal :: abs
begin

function abs_ereal where
  "\<bar>ereal r\<bar> = ereal \<bar>r\<bar>"
| "\<bar>-\<infinity>\<bar> = (\<infinity>::ereal)"
| "\<bar>\<infinity>\<bar> = (\<infinity>::ereal)"
by (auto intro: ereal_cases)
termination proof qed (rule wf_empty)

instance ..

end

lemma abs_eq_infinity_cases[elim!]:
  fixes x :: ereal
  assumes "\<bar>x\<bar> = \<infinity>"
  obtains "x = \<infinity>" | "x = -\<infinity>"
  using assms by (cases x) auto

lemma abs_neq_infinity_cases[elim!]:
  fixes x :: ereal
  assumes "\<bar>x\<bar> \<noteq> \<infinity>"
  obtains r where "x = ereal r"
  using assms by (cases x) auto

lemma abs_ereal_uminus[simp]:
  fixes x :: ereal
  shows "\<bar>- x\<bar> = \<bar>x\<bar>"
  by (cases x) auto

lemma ereal_infinity_cases:
  fixes a :: ereal
  shows "a \<noteq> \<infinity> \<Longrightarrow> a \<noteq> -\<infinity> \<Longrightarrow> \<bar>a\<bar> \<noteq> \<infinity>"
  by auto


subsubsection "Addition"

instantiation ereal :: "{one,comm_monoid_add,zero_neq_one}"
begin

definition "0 = ereal 0"
definition "1 = ereal 1"

function plus_ereal where
  "ereal r + ereal p = ereal (r + p)"
| "\<infinity> + a = (\<infinity>::ereal)"
| "a + \<infinity> = (\<infinity>::ereal)"
| "ereal r + -\<infinity> = - \<infinity>"
| "-\<infinity> + ereal p = -(\<infinity>::ereal)"
| "-\<infinity> + -\<infinity> = -(\<infinity>::ereal)"
proof -
  case (goal1 P x)
  then obtain a b where "x = (a, b)"
    by (cases x) auto
  with goal1 show P
   by (cases rule: ereal2_cases[of a b]) auto
qed auto
termination by default (rule wf_empty)

lemma Infty_neq_0[simp]:
  "(\<infinity>::ereal) \<noteq> 0" "0 \<noteq> (\<infinity>::ereal)"
  "-(\<infinity>::ereal) \<noteq> 0" "0 \<noteq> -(\<infinity>::ereal)"
  by (simp_all add: zero_ereal_def)

lemma ereal_eq_0[simp]:
  "ereal r = 0 \<longleftrightarrow> r = 0"
  "0 = ereal r \<longleftrightarrow> r = 0"
  unfolding zero_ereal_def by simp_all

lemma ereal_eq_1[simp]:
  "ereal r = 1 \<longleftrightarrow> r = 1"
  "1 = ereal r \<longleftrightarrow> r = 1"
  unfolding one_ereal_def by simp_all

instance
proof
  fix a b c :: ereal
  show "0 + a = a"
    by (cases a) (simp_all add: zero_ereal_def)
  show "a + b = b + a"
    by (cases rule: ereal2_cases[of a b]) simp_all
  show "a + b + c = a + (b + c)"
    by (cases rule: ereal3_cases[of a b c]) simp_all
  show "0 \<noteq> (1::ereal)"
    by (simp add: one_ereal_def zero_ereal_def)
qed

end

instance ereal :: numeral ..

lemma real_of_ereal_0[simp]: "real (0::ereal) = 0"
  unfolding real_of_ereal_def zero_ereal_def by simp

lemma abs_ereal_zero[simp]: "\<bar>0\<bar> = (0::ereal)"
  unfolding zero_ereal_def abs_ereal.simps by simp

lemma ereal_uminus_zero[simp]: "- 0 = (0::ereal)"
  by (simp add: zero_ereal_def)

lemma ereal_uminus_zero_iff[simp]:
  fixes a :: ereal
  shows "-a = 0 \<longleftrightarrow> a = 0"
  by (cases a) simp_all

lemma ereal_plus_eq_PInfty[simp]:
  fixes a b :: ereal
  shows "a + b = \<infinity> \<longleftrightarrow> a = \<infinity> \<or> b = \<infinity>"
  by (cases rule: ereal2_cases[of a b]) auto

lemma ereal_plus_eq_MInfty[simp]:
  fixes a b :: ereal
  shows "a + b = -\<infinity> \<longleftrightarrow> (a = -\<infinity> \<or> b = -\<infinity>) \<and> a \<noteq> \<infinity> \<and> b \<noteq> \<infinity>"
  by (cases rule: ereal2_cases[of a b]) auto

lemma ereal_add_cancel_left:
  fixes a b :: ereal
  assumes "a \<noteq> -\<infinity>"
  shows "a + b = a + c \<longleftrightarrow> a = \<infinity> \<or> b = c"
  using assms by (cases rule: ereal3_cases[of a b c]) auto

lemma ereal_add_cancel_right:
  fixes a b :: ereal
  assumes "a \<noteq> -\<infinity>"
  shows "b + a = c + a \<longleftrightarrow> a = \<infinity> \<or> b = c"
  using assms by (cases rule: ereal3_cases[of a b c]) auto

lemma ereal_real: "ereal (real x) = (if \<bar>x\<bar> = \<infinity> then 0 else x)"
  by (cases x) simp_all

lemma real_of_ereal_add:
  fixes a b :: ereal
  shows "real (a + b) =
    (if (\<bar>a\<bar> = \<infinity>) \<and> (\<bar>b\<bar> = \<infinity>) \<or> (\<bar>a\<bar> \<noteq> \<infinity>) \<and> (\<bar>b\<bar> \<noteq> \<infinity>) then real a + real b else 0)"
  by (cases rule: ereal2_cases[of a b]) auto


subsubsection "Linear order on @{typ ereal}"

instantiation ereal :: linorder
begin

function less_ereal
where
  "   ereal x < ereal y     \<longleftrightarrow> x < y"
| "(\<infinity>::ereal) < a           \<longleftrightarrow> False"
| "         a < -(\<infinity>::ereal) \<longleftrightarrow> False"
| "ereal x    < \<infinity>           \<longleftrightarrow> True"
| "        -\<infinity> < ereal r     \<longleftrightarrow> True"
| "        -\<infinity> < (\<infinity>::ereal) \<longleftrightarrow> True"
proof -
  case (goal1 P x)
  then obtain a b where "x = (a,b)" by (cases x) auto
  with goal1 show P by (cases rule: ereal2_cases[of a b]) auto
qed simp_all
termination by (relation "{}") simp

definition "x \<le> (y::ereal) \<longleftrightarrow> x < y \<or> x = y"

lemma ereal_infty_less[simp]:
  fixes x :: ereal
  shows "x < \<infinity> \<longleftrightarrow> (x \<noteq> \<infinity>)"
    "-\<infinity> < x \<longleftrightarrow> (x \<noteq> -\<infinity>)"
  by (cases x, simp_all) (cases x, simp_all)

lemma ereal_infty_less_eq[simp]:
  fixes x :: ereal
  shows "\<infinity> \<le> x \<longleftrightarrow> x = \<infinity>"
    and "x \<le> -\<infinity> \<longleftrightarrow> x = -\<infinity>"
  by (auto simp add: less_eq_ereal_def)

lemma ereal_less[simp]:
  "ereal r < 0 \<longleftrightarrow> (r < 0)"
  "0 < ereal r \<longleftrightarrow> (0 < r)"
  "ereal r < 1 \<longleftrightarrow> (r < 1)"
  "1 < ereal r \<longleftrightarrow> (1 < r)"
  "0 < (\<infinity>::ereal)"
  "-(\<infinity>::ereal) < 0"
  by (simp_all add: zero_ereal_def one_ereal_def)

lemma ereal_less_eq[simp]:
  "x \<le> (\<infinity>::ereal)"
  "-(\<infinity>::ereal) \<le> x"
  "ereal r \<le> ereal p \<longleftrightarrow> r \<le> p"
  "ereal r \<le> 0 \<longleftrightarrow> r \<le> 0"
  "0 \<le> ereal r \<longleftrightarrow> 0 \<le> r"
  "ereal r \<le> 1 \<longleftrightarrow> r \<le> 1"
  "1 \<le> ereal r \<longleftrightarrow> 1 \<le> r"
  by (auto simp add: less_eq_ereal_def zero_ereal_def one_ereal_def)

lemma ereal_infty_less_eq2:
  "a \<le> b \<Longrightarrow> a = \<infinity> \<Longrightarrow> b = (\<infinity>::ereal)"
  "a \<le> b \<Longrightarrow> b = -\<infinity> \<Longrightarrow> a = -(\<infinity>::ereal)"
  by simp_all

instance
proof
  fix x y z :: ereal
  show "x \<le> x"
    by (cases x) simp_all
  show "x < y \<longleftrightarrow> x \<le> y \<and> \<not> y \<le> x"
    by (cases rule: ereal2_cases[of x y]) auto
  show "x \<le> y \<or> y \<le> x "
    by (cases rule: ereal2_cases[of x y]) auto
  {
    assume "x \<le> y" "y \<le> x"
    then show "x = y"
      by (cases rule: ereal2_cases[of x y]) auto
  }
  {
    assume "x \<le> y" "y \<le> z"
    then show "x \<le> z"
      by (cases rule: ereal3_cases[of x y z]) auto
  }
qed

end

lemma ereal_dense2: "x < y \<Longrightarrow> \<exists>z. x < ereal z \<and> ereal z < y"
  using lt_ex gt_ex dense by (cases x y rule: ereal2_cases) auto

instance ereal :: dense_linorder
  by default (blast dest: ereal_dense2)

instance ereal :: ordered_ab_semigroup_add
proof
  fix a b c :: ereal
  assume "a \<le> b"
  then show "c + a \<le> c + b"
    by (cases rule: ereal3_cases[of a b c]) auto
qed

lemma real_of_ereal_positive_mono:
  fixes x y :: ereal
  shows "0 \<le> x \<Longrightarrow> x \<le> y \<Longrightarrow> y \<noteq> \<infinity> \<Longrightarrow> real x \<le> real y"
  by (cases rule: ereal2_cases[of x y]) auto

lemma ereal_MInfty_lessI[intro, simp]:
  fixes a :: ereal
  shows "a \<noteq> -\<infinity> \<Longrightarrow> -\<infinity> < a"
  by (cases a) auto

lemma ereal_less_PInfty[intro, simp]:
  fixes a :: ereal
  shows "a \<noteq> \<infinity> \<Longrightarrow> a < \<infinity>"
  by (cases a) auto

lemma ereal_less_ereal_Ex:
  fixes a b :: ereal
  shows "x < ereal r \<longleftrightarrow> x = -\<infinity> \<or> (\<exists>p. p < r \<and> x = ereal p)"
  by (cases x) auto

lemma less_PInf_Ex_of_nat: "x \<noteq> \<infinity> \<longleftrightarrow> (\<exists>n::nat. x < ereal (real n))"
proof (cases x)
  case (real r)
  then show ?thesis
    using reals_Archimedean2[of r] by simp
qed simp_all

lemma ereal_add_mono:
  fixes a b c d :: ereal
  assumes "a \<le> b"
    and "c \<le> d"
  shows "a + c \<le> b + d"
  using assms
  apply (cases a)
  apply (cases rule: ereal3_cases[of b c d], auto)
  apply (cases rule: ereal3_cases[of b c d], auto)
  done

lemma ereal_minus_le_minus[simp]:
  fixes a b :: ereal
  shows "- a \<le> - b \<longleftrightarrow> b \<le> a"
  by (cases rule: ereal2_cases[of a b]) auto

lemma ereal_minus_less_minus[simp]:
  fixes a b :: ereal
  shows "- a < - b \<longleftrightarrow> b < a"
  by (cases rule: ereal2_cases[of a b]) auto

lemma ereal_le_real_iff:
  "x \<le> real y \<longleftrightarrow> (\<bar>y\<bar> \<noteq> \<infinity> \<longrightarrow> ereal x \<le> y) \<and> (\<bar>y\<bar> = \<infinity> \<longrightarrow> x \<le> 0)"
  by (cases y) auto

lemma real_le_ereal_iff:
  "real y \<le> x \<longleftrightarrow> (\<bar>y\<bar> \<noteq> \<infinity> \<longrightarrow> y \<le> ereal x) \<and> (\<bar>y\<bar> = \<infinity> \<longrightarrow> 0 \<le> x)"
  by (cases y) auto

lemma ereal_less_real_iff:
  "x < real y \<longleftrightarrow> (\<bar>y\<bar> \<noteq> \<infinity> \<longrightarrow> ereal x < y) \<and> (\<bar>y\<bar> = \<infinity> \<longrightarrow> x < 0)"
  by (cases y) auto

lemma real_less_ereal_iff:
  "real y < x \<longleftrightarrow> (\<bar>y\<bar> \<noteq> \<infinity> \<longrightarrow> y < ereal x) \<and> (\<bar>y\<bar> = \<infinity> \<longrightarrow> 0 < x)"
  by (cases y) auto

lemma real_of_ereal_pos:
  fixes x :: ereal
  shows "0 \<le> x \<Longrightarrow> 0 \<le> real x" by (cases x) auto

lemmas real_of_ereal_ord_simps =
  ereal_le_real_iff real_le_ereal_iff ereal_less_real_iff real_less_ereal_iff

lemma abs_ereal_ge0[simp]: "0 \<le> x \<Longrightarrow> \<bar>x :: ereal\<bar> = x"
  by (cases x) auto

lemma abs_ereal_less0[simp]: "x < 0 \<Longrightarrow> \<bar>x :: ereal\<bar> = -x"
  by (cases x) auto

lemma abs_ereal_pos[simp]: "0 \<le> \<bar>x :: ereal\<bar>"
  by (cases x) auto

lemma real_of_ereal_le_0[simp]: "real (x :: ereal) \<le> 0 \<longleftrightarrow> x \<le> 0 \<or> x = \<infinity>"
  by (cases x) auto

lemma abs_real_of_ereal[simp]: "\<bar>real (x :: ereal)\<bar> = real \<bar>x\<bar>"
  by (cases x) auto

lemma zero_less_real_of_ereal:
  fixes x :: ereal
  shows "0 < real x \<longleftrightarrow> 0 < x \<and> x \<noteq> \<infinity>"
  by (cases x) auto

lemma ereal_0_le_uminus_iff[simp]:
  fixes a :: ereal
  shows "0 \<le> - a \<longleftrightarrow> a \<le> 0"
  by (cases rule: ereal2_cases[of a]) auto

lemma ereal_uminus_le_0_iff[simp]:
  fixes a :: ereal
  shows "- a \<le> 0 \<longleftrightarrow> 0 \<le> a"
  by (cases rule: ereal2_cases[of a]) auto

lemma ereal_add_strict_mono:
  fixes a b c d :: ereal
  assumes "a = b"
    and "0 \<le> a"
    and "a \<noteq> \<infinity>"
    and "c < d"
  shows "a + c < b + d"
  using assms
  by (cases rule: ereal3_cases[case_product ereal_cases, of a b c d]) auto

lemma ereal_less_add:
  fixes a b c :: ereal
  shows "\<bar>a\<bar> \<noteq> \<infinity> \<Longrightarrow> c < b \<Longrightarrow> a + c < a + b"
  by (cases rule: ereal2_cases[of b c]) auto

lemma ereal_add_nonneg_eq_0_iff:
  fixes a b :: ereal
  shows "0 \<le> a \<Longrightarrow> 0 \<le> b \<Longrightarrow> a + b = 0 \<longleftrightarrow> a = 0 \<and> b = 0"
  by (cases a b rule: ereal2_cases) auto

lemma ereal_uminus_eq_reorder: "- a = b \<longleftrightarrow> a = (-b::ereal)"
  by auto

lemma ereal_uminus_less_reorder: "- a < b \<longleftrightarrow> -b < (a::ereal)"
  by (subst (3) ereal_uminus_uminus[symmetric]) (simp only: ereal_minus_less_minus)

lemma ereal_uminus_le_reorder: "- a \<le> b \<longleftrightarrow> -b \<le> (a::ereal)"
  by (subst (3) ereal_uminus_uminus[symmetric]) (simp only: ereal_minus_le_minus)

lemmas ereal_uminus_reorder =
  ereal_uminus_eq_reorder ereal_uminus_less_reorder ereal_uminus_le_reorder

lemma ereal_bot:
  fixes x :: ereal
  assumes "\<And>B. x \<le> ereal B"
  shows "x = - \<infinity>"
proof (cases x)
  case (real r)
  with assms[of "r - 1"] show ?thesis
    by auto
next
  case PInf
  with assms[of 0] show ?thesis
    by auto
next
  case MInf
  then show ?thesis
    by simp
qed

lemma ereal_top:
  fixes x :: ereal
  assumes "\<And>B. x \<ge> ereal B"
  shows "x = \<infinity>"
proof (cases x)
  case (real r)
  with assms[of "r + 1"] show ?thesis
    by auto
next
  case MInf
  with assms[of 0] show ?thesis
    by auto
next
  case PInf
  then show ?thesis
    by simp
qed

lemma
  shows ereal_max[simp]: "ereal (max x y) = max (ereal x) (ereal y)"
    and ereal_min[simp]: "ereal (min x y) = min (ereal x) (ereal y)"
  by (simp_all add: min_def max_def)

lemma ereal_max_0: "max 0 (ereal r) = ereal (max 0 r)"
  by (auto simp: zero_ereal_def)

lemma
  fixes f :: "nat \<Rightarrow> ereal"
  shows ereal_incseq_uminus[simp]: "incseq (\<lambda>x. - f x) \<longleftrightarrow> decseq f"
    and ereal_decseq_uminus[simp]: "decseq (\<lambda>x. - f x) \<longleftrightarrow> incseq f"
  unfolding decseq_def incseq_def by auto

lemma incseq_ereal: "incseq f \<Longrightarrow> incseq (\<lambda>x. ereal (f x))"
  unfolding incseq_def by auto

lemma ereal_add_nonneg_nonneg:
  fixes a b :: ereal
  shows "0 \<le> a \<Longrightarrow> 0 \<le> b \<Longrightarrow> 0 \<le> a + b"
  using add_mono[of 0 a 0 b] by simp

lemma image_eqD: "f ` A = B \<Longrightarrow> \<forall>x\<in>A. f x \<in> B"
  by auto

lemma incseq_setsumI:
  fixes f :: "nat \<Rightarrow> 'a::{comm_monoid_add,ordered_ab_semigroup_add}"
  assumes "\<And>i. 0 \<le> f i"
  shows "incseq (\<lambda>i. setsum f {..< i})"
proof (intro incseq_SucI)
  fix n
  have "setsum f {..< n} + 0 \<le> setsum f {..<n} + f n"
    using assms by (rule add_left_mono)
  then show "setsum f {..< n} \<le> setsum f {..< Suc n}"
    by auto
qed

lemma incseq_setsumI2:
  fixes f :: "'i \<Rightarrow> nat \<Rightarrow> 'a::{comm_monoid_add,ordered_ab_semigroup_add}"
  assumes "\<And>n. n \<in> A \<Longrightarrow> incseq (f n)"
  shows "incseq (\<lambda>i. \<Sum>n\<in>A. f n i)"
  using assms
  unfolding incseq_def by (auto intro: setsum_mono)


subsubsection "Multiplication"

instantiation ereal :: "{comm_monoid_mult,sgn}"
begin

function sgn_ereal :: "ereal \<Rightarrow> ereal" where
  "sgn (ereal r) = ereal (sgn r)"
| "sgn (\<infinity>::ereal) = 1"
| "sgn (-\<infinity>::ereal) = -1"
by (auto intro: ereal_cases)
termination by default (rule wf_empty)

function times_ereal where
  "ereal r * ereal p = ereal (r * p)"
| "ereal r * \<infinity> = (if r = 0 then 0 else if r > 0 then \<infinity> else -\<infinity>)"
| "\<infinity> * ereal r = (if r = 0 then 0 else if r > 0 then \<infinity> else -\<infinity>)"
| "ereal r * -\<infinity> = (if r = 0 then 0 else if r > 0 then -\<infinity> else \<infinity>)"
| "-\<infinity> * ereal r = (if r = 0 then 0 else if r > 0 then -\<infinity> else \<infinity>)"
| "(\<infinity>::ereal) * \<infinity> = \<infinity>"
| "-(\<infinity>::ereal) * \<infinity> = -\<infinity>"
| "(\<infinity>::ereal) * -\<infinity> = -\<infinity>"
| "-(\<infinity>::ereal) * -\<infinity> = \<infinity>"
proof -
  case (goal1 P x)
  then obtain a b where "x = (a, b)"
    by (cases x) auto
  with goal1 show P
    by (cases rule: ereal2_cases[of a b]) auto
qed simp_all
termination by (relation "{}") simp

instance
proof
  fix a b c :: ereal
  show "1 * a = a"
    by (cases a) (simp_all add: one_ereal_def)
  show "a * b = b * a"
    by (cases rule: ereal2_cases[of a b]) simp_all
  show "a * b * c = a * (b * c)"
    by (cases rule: ereal3_cases[of a b c])
       (simp_all add: zero_ereal_def zero_less_mult_iff)
qed

end

lemma real_ereal_1[simp]: "real (1::ereal) = 1"
  unfolding one_ereal_def by simp

lemma real_of_ereal_le_1:
  fixes a :: ereal
  shows "a \<le> 1 \<Longrightarrow> real a \<le> 1"
  by (cases a) (auto simp: one_ereal_def)

lemma abs_ereal_one[simp]: "\<bar>1\<bar> = (1::ereal)"
  unfolding one_ereal_def by simp

lemma ereal_mult_zero[simp]:
  fixes a :: ereal
  shows "a * 0 = 0"
  by (cases a) (simp_all add: zero_ereal_def)

lemma ereal_zero_mult[simp]:
  fixes a :: ereal
  shows "0 * a = 0"
  by (cases a) (simp_all add: zero_ereal_def)

lemma ereal_m1_less_0[simp]: "-(1::ereal) < 0"
  by (simp add: zero_ereal_def one_ereal_def)

lemma ereal_times[simp]:
  "1 \<noteq> (\<infinity>::ereal)" "(\<infinity>::ereal) \<noteq> 1"
  "1 \<noteq> -(\<infinity>::ereal)" "-(\<infinity>::ereal) \<noteq> 1"
  by (auto simp add: times_ereal_def one_ereal_def)

lemma ereal_plus_1[simp]:
  "1 + ereal r = ereal (r + 1)"
  "ereal r + 1 = ereal (r + 1)"
  "1 + -(\<infinity>::ereal) = -\<infinity>"
  "-(\<infinity>::ereal) + 1 = -\<infinity>"
  unfolding one_ereal_def by auto

lemma ereal_zero_times[simp]:
  fixes a b :: ereal
  shows "a * b = 0 \<longleftrightarrow> a = 0 \<or> b = 0"
  by (cases rule: ereal2_cases[of a b]) auto

lemma ereal_mult_eq_PInfty[simp]:
  "a * b = (\<infinity>::ereal) \<longleftrightarrow>
    (a = \<infinity> \<and> b > 0) \<or> (a > 0 \<and> b = \<infinity>) \<or> (a = -\<infinity> \<and> b < 0) \<or> (a < 0 \<and> b = -\<infinity>)"
  by (cases rule: ereal2_cases[of a b]) auto

lemma ereal_mult_eq_MInfty[simp]:
  "a * b = -(\<infinity>::ereal) \<longleftrightarrow>
    (a = \<infinity> \<and> b < 0) \<or> (a < 0 \<and> b = \<infinity>) \<or> (a = -\<infinity> \<and> b > 0) \<or> (a > 0 \<and> b = -\<infinity>)"
  by (cases rule: ereal2_cases[of a b]) auto

lemma ereal_abs_mult: "\<bar>x * y :: ereal\<bar> = \<bar>x\<bar> * \<bar>y\<bar>"
  by (cases x y rule: ereal2_cases) (auto simp: abs_mult)

lemma ereal_0_less_1[simp]: "0 < (1::ereal)"
  by (simp_all add: zero_ereal_def one_ereal_def)

lemma ereal_mult_minus_left[simp]:
  fixes a b :: ereal
  shows "-a * b = - (a * b)"
  by (cases rule: ereal2_cases[of a b]) auto

lemma ereal_mult_minus_right[simp]:
  fixes a b :: ereal
  shows "a * -b = - (a * b)"
  by (cases rule: ereal2_cases[of a b]) auto

lemma ereal_mult_infty[simp]:
  "a * (\<infinity>::ereal) = (if a = 0 then 0 else if 0 < a then \<infinity> else - \<infinity>)"
  by (cases a) auto

lemma ereal_infty_mult[simp]:
  "(\<infinity>::ereal) * a = (if a = 0 then 0 else if 0 < a then \<infinity> else - \<infinity>)"
  by (cases a) auto

lemma ereal_mult_strict_right_mono:
  assumes "a < b"
    and "0 < c"
    and "c < (\<infinity>::ereal)"
  shows "a * c < b * c"
  using assms
  by (cases rule: ereal3_cases[of a b c]) (auto simp: zero_le_mult_iff)

lemma ereal_mult_strict_left_mono:
  "a < b \<Longrightarrow> 0 < c \<Longrightarrow> c < (\<infinity>::ereal) \<Longrightarrow> c * a < c * b"
  using ereal_mult_strict_right_mono
  by (simp add: mult_commute[of c])

lemma ereal_mult_right_mono:
  fixes a b c :: ereal
  shows "a \<le> b \<Longrightarrow> 0 \<le> c \<Longrightarrow> a * c \<le> b * c"
  using assms
  apply (cases "c = 0")
  apply simp
  apply (cases rule: ereal3_cases[of a b c])
  apply (auto simp: zero_le_mult_iff)
  done

lemma ereal_mult_left_mono:
  fixes a b c :: ereal
  shows "a \<le> b \<Longrightarrow> 0 \<le> c \<Longrightarrow> c * a \<le> c * b"
  using ereal_mult_right_mono
  by (simp add: mult_commute[of c])

lemma zero_less_one_ereal[simp]: "0 \<le> (1::ereal)"
  by (simp add: one_ereal_def zero_ereal_def)

lemma ereal_0_le_mult[simp]: "0 \<le> a \<Longrightarrow> 0 \<le> b \<Longrightarrow> 0 \<le> a * (b :: ereal)"
  by (cases rule: ereal2_cases[of a b]) (auto simp: mult_nonneg_nonneg)

lemma ereal_right_distrib:
  fixes r a b :: ereal
  shows "0 \<le> a \<Longrightarrow> 0 \<le> b \<Longrightarrow> r * (a + b) = r * a + r * b"
  by (cases rule: ereal3_cases[of r a b]) (simp_all add: field_simps)

lemma ereal_left_distrib:
  fixes r a b :: ereal
  shows "0 \<le> a \<Longrightarrow> 0 \<le> b \<Longrightarrow> (a + b) * r = a * r + b * r"
  by (cases rule: ereal3_cases[of r a b]) (simp_all add: field_simps)

lemma ereal_mult_le_0_iff:
  fixes a b :: ereal
  shows "a * b \<le> 0 \<longleftrightarrow> (0 \<le> a \<and> b \<le> 0) \<or> (a \<le> 0 \<and> 0 \<le> b)"
  by (cases rule: ereal2_cases[of a b]) (simp_all add: mult_le_0_iff)

lemma ereal_zero_le_0_iff:
  fixes a b :: ereal
  shows "0 \<le> a * b \<longleftrightarrow> (0 \<le> a \<and> 0 \<le> b) \<or> (a \<le> 0 \<and> b \<le> 0)"
  by (cases rule: ereal2_cases[of a b]) (simp_all add: zero_le_mult_iff)

lemma ereal_mult_less_0_iff:
  fixes a b :: ereal
  shows "a * b < 0 \<longleftrightarrow> (0 < a \<and> b < 0) \<or> (a < 0 \<and> 0 < b)"
  by (cases rule: ereal2_cases[of a b]) (simp_all add: mult_less_0_iff)

lemma ereal_zero_less_0_iff:
  fixes a b :: ereal
  shows "0 < a * b \<longleftrightarrow> (0 < a \<and> 0 < b) \<or> (a < 0 \<and> b < 0)"
  by (cases rule: ereal2_cases[of a b]) (simp_all add: zero_less_mult_iff)

lemma ereal_left_mult_cong:
  fixes a b c :: ereal
  shows "(c \<noteq> 0 \<Longrightarrow> a = b) \<Longrightarrow> c * a = c * b"
  by (cases "c = 0") simp_all

lemma ereal_right_mult_cong:
  fixes a b c :: ereal
  shows "(c \<noteq> 0 \<Longrightarrow> a = b) \<Longrightarrow> a * c = b * c"
  by (cases "c = 0") simp_all

lemma ereal_distrib:
  fixes a b c :: ereal
  assumes "a \<noteq> \<infinity> \<or> b \<noteq> -\<infinity>"
    and "a \<noteq> -\<infinity> \<or> b \<noteq> \<infinity>"
    and "\<bar>c\<bar> \<noteq> \<infinity>"
  shows "(a + b) * c = a * c + b * c"
  using assms
  by (cases rule: ereal3_cases[of a b c]) (simp_all add: field_simps)

lemma numeral_eq_ereal [simp]: "numeral w = ereal (numeral w)"
  apply (induct w rule: num_induct)
  apply (simp only: numeral_One one_ereal_def)
  apply (simp only: numeral_inc ereal_plus_1)
  done

lemma ereal_le_epsilon:
  fixes x y :: ereal
  assumes "\<forall>e. 0 < e \<longrightarrow> x \<le> y + e"
  shows "x \<le> y"
proof -
  {
    assume a: "\<exists>r. y = ereal r"
    then obtain r where r_def: "y = ereal r"
      by auto
    {
      assume "x = -\<infinity>"
      then have ?thesis by auto
    }
    moreover
    {
      assume "x \<noteq> -\<infinity>"
      then obtain p where p_def: "x = ereal p"
      using a assms[rule_format, of 1]
        by (cases x) auto
      {
        fix e
        have "0 < e \<longrightarrow> p \<le> r + e"
          using assms[rule_format, of "ereal e"] p_def r_def by auto
      }
      then have "p \<le> r"
        apply (subst field_le_epsilon)
        apply auto
        done
      then have ?thesis
        using r_def p_def by auto
    }
    ultimately have ?thesis
      by blast
  }
  moreover
  {
    assume "y = -\<infinity> | y = \<infinity>"
    then have ?thesis
      using assms[rule_format, of 1] by (cases x) auto
  }
  ultimately show ?thesis
    by (cases y) auto
qed

lemma ereal_le_epsilon2:
  fixes x y :: ereal
  assumes "\<forall>e. 0 < e \<longrightarrow> x \<le> y + ereal e"
  shows "x \<le> y"
proof -
  {
    fix e :: ereal
    assume "e > 0"
    {
      assume "e = \<infinity>"
      then have "x \<le> y + e"
        by auto
    }
    moreover
    {
      assume "e \<noteq> \<infinity>"
      then obtain r where "e = ereal r"
        using `e > 0` by (cases e) auto
      then have "x \<le> y + e"
        using assms[rule_format, of r] `e>0` by auto
    }
    ultimately have "x \<le> y + e"
      by blast
  }
  then show ?thesis
    using ereal_le_epsilon by auto
qed

lemma ereal_le_real:
  fixes x y :: ereal
  assumes "\<forall>z. x \<le> ereal z \<longrightarrow> y \<le> ereal z"
  shows "y \<le> x"
  by (metis assms ereal_bot ereal_cases ereal_infty_less_eq(2) ereal_less_eq(1) linorder_le_cases)

lemma setprod_ereal_0:
  fixes f :: "'a \<Rightarrow> ereal"
  shows "(\<Prod>i\<in>A. f i) = 0 \<longleftrightarrow> finite A \<and> (\<exists>i\<in>A. f i = 0)"
proof (cases "finite A")
  case True
  then show ?thesis by (induct A) auto
next
  case False
  then show ?thesis by auto
qed

lemma setprod_ereal_pos:
  fixes f :: "'a \<Rightarrow> ereal"
  assumes pos: "\<And>i. i \<in> I \<Longrightarrow> 0 \<le> f i"
  shows "0 \<le> (\<Prod>i\<in>I. f i)"
proof (cases "finite I")
  case True
  from this pos show ?thesis
    by induct auto
next
  case False
  then show ?thesis by simp
qed

lemma setprod_PInf:
  fixes f :: "'a \<Rightarrow> ereal"
  assumes "\<And>i. i \<in> I \<Longrightarrow> 0 \<le> f i"
  shows "(\<Prod>i\<in>I. f i) = \<infinity> \<longleftrightarrow> finite I \<and> (\<exists>i\<in>I. f i = \<infinity>) \<and> (\<forall>i\<in>I. f i \<noteq> 0)"
proof (cases "finite I")
  case True
  from this assms show ?thesis
  proof (induct I)
    case (insert i I)
    then have pos: "0 \<le> f i" "0 \<le> setprod f I"
      by (auto intro!: setprod_ereal_pos)
    from insert have "(\<Prod>j\<in>insert i I. f j) = \<infinity> \<longleftrightarrow> setprod f I * f i = \<infinity>"
      by auto
    also have "\<dots> \<longleftrightarrow> (setprod f I = \<infinity> \<or> f i = \<infinity>) \<and> f i \<noteq> 0 \<and> setprod f I \<noteq> 0"
      using setprod_ereal_pos[of I f] pos
      by (cases rule: ereal2_cases[of "f i" "setprod f I"]) auto
    also have "\<dots> \<longleftrightarrow> finite (insert i I) \<and> (\<exists>j\<in>insert i I. f j = \<infinity>) \<and> (\<forall>j\<in>insert i I. f j \<noteq> 0)"
      using insert by (auto simp: setprod_ereal_0)
    finally show ?case .
  qed simp
next
  case False
  then show ?thesis by simp
qed

lemma setprod_ereal: "(\<Prod>i\<in>A. ereal (f i)) = ereal (setprod f A)"
proof (cases "finite A")
  case True
  then show ?thesis
    by induct (auto simp: one_ereal_def)
next
  case False
  then show ?thesis
    by (simp add: one_ereal_def)
qed


subsubsection {* Power *}

lemma ereal_power[simp]: "(ereal x) ^ n = ereal (x^n)"
  by (induct n) (auto simp: one_ereal_def)

lemma ereal_power_PInf[simp]: "(\<infinity>::ereal) ^ n = (if n = 0 then 1 else \<infinity>)"
  by (induct n) (auto simp: one_ereal_def)

lemma ereal_power_uminus[simp]:
  fixes x :: ereal
  shows "(- x) ^ n = (if even n then x ^ n else - (x^n))"
  by (induct n) (auto simp: one_ereal_def)

lemma ereal_power_numeral[simp]:
  "(numeral num :: ereal) ^ n = ereal (numeral num ^ n)"
  by (induct n) (auto simp: one_ereal_def)

lemma zero_le_power_ereal[simp]:
  fixes a :: ereal
  assumes "0 \<le> a"
  shows "0 \<le> a ^ n"
  using assms by (induct n) (auto simp: ereal_zero_le_0_iff)


subsubsection {* Subtraction *}

lemma ereal_minus_minus_image[simp]:
  fixes S :: "ereal set"
  shows "uminus ` uminus ` S = S"
  by (auto simp: image_iff)

lemma ereal_uminus_lessThan[simp]:
  fixes a :: ereal
  shows "uminus ` {..<a} = {-a<..}"
proof -
  {
    fix x
    assume "-a < x"
    then have "- x < - (- a)"
      by (simp del: ereal_uminus_uminus)
    then have "- x < a"
      by simp
  }
  then show ?thesis
    by force
qed

lemma ereal_uminus_greaterThan[simp]: "uminus ` {(a::ereal)<..} = {..<-a}"
  by (metis ereal_uminus_lessThan ereal_uminus_uminus ereal_minus_minus_image)

instantiation ereal :: minus
begin

definition "x - y = x + -(y::ereal)"
instance ..

end

lemma ereal_minus[simp]:
  "ereal r - ereal p = ereal (r - p)"
  "-\<infinity> - ereal r = -\<infinity>"
  "ereal r - \<infinity> = -\<infinity>"
  "(\<infinity>::ereal) - x = \<infinity>"
  "-(\<infinity>::ereal) - \<infinity> = -\<infinity>"
  "x - -y = x + y"
  "x - 0 = x"
  "0 - x = -x"
  by (simp_all add: minus_ereal_def)

lemma ereal_x_minus_x[simp]: "x - x = (if \<bar>x\<bar> = \<infinity> then \<infinity> else 0::ereal)"
  by (cases x) simp_all

lemma ereal_eq_minus_iff:
  fixes x y z :: ereal
  shows "x = z - y \<longleftrightarrow>
    (\<bar>y\<bar> \<noteq> \<infinity> \<longrightarrow> x + y = z) \<and>
    (y = -\<infinity> \<longrightarrow> x = \<infinity>) \<and>
    (y = \<infinity> \<longrightarrow> z = \<infinity> \<longrightarrow> x = \<infinity>) \<and>
    (y = \<infinity> \<longrightarrow> z \<noteq> \<infinity> \<longrightarrow> x = -\<infinity>)"
  by (cases rule: ereal3_cases[of x y z]) auto

lemma ereal_eq_minus:
  fixes x y z :: ereal
  shows "\<bar>y\<bar> \<noteq> \<infinity> \<Longrightarrow> x = z - y \<longleftrightarrow> x + y = z"
  by (auto simp: ereal_eq_minus_iff)

lemma ereal_less_minus_iff:
  fixes x y z :: ereal
  shows "x < z - y \<longleftrightarrow>
    (y = \<infinity> \<longrightarrow> z = \<infinity> \<and> x \<noteq> \<infinity>) \<and>
    (y = -\<infinity> \<longrightarrow> x \<noteq> \<infinity>) \<and>
    (\<bar>y\<bar> \<noteq> \<infinity>\<longrightarrow> x + y < z)"
  by (cases rule: ereal3_cases[of x y z]) auto

lemma ereal_less_minus:
  fixes x y z :: ereal
  shows "\<bar>y\<bar> \<noteq> \<infinity> \<Longrightarrow> x < z - y \<longleftrightarrow> x + y < z"
  by (auto simp: ereal_less_minus_iff)

lemma ereal_le_minus_iff:
  fixes x y z :: ereal
  shows "x \<le> z - y \<longleftrightarrow> (y = \<infinity> \<longrightarrow> z \<noteq> \<infinity> \<longrightarrow> x = -\<infinity>) \<and> (\<bar>y\<bar> \<noteq> \<infinity> \<longrightarrow> x + y \<le> z)"
  by (cases rule: ereal3_cases[of x y z]) auto

lemma ereal_le_minus:
  fixes x y z :: ereal
  shows "\<bar>y\<bar> \<noteq> \<infinity> \<Longrightarrow> x \<le> z - y \<longleftrightarrow> x + y \<le> z"
  by (auto simp: ereal_le_minus_iff)

lemma ereal_minus_less_iff:
  fixes x y z :: ereal
  shows "x - y < z \<longleftrightarrow> y \<noteq> -\<infinity> \<and> (y = \<infinity> \<longrightarrow> x \<noteq> \<infinity> \<and> z \<noteq> -\<infinity>) \<and> (y \<noteq> \<infinity> \<longrightarrow> x < z + y)"
  by (cases rule: ereal3_cases[of x y z]) auto

lemma ereal_minus_less:
  fixes x y z :: ereal
  shows "\<bar>y\<bar> \<noteq> \<infinity> \<Longrightarrow> x - y < z \<longleftrightarrow> x < z + y"
  by (auto simp: ereal_minus_less_iff)

lemma ereal_minus_le_iff:
  fixes x y z :: ereal
  shows "x - y \<le> z \<longleftrightarrow>
    (y = -\<infinity> \<longrightarrow> z = \<infinity>) \<and>
    (y = \<infinity> \<longrightarrow> x = \<infinity> \<longrightarrow> z = \<infinity>) \<and>
    (\<bar>y\<bar> \<noteq> \<infinity> \<longrightarrow> x \<le> z + y)"
  by (cases rule: ereal3_cases[of x y z]) auto

lemma ereal_minus_le:
  fixes x y z :: ereal
  shows "\<bar>y\<bar> \<noteq> \<infinity> \<Longrightarrow> x - y \<le> z \<longleftrightarrow> x \<le> z + y"
  by (auto simp: ereal_minus_le_iff)

lemma ereal_minus_eq_minus_iff:
  fixes a b c :: ereal
  shows "a - b = a - c \<longleftrightarrow>
    b = c \<or> a = \<infinity> \<or> (a = -\<infinity> \<and> b \<noteq> -\<infinity> \<and> c \<noteq> -\<infinity>)"
  by (cases rule: ereal3_cases[of a b c]) auto

lemma ereal_add_le_add_iff:
  fixes a b c :: ereal
  shows "c + a \<le> c + b \<longleftrightarrow>
    a \<le> b \<or> c = \<infinity> \<or> (c = -\<infinity> \<and> a \<noteq> \<infinity> \<and> b \<noteq> \<infinity>)"
  by (cases rule: ereal3_cases[of a b c]) (simp_all add: field_simps)

lemma ereal_mult_le_mult_iff:
  fixes a b c :: ereal
  shows "\<bar>c\<bar> \<noteq> \<infinity> \<Longrightarrow> c * a \<le> c * b \<longleftrightarrow> (0 < c \<longrightarrow> a \<le> b) \<and> (c < 0 \<longrightarrow> b \<le> a)"
  by (cases rule: ereal3_cases[of a b c]) (simp_all add: mult_le_cancel_left)

lemma ereal_minus_mono:
  fixes A B C D :: ereal assumes "A \<le> B" "D \<le> C"
  shows "A - C \<le> B - D"
  using assms
  by (cases rule: ereal3_cases[case_product ereal_cases, of A B C D]) simp_all

lemma real_of_ereal_minus:
  fixes a b :: ereal
  shows "real (a - b) = (if \<bar>a\<bar> = \<infinity> \<or> \<bar>b\<bar> = \<infinity> then 0 else real a - real b)"
  by (cases rule: ereal2_cases[of a b]) auto

lemma ereal_diff_positive:
  fixes a b :: ereal shows "a \<le> b \<Longrightarrow> 0 \<le> b - a"
  by (cases rule: ereal2_cases[of a b]) auto

lemma ereal_between:
  fixes x e :: ereal
  assumes "\<bar>x\<bar> \<noteq> \<infinity>"
    and "0 < e"
  shows "x - e < x"
    and "x < x + e"
  using assms
  apply (cases x, cases e)
  apply auto
  using assms
  apply (cases x, cases e)
  apply auto
  done

lemma ereal_minus_eq_PInfty_iff:
  fixes x y :: ereal
  shows "x - y = \<infinity> \<longleftrightarrow> y = -\<infinity> \<or> x = \<infinity>"
  by (cases x y rule: ereal2_cases) simp_all


subsubsection {* Division *}

instantiation ereal :: inverse
begin

function inverse_ereal where
  "inverse (ereal r) = (if r = 0 then \<infinity> else ereal (inverse r))"
| "inverse (\<infinity>::ereal) = 0"
| "inverse (-\<infinity>::ereal) = 0"
  by (auto intro: ereal_cases)
termination by (relation "{}") simp

definition "x / y = x * inverse (y :: ereal)"

instance ..

end

lemma real_of_ereal_inverse[simp]:
  fixes a :: ereal
  shows "real (inverse a) = 1 / real a"
  by (cases a) (auto simp: inverse_eq_divide)

lemma ereal_inverse[simp]:
  "inverse (0::ereal) = \<infinity>"
  "inverse (1::ereal) = 1"
  by (simp_all add: one_ereal_def zero_ereal_def)

lemma ereal_divide[simp]:
  "ereal r / ereal p = (if p = 0 then ereal r * \<infinity> else ereal (r / p))"
  unfolding divide_ereal_def by (auto simp: divide_real_def)

lemma ereal_divide_same[simp]:
  fixes x :: ereal
  shows "x / x = (if \<bar>x\<bar> = \<infinity> \<or> x = 0 then 0 else 1)"
  by (cases x) (simp_all add: divide_real_def divide_ereal_def one_ereal_def)

lemma ereal_inv_inv[simp]:
  fixes x :: ereal
  shows "inverse (inverse x) = (if x \<noteq> -\<infinity> then x else \<infinity>)"
  by (cases x) auto

lemma ereal_inverse_minus[simp]:
  fixes x :: ereal
  shows "inverse (- x) = (if x = 0 then \<infinity> else -inverse x)"
  by (cases x) simp_all

lemma ereal_uminus_divide[simp]:
  fixes x y :: ereal
  shows "- x / y = - (x / y)"
  unfolding divide_ereal_def by simp

lemma ereal_divide_Infty[simp]:
  fixes x :: ereal
  shows "x / \<infinity> = 0" "x / -\<infinity> = 0"
  unfolding divide_ereal_def by simp_all

lemma ereal_divide_one[simp]: "x / 1 = (x::ereal)"
  unfolding divide_ereal_def by simp

lemma ereal_divide_ereal[simp]: "\<infinity> / ereal r = (if 0 \<le> r then \<infinity> else -\<infinity>)"
  unfolding divide_ereal_def by simp

lemma zero_le_divide_ereal[simp]:
  fixes a :: ereal
  assumes "0 \<le> a"
    and "0 \<le> b"
  shows "0 \<le> a / b"
  using assms by (cases rule: ereal2_cases[of a b]) (auto simp: zero_le_divide_iff)

lemma ereal_le_divide_pos:
  fixes x y z :: ereal
  shows "x > 0 \<Longrightarrow> x \<noteq> \<infinity> \<Longrightarrow> y \<le> z / x \<longleftrightarrow> x * y \<le> z"
  by (cases rule: ereal3_cases[of x y z]) (auto simp: field_simps)

lemma ereal_divide_le_pos:
  fixes x y z :: ereal
  shows "x > 0 \<Longrightarrow> x \<noteq> \<infinity> \<Longrightarrow> z / x \<le> y \<longleftrightarrow> z \<le> x * y"
  by (cases rule: ereal3_cases[of x y z]) (auto simp: field_simps)

lemma ereal_le_divide_neg:
  fixes x y z :: ereal
  shows "x < 0 \<Longrightarrow> x \<noteq> -\<infinity> \<Longrightarrow> y \<le> z / x \<longleftrightarrow> z \<le> x * y"
  by (cases rule: ereal3_cases[of x y z]) (auto simp: field_simps)

lemma ereal_divide_le_neg:
  fixes x y z :: ereal
  shows "x < 0 \<Longrightarrow> x \<noteq> -\<infinity> \<Longrightarrow> z / x \<le> y \<longleftrightarrow> x * y \<le> z"
  by (cases rule: ereal3_cases[of x y z]) (auto simp: field_simps)

lemma ereal_inverse_antimono_strict:
  fixes x y :: ereal
  shows "0 \<le> x \<Longrightarrow> x < y \<Longrightarrow> inverse y < inverse x"
  by (cases rule: ereal2_cases[of x y]) auto

lemma ereal_inverse_antimono:
  fixes x y :: ereal
  shows "0 \<le> x \<Longrightarrow> x \<le> y \<Longrightarrow> inverse y \<le> inverse x"
  by (cases rule: ereal2_cases[of x y]) auto

lemma inverse_inverse_Pinfty_iff[simp]:
  fixes x :: ereal
  shows "inverse x = \<infinity> \<longleftrightarrow> x = 0"
  by (cases x) auto

lemma ereal_inverse_eq_0:
  fixes x :: ereal
  shows "inverse x = 0 \<longleftrightarrow> x = \<infinity> \<or> x = -\<infinity>"
  by (cases x) auto

lemma ereal_0_gt_inverse:
  fixes x :: ereal
  shows "0 < inverse x \<longleftrightarrow> x \<noteq> \<infinity> \<and> 0 \<le> x"
  by (cases x) auto

lemma ereal_mult_less_right:
  fixes a b c :: ereal
  assumes "b * a < c * a"
    and "0 < a"
    and "a < \<infinity>"
  shows "b < c"
  using assms
  by (cases rule: ereal3_cases[of a b c])
     (auto split: split_if_asm simp: zero_less_mult_iff zero_le_mult_iff)

lemma ereal_power_divide:
  fixes x y :: ereal
  shows "y \<noteq> 0 \<Longrightarrow> (x / y) ^ n = x^n / y^n"
  by (cases rule: ereal2_cases[of x y])
     (auto simp: one_ereal_def zero_ereal_def power_divide not_le
                 power_less_zero_eq zero_le_power_iff)

lemma ereal_le_mult_one_interval:
  fixes x y :: ereal
  assumes y: "y \<noteq> -\<infinity>"
  assumes z: "\<And>z. 0 < z \<Longrightarrow> z < 1 \<Longrightarrow> z * x \<le> y"
  shows "x \<le> y"
proof (cases x)
  case PInf
  with z[of "1 / 2"] show "x \<le> y"
    by (simp add: one_ereal_def)
next
  case (real r)
  note r = this
  show "x \<le> y"
  proof (cases y)
    case (real p)
    note p = this
    have "r \<le> p"
    proof (rule field_le_mult_one_interval)
      fix z :: real
      assume "0 < z" and "z < 1"
      with z[of "ereal z"] show "z * r \<le> p"
        using p r by (auto simp: zero_le_mult_iff one_ereal_def)
    qed
    then show "x \<le> y"
      using p r by simp
  qed (insert y, simp_all)
qed simp

lemma ereal_divide_right_mono[simp]:
  fixes x y z :: ereal
  assumes "x \<le> y"
    and "0 < z"
  shows "x / z \<le> y / z"
  using assms by (cases x y z rule: ereal3_cases) (auto intro: divide_right_mono)

lemma ereal_divide_left_mono[simp]:
  fixes x y z :: ereal
  assumes "y \<le> x"
    and "0 < z"
    and "0 < x * y"
  shows "z / x \<le> z / y"
  using assms
  by (cases x y z rule: ereal3_cases)
     (auto intro: divide_left_mono simp: field_simps zero_less_mult_iff mult_less_0_iff split: split_if_asm)

lemma ereal_divide_zero_left[simp]:
  fixes a :: ereal
  shows "0 / a = 0"
  by (cases a) (auto simp: zero_ereal_def)

lemma ereal_times_divide_eq_left[simp]:
  fixes a b c :: ereal
  shows "b / c * a = b * a / c"
  by (cases a b c rule: ereal3_cases) (auto simp: field_simps zero_less_mult_iff mult_less_0_iff)


subsection "Complete lattice"

instantiation ereal :: lattice
begin

definition [simp]: "sup x y = (max x y :: ereal)"
definition [simp]: "inf x y = (min x y :: ereal)"
instance by default simp_all

end

instantiation ereal :: complete_lattice
begin

definition "bot = (-\<infinity>::ereal)"
definition "top = (\<infinity>::ereal)"

definition "Sup S = (SOME x :: ereal. (\<forall>y\<in>S. y \<le> x) \<and> (\<forall>z. (\<forall>y\<in>S. y \<le> z) \<longrightarrow> x \<le> z))"
definition "Inf S = (SOME x :: ereal. (\<forall>y\<in>S. x \<le> y) \<and> (\<forall>z. (\<forall>y\<in>S. z \<le> y) \<longrightarrow> z \<le> x))"

lemma ereal_complete_Sup:
  fixes S :: "ereal set"
  shows "\<exists>x. (\<forall>y\<in>S. y \<le> x) \<and> (\<forall>z. (\<forall>y\<in>S. y \<le> z) \<longrightarrow> x \<le> z)"
proof (cases "\<exists>x. \<forall>a\<in>S. a \<le> ereal x")
  case True
  then obtain y where y: "\<And>a. a\<in>S \<Longrightarrow> a \<le> ereal y"
    by auto
  then have "\<infinity> \<notin> S"
    by force
  show ?thesis
  proof (cases "S \<noteq> {-\<infinity>} \<and> S \<noteq> {}")
    case True
    with `\<infinity> \<notin> S` obtain x where x: "x \<in> S" "\<bar>x\<bar> \<noteq> \<infinity>"
      by auto
    obtain s where s: "\<forall>x\<in>ereal -` S. x \<le> s" "\<And>z. (\<forall>x\<in>ereal -` S. x \<le> z) \<Longrightarrow> s \<le> z"
    proof (atomize_elim, rule complete_real)
      show "\<exists>x. x \<in> ereal -` S"
        using x by auto
      show "\<exists>z. \<forall>x\<in>ereal -` S. x \<le> z"
        by (auto dest: y intro!: exI[of _ y])
    qed
    show ?thesis
    proof (safe intro!: exI[of _ "ereal s"])
      fix y
      assume "y \<in> S"
      with s `\<infinity> \<notin> S` show "y \<le> ereal s"
        by (cases y) auto
    next
      fix z
      assume "\<forall>y\<in>S. y \<le> z"
      with `S \<noteq> {-\<infinity>} \<and> S \<noteq> {}` show "ereal s \<le> z"
        by (cases z) (auto intro!: s)
    qed
  next
    case False
    then show ?thesis
      by (auto intro!: exI[of _ "-\<infinity>"])
  qed
next
  case False
  then show ?thesis
    by (fastforce intro!: exI[of _ \<infinity>] ereal_top intro: order_trans dest: less_imp_le simp: not_le)
qed

lemma ereal_complete_uminus_eq:
  fixes S :: "ereal set"
  shows "(\<forall>y\<in>uminus`S. y \<le> x) \<and> (\<forall>z. (\<forall>y\<in>uminus`S. y \<le> z) \<longrightarrow> x \<le> z)
     \<longleftrightarrow> (\<forall>y\<in>S. -x \<le> y) \<and> (\<forall>z. (\<forall>y\<in>S. z \<le> y) \<longrightarrow> z \<le> -x)"
  by simp (metis ereal_minus_le_minus ereal_uminus_uminus)

lemma ereal_complete_Inf:
  "\<exists>x. (\<forall>y\<in>S::ereal set. x \<le> y) \<and> (\<forall>z. (\<forall>y\<in>S. z \<le> y) \<longrightarrow> z \<le> x)"
  using ereal_complete_Sup[of "uminus ` S"]
  unfolding ereal_complete_uminus_eq
  by auto

instance
proof
  show "Sup {} = (bot::ereal)"
    apply (auto simp: bot_ereal_def Sup_ereal_def)
    apply (rule some1_equality)
    apply (metis ereal_bot ereal_less_eq(2))
    apply (metis ereal_less_eq(2))
    done
  show "Inf {} = (top::ereal)"
    apply (auto simp: top_ereal_def Inf_ereal_def)
    apply (rule some1_equality)
    apply (metis ereal_top ereal_less_eq(1))
    apply (metis ereal_less_eq(1))
    done
qed (auto intro: someI2_ex ereal_complete_Sup ereal_complete_Inf
  simp: Sup_ereal_def Inf_ereal_def bot_ereal_def top_ereal_def)

end

instance ereal :: complete_linorder ..

instance ereal :: linear_continuum
proof
  show "\<exists>a b::ereal. a \<noteq> b"
    using zero_neq_one by blast
qed

lemma ereal_Sup_uminus_image_eq: "Sup (uminus ` S::ereal set) = - Inf S"
  by (auto intro!: SUP_eqI
           simp: Ball_def[symmetric] ereal_uminus_le_reorder le_Inf_iff
           intro!: complete_lattice_class.Inf_lower2)

lemma ereal_SUP_uminus_eq:
  fixes f :: "'a \<Rightarrow> ereal"
  shows "(SUP x:S. uminus (f x)) = - (INF x:S. f x)"
  using ereal_Sup_uminus_image_eq [of "f ` S"] by (simp add: comp_def)

lemma ereal_inj_on_uminus[intro, simp]: "inj_on uminus (A :: ereal set)"
  by (auto intro!: inj_onI)

lemma ereal_Inf_uminus_image_eq: "Inf (uminus ` S::ereal set) = - Sup S"
  using ereal_Sup_uminus_image_eq[of "uminus ` S"] by simp

lemma ereal_INF_uminus_eq:
  fixes f :: "'a \<Rightarrow> ereal"
  shows "(INF x:S. uminus (f x)) = - (SUP x:S. f x)"
  using ereal_Inf_uminus_image_eq [of "f ` S"] by (simp add: comp_def)

lemma ereal_SUP_not_infty:
  fixes f :: "_ \<Rightarrow> ereal"
  shows "A \<noteq> {} \<Longrightarrow> l \<noteq> -\<infinity> \<Longrightarrow> u \<noteq> \<infinity> \<Longrightarrow> \<forall>a\<in>A. l \<le> f a \<and> f a \<le> u \<Longrightarrow> \<bar>SUPREMUM A f\<bar> \<noteq> \<infinity>"
  using SUP_upper2[of _ A l f] SUP_least[of A f u]
  by (cases "SUPREMUM A f") auto

lemma ereal_INF_not_infty:
  fixes f :: "_ \<Rightarrow> ereal"
  shows "A \<noteq> {} \<Longrightarrow> l \<noteq> -\<infinity> \<Longrightarrow> u \<noteq> \<infinity> \<Longrightarrow> \<forall>a\<in>A. l \<le> f a \<and> f a \<le> u \<Longrightarrow> \<bar>INFIMUM A f\<bar> \<noteq> \<infinity>"
  using INF_lower2[of _ A f u] INF_greatest[of A l f]
  by (cases "INFIMUM A f") auto

lemma ereal_SUP_uminus:
  fixes f :: "'a \<Rightarrow> ereal"
  shows "(SUP i : R. -(f i)) = -(INF i : R. f i)"
  using ereal_Sup_uminus_image_eq[of "f`R"]
  by (simp add: image_image)

lemma ereal_INF_uminus:
  fixes f :: "'a \<Rightarrow> ereal"
  shows "(INF i : R. - f i) = - (SUP i : R. f i)"
  using ereal_SUP_uminus [of _ "\<lambda>x. - f x"] by simp

lemma ereal_image_uminus_shift:
  fixes X Y :: "ereal set"
  shows "uminus ` X = Y \<longleftrightarrow> X = uminus ` Y"
proof
  assume "uminus ` X = Y"
  then have "uminus ` uminus ` X = uminus ` Y"
    by (simp add: inj_image_eq_iff)
  then show "X = uminus ` Y"
    by (simp add: image_image)
qed (simp add: image_image)

lemma Inf_ereal_iff:
  fixes z :: ereal
  shows "(\<And>x. x \<in> X \<Longrightarrow> z \<le> x) \<Longrightarrow> (\<exists>x\<in>X. x < y) \<longleftrightarrow> Inf X < y"
  by (metis complete_lattice_class.Inf_greatest complete_lattice_class.Inf_lower
      less_le_not_le linear order_less_le_trans)

lemma Sup_eq_MInfty:
  fixes S :: "ereal set"
  shows "Sup S = -\<infinity> \<longleftrightarrow> S = {} \<or> S = {-\<infinity>}"
  unfolding bot_ereal_def[symmetric] by auto

lemma Inf_eq_PInfty:
  fixes S :: "ereal set"
  shows "Inf S = \<infinity> \<longleftrightarrow> S = {} \<or> S = {\<infinity>}"
  using Sup_eq_MInfty[of "uminus`S"]
  unfolding ereal_Sup_uminus_image_eq ereal_image_uminus_shift by simp

lemma Inf_eq_MInfty:
  fixes S :: "ereal set"
  shows "-\<infinity> \<in> S \<Longrightarrow> Inf S = -\<infinity>"
  unfolding bot_ereal_def[symmetric] by auto

lemma Sup_eq_PInfty:
  fixes S :: "ereal set"
  shows "\<infinity> \<in> S \<Longrightarrow> Sup S = \<infinity>"
  unfolding top_ereal_def[symmetric] by auto

lemma Sup_ereal_close:
  fixes e :: ereal
  assumes "0 < e"
    and S: "\<bar>Sup S\<bar> \<noteq> \<infinity>" "S \<noteq> {}"
  shows "\<exists>x\<in>S. Sup S - e < x"
  using assms by (cases e) (auto intro!: less_Sup_iff[THEN iffD1])

lemma Inf_ereal_close:
  fixes e :: ereal
  assumes "\<bar>Inf X\<bar> \<noteq> \<infinity>"
    and "0 < e"
  shows "\<exists>x\<in>X. x < Inf X + e"
proof (rule Inf_less_iff[THEN iffD1])
  show "Inf X < Inf X + e"
    using assms by (cases e) auto
qed

lemma SUP_nat_Infty: "(SUP i::nat. ereal (real i)) = \<infinity>"
proof -
  {
    fix x :: ereal
    assume "x \<noteq> \<infinity>"
    then have "\<exists>k::nat. x < ereal (real k)"
    proof (cases x)
      case MInf
      then show ?thesis
        by (intro exI[of _ 0]) auto
    next
      case (real r)
      moreover obtain k :: nat where "r < real k"
        using ex_less_of_nat by (auto simp: real_eq_of_nat)
      ultimately show ?thesis
        by auto
    qed simp
  }
  then show ?thesis
    using SUP_eq_top_iff[of UNIV "\<lambda>n::nat. ereal (real n)"]
    by (auto simp: top_ereal_def)
qed

lemma Inf_less:
  fixes x :: ereal
  assumes "(INF i:A. f i) < x"
  shows "\<exists>i. i \<in> A \<and> f i \<le> x"
proof (rule ccontr)
  assume "\<not> ?thesis"
  then have "\<forall>i\<in>A. f i > x"
    by auto
  then have "(INF i:A. f i) \<ge> x"
    by (subst INF_greatest) auto
  then show False
    using assms by auto
qed

lemma SUP_ereal_le_addI:
  fixes f :: "'i \<Rightarrow> ereal"
  assumes "\<And>i. f i + y \<le> z"
    and "y \<noteq> -\<infinity>"
  shows "SUPREMUM UNIV f + y \<le> z"
proof (cases y)
  case (real r)
  then have "\<And>i. f i \<le> z - y"
    using assms by (simp add: ereal_le_minus_iff)
  then have "SUPREMUM UNIV f \<le> z - y"
    by (rule SUP_least)
  then show ?thesis
    using real by (simp add: ereal_le_minus_iff)
qed (insert assms, auto)

lemma SUP_ereal_add:
  fixes f g :: "nat \<Rightarrow> ereal"
  assumes "incseq f"
    and "incseq g"
    and pos: "\<And>i. f i \<noteq> -\<infinity>" "\<And>i. g i \<noteq> -\<infinity>"
  shows "(SUP i. f i + g i) = SUPREMUM UNIV f + SUPREMUM UNIV g"
proof (rule SUP_eqI)
  fix y
  assume *: "\<And>i. i \<in> UNIV \<Longrightarrow> f i + g i \<le> y"
  have f: "SUPREMUM UNIV f \<noteq> -\<infinity>"
    using pos
    unfolding SUP_def Sup_eq_MInfty
    by (auto dest: image_eqD)
  {
    fix j
    {
      fix i
      have "f i + g j \<le> f i + g (max i j)"
        using `incseq g`[THEN incseqD]
        by (rule add_left_mono) auto
      also have "\<dots> \<le> f (max i j) + g (max i j)"
        using `incseq f`[THEN incseqD]
        by (rule add_right_mono) auto
      also have "\<dots> \<le> y" using * by auto
      finally have "f i + g j \<le> y" .
    }
    then have "SUPREMUM UNIV f + g j \<le> y"
      using assms(4)[of j] by (intro SUP_ereal_le_addI) auto
    then have "g j + SUPREMUM UNIV f \<le> y" by (simp add: ac_simps)
  }
  then have "SUPREMUM UNIV g + SUPREMUM UNIV f \<le> y"
    using f by (rule SUP_ereal_le_addI)
  then show "SUPREMUM UNIV f + SUPREMUM UNIV g \<le> y"
    by (simp add: ac_simps)
qed (auto intro!: add_mono SUP_upper)

lemma SUP_ereal_add_pos:
  fixes f g :: "nat \<Rightarrow> ereal"
  assumes inc: "incseq f" "incseq g"
    and pos: "\<And>i. 0 \<le> f i" "\<And>i. 0 \<le> g i"
  shows "(SUP i. f i + g i) = SUPREMUM UNIV f + SUPREMUM UNIV g"
proof (intro SUP_ereal_add inc)
  fix i
  show "f i \<noteq> -\<infinity>" "g i \<noteq> -\<infinity>"
    using pos[of i] by auto
qed

lemma SUP_ereal_setsum:
  fixes f g :: "'a \<Rightarrow> nat \<Rightarrow> ereal"
  assumes "\<And>n. n \<in> A \<Longrightarrow> incseq (f n)"
    and pos: "\<And>n i. n \<in> A \<Longrightarrow> 0 \<le> f n i"
  shows "(SUP i. \<Sum>n\<in>A. f n i) = (\<Sum>n\<in>A. SUPREMUM UNIV (f n))"
proof (cases "finite A")
  case True
  then show ?thesis using assms
    by induct (auto simp: incseq_setsumI2 setsum_nonneg SUP_ereal_add_pos)
next
  case False
  then show ?thesis by simp
qed

lemma SUP_ereal_cmult:
  fixes f :: "nat \<Rightarrow> ereal"
  assumes "\<And>i. 0 \<le> f i"
    and "0 \<le> c"
  shows "(SUP i. c * f i) = c * SUPREMUM UNIV f"
proof (rule SUP_eqI)
  fix i
  have "f i \<le> SUPREMUM UNIV f"
    by (rule SUP_upper) auto
  then show "c * f i \<le> c * SUPREMUM UNIV f"
    using `0 \<le> c` by (rule ereal_mult_left_mono)
next
  fix y
  assume "\<And>i. i \<in> UNIV \<Longrightarrow> c * f i \<le> y"
  then have *: "\<And>i. c * f i \<le> y" by simp
  show "c * SUPREMUM UNIV f \<le> y"
  proof (cases "0 < c \<and> c \<noteq> \<infinity>")
    case True
    with * have "SUPREMUM UNIV f \<le> y / c"
      by (intro SUP_least) (auto simp: ereal_le_divide_pos)
    with True show ?thesis
      by (auto simp: ereal_le_divide_pos)
  next
    case False
    {
      assume "c = \<infinity>"
      have ?thesis
      proof (cases "\<forall>i. f i = 0")
        case True
        then have "range f = {0}"
          by auto
        with True show "c * SUPREMUM UNIV f \<le> y"
          using * by auto
      next
        case False
        then obtain i where "f i \<noteq> 0"
          by auto
        with *[of i] `c = \<infinity>` `0 \<le> f i` show ?thesis
          by (auto split: split_if_asm)
      qed
    }
    moreover note False
    ultimately show ?thesis
      using * `0 \<le> c` by auto
  qed
qed

lemma SUP_PInfty:
  fixes f :: "'a \<Rightarrow> ereal"
  assumes "\<And>n::nat. \<exists>i\<in>A. ereal (real n) \<le> f i"
  shows "(SUP i:A. f i) = \<infinity>"
  unfolding SUP_def Sup_eq_top_iff[where 'a=ereal, unfolded top_ereal_def]
  apply simp
proof safe
  fix x :: ereal
  assume "x \<noteq> \<infinity>"
  show "\<exists>i\<in>A. x < f i"
  proof (cases x)
    case PInf
    with `x \<noteq> \<infinity>` show ?thesis
      by simp
  next
    case MInf
    with assms[of "0"] show ?thesis
      by force
  next
    case (real r)
    with less_PInf_Ex_of_nat[of x] obtain n :: nat where "x < ereal (real n)"
      by auto
    moreover obtain i where "i \<in> A" "ereal (real n) \<le> f i"
      using assms ..
    ultimately show ?thesis
      by (auto intro!: bexI[of _ i])
  qed
qed

lemma Sup_countable_SUP:
  assumes "A \<noteq> {}"
  shows "\<exists>f::nat \<Rightarrow> ereal. range f \<subseteq> A \<and> Sup A = SUPREMUM UNIV f"
proof (cases "Sup A")
  case (real r)
  have "\<forall>n::nat. \<exists>x. x \<in> A \<and> Sup A < x + 1 / ereal (real n)"
  proof
    fix n :: nat
    have "\<exists>x\<in>A. Sup A - 1 / ereal (real n) < x"
      using assms real by (intro Sup_ereal_close) (auto simp: one_ereal_def)
    then obtain x where "x \<in> A" "Sup A - 1 / ereal (real n) < x" ..
    then show "\<exists>x. x \<in> A \<and> Sup A < x + 1 / ereal (real n)"
      by (auto intro!: exI[of _ x] simp: ereal_minus_less_iff)
  qed
  from choice[OF this] obtain f :: "nat \<Rightarrow> ereal"
    where f: "\<forall>x. f x \<in> A \<and> Sup A < f x + 1 / ereal (real x)" ..
  have "SUPREMUM UNIV f = Sup A"
  proof (rule SUP_eqI)
    fix i
    show "f i \<le> Sup A"
      using f by (auto intro!: complete_lattice_class.Sup_upper)
  next
    fix y
    assume bound: "\<And>i. i \<in> UNIV \<Longrightarrow> f i \<le> y"
    show "Sup A \<le> y"
    proof (rule ereal_le_epsilon, intro allI impI)
      fix e :: ereal
      assume "0 < e"
      show "Sup A \<le> y + e"
      proof (cases e)
        case (real r)
        then have "0 < r"
          using `0 < e` by auto
        then obtain n :: nat where *: "1 / real n < r" "0 < n"
          using ex_inverse_of_nat_less
          by (auto simp: real_eq_of_nat inverse_eq_divide)
        have "Sup A \<le> f n + 1 / ereal (real n)"
          using f[THEN spec, of n]
          by auto
        also have "1 / ereal (real n) \<le> e"
          using real *
          by (auto simp: one_ereal_def )
        with bound have "f n + 1 / ereal (real n) \<le> y + e"
          by (rule add_mono) simp
        finally show "Sup A \<le> y + e" .
      qed (insert `0 < e`, auto)
    qed
  qed
  with f show ?thesis
    by (auto intro!: exI[of _ f])
next
  case PInf
  from `A \<noteq> {}` obtain x where "x \<in> A"
    by auto
  show ?thesis
  proof (cases "\<infinity> \<in> A")
    case True
    then have "\<infinity> \<le> Sup A"
      by (intro complete_lattice_class.Sup_upper)
    with True show ?thesis
      by (auto intro!: exI[of _ "\<lambda>x. \<infinity>"])
  next
    case False
    have "\<exists>x\<in>A. 0 \<le> x"
      by (metis Infty_neq_0(2) PInf complete_lattice_class.Sup_least ereal_infty_less_eq2(1) linorder_linear)
    then obtain x where "x \<in> A" and "0 \<le> x"
      by auto
    have "\<forall>n::nat. \<exists>f. f \<in> A \<and> x + ereal (real n) \<le> f"
    proof (rule ccontr)
      assume "\<not> ?thesis"
      then have "\<exists>n::nat. Sup A \<le> x + ereal (real n)"
        by (simp add: Sup_le_iff not_le less_imp_le Ball_def) (metis less_imp_le)
      then show False using `x \<in> A` `\<infinity> \<notin> A` PInf
        by (cases x) auto
    qed
    from choice[OF this] obtain f :: "nat \<Rightarrow> ereal"
      where f: "\<forall>z. f z \<in> A \<and> x + ereal (real z) \<le> f z" ..
    have "SUPREMUM UNIV f = \<infinity>"
    proof (rule SUP_PInfty)
      fix n :: nat
      show "\<exists>i\<in>UNIV. ereal (real n) \<le> f i"
        using f[THEN spec, of n] `0 \<le> x`
        by (cases rule: ereal2_cases[of "f n" x]) (auto intro!: exI[of _ n])
    qed
    then show ?thesis
      using f PInf by (auto intro!: exI[of _ f])
  qed
next
  case MInf
  with `A \<noteq> {}` have "A = {-\<infinity>}"
    by (auto simp: Sup_eq_MInfty)
  then show ?thesis
    using MInf by (auto intro!: exI[of _ "\<lambda>x. -\<infinity>"])
qed

lemma SUP_countable_SUP:
  "A \<noteq> {} \<Longrightarrow> \<exists>f::nat \<Rightarrow> ereal. range f \<subseteq> g`A \<and> SUPREMUM A g = SUPREMUM UNIV f"
  using Sup_countable_SUP [of "g`A"]
  by auto

lemma Sup_ereal_cadd:
  fixes A :: "ereal set"
  assumes "A \<noteq> {}"
    and "a \<noteq> -\<infinity>"
  shows "Sup ((\<lambda>x. a + x) ` A) = a + Sup A"
proof (rule antisym)
  have *: "\<And>a::ereal. \<And>A. Sup ((\<lambda>x. a + x) ` A) \<le> a + Sup A"
    by (auto intro!: add_mono complete_lattice_class.SUP_least complete_lattice_class.Sup_upper)
  then show "Sup ((\<lambda>x. a + x) ` A) \<le> a + Sup A" .
  show "a + Sup A \<le> Sup ((\<lambda>x. a + x) ` A)"
  proof (cases a)
    case PInf with `A \<noteq> {}`
    show ?thesis
      by (auto simp: image_constant max.absorb1)
  next
    case (real r)
    then have **: "op + (- a) ` op + a ` A = A"
      by (auto simp: image_iff ac_simps zero_ereal_def[symmetric])
    from *[of "-a" "(\<lambda>x. a + x) ` A"] real show ?thesis
      unfolding **
      by (cases rule: ereal2_cases[of "Sup A" "Sup (op + a ` A)"]) auto
  qed (insert `a \<noteq> -\<infinity>`, auto)
qed

lemma Sup_ereal_cminus:
  fixes A :: "ereal set"
  assumes "A \<noteq> {}"
    and "a \<noteq> -\<infinity>"
  shows "Sup ((\<lambda>x. a - x) ` A) = a - Inf A"
  using Sup_ereal_cadd [of "uminus ` A" a] assms
  unfolding image_image minus_ereal_def by (simp add: ereal_SUP_uminus_eq)

lemma SUP_ereal_cminus:
  fixes f :: "'i \<Rightarrow> ereal"
  fixes A
  assumes "A \<noteq> {}"
    and "a \<noteq> -\<infinity>"
  shows "(SUP x:A. a - f x) = a - (INF x:A. f x)"
  using Sup_ereal_cminus[of "f`A" a] assms
  unfolding SUP_def INF_def image_image by auto

lemma Inf_ereal_cminus:
  fixes A :: "ereal set"
  assumes "A \<noteq> {}"
    and "\<bar>a\<bar> \<noteq> \<infinity>"
  shows "Inf ((\<lambda>x. a - x) ` A) = a - Sup A"
proof -
  {
    fix x
    have "-a - -x = -(a - x)"
      using assms by (cases x) auto
  } note * = this
  then have "(\<lambda>x. -a - x)`uminus`A = uminus ` (\<lambda>x. a - x) ` A"
    by (auto simp: image_image)
  with * show ?thesis
    using Sup_ereal_cminus [of "uminus ` A" "- a"] assms
    by (auto simp add: ereal_INF_uminus_eq ereal_SUP_uminus_eq)
qed

lemma INF_ereal_cminus:
  fixes a :: ereal
  assumes "A \<noteq> {}"
    and "\<bar>a\<bar> \<noteq> \<infinity>"
  shows "(INF x:A. a - f x) = a - (SUP x:A. f x)"
  using Inf_ereal_cminus[of "f`A" a] assms
  unfolding SUP_def INF_def image_image
  by auto

lemma uminus_ereal_add_uminus_uminus:
  fixes a b :: ereal
  shows "a \<noteq> \<infinity> \<Longrightarrow> b \<noteq> \<infinity> \<Longrightarrow> - (- a + - b) = a + b"
  by (cases rule: ereal2_cases[of a b]) auto

lemma INF_ereal_add:
  fixes f :: "nat \<Rightarrow> ereal"
  assumes "decseq f" "decseq g"
    and fin: "\<And>i. f i \<noteq> \<infinity>" "\<And>i. g i \<noteq> \<infinity>"
  shows "(INF i. f i + g i) = INFIMUM UNIV f + INFIMUM UNIV g"
proof -
  have INF_less: "(INF i. f i) < \<infinity>" "(INF i. g i) < \<infinity>"
    using assms unfolding INF_less_iff by auto
  {
    fix i
    from fin[of i] have "- ((- f i) + (- g i)) = f i + g i"
      by (rule uminus_ereal_add_uminus_uminus)
  }
  then have "(INF i. f i + g i) = (INF i. - ((- f i) + (- g i)))"
    by simp
  also have "\<dots> = INFIMUM UNIV f + INFIMUM UNIV g"
    unfolding ereal_INF_uminus
    using assms INF_less
    by (subst SUP_ereal_add)
       (auto simp: ereal_SUP_uminus intro!: uminus_ereal_add_uminus_uminus)
  finally show ?thesis .
qed

subsection "Relation to @{typ enat}"

definition "ereal_of_enat n = (case n of enat n \<Rightarrow> ereal (real n) | \<infinity> \<Rightarrow> \<infinity>)"

declare [[coercion "ereal_of_enat :: enat \<Rightarrow> ereal"]]
declare [[coercion "(\<lambda>n. ereal (real n)) :: nat \<Rightarrow> ereal"]]

lemma ereal_of_enat_simps[simp]:
  "ereal_of_enat (enat n) = ereal n"
  "ereal_of_enat \<infinity> = \<infinity>"
  by (simp_all add: ereal_of_enat_def)

lemma ereal_of_enat_le_iff[simp]: "ereal_of_enat m \<le> ereal_of_enat n \<longleftrightarrow> m \<le> n"
  by (cases m n rule: enat2_cases) auto

lemma ereal_of_enat_less_iff[simp]: "ereal_of_enat m < ereal_of_enat n \<longleftrightarrow> m < n"
  by (cases m n rule: enat2_cases) auto

lemma numeral_le_ereal_of_enat_iff[simp]: "numeral m \<le> ereal_of_enat n \<longleftrightarrow> numeral m \<le> n"
  by (cases n) (auto dest: natceiling_le intro: natceiling_le_eq[THEN iffD1])

lemma numeral_less_ereal_of_enat_iff[simp]: "numeral m < ereal_of_enat n \<longleftrightarrow> numeral m < n"
  by (cases n) (auto simp: real_of_nat_less_iff[symmetric])

lemma ereal_of_enat_ge_zero_cancel_iff[simp]: "0 \<le> ereal_of_enat n \<longleftrightarrow> 0 \<le> n"
  by (cases n) (auto simp: enat_0[symmetric])

lemma ereal_of_enat_gt_zero_cancel_iff[simp]: "0 < ereal_of_enat n \<longleftrightarrow> 0 < n"
  by (cases n) (auto simp: enat_0[symmetric])

lemma ereal_of_enat_zero[simp]: "ereal_of_enat 0 = 0"
  by (auto simp: enat_0[symmetric])

lemma ereal_of_enat_inf[simp]: "ereal_of_enat n = \<infinity> \<longleftrightarrow> n = \<infinity>"
  by (cases n) auto

lemma ereal_of_enat_add: "ereal_of_enat (m + n) = ereal_of_enat m + ereal_of_enat n"
  by (cases m n rule: enat2_cases) auto

lemma ereal_of_enat_sub:
  assumes "n \<le> m"
  shows "ereal_of_enat (m - n) = ereal_of_enat m - ereal_of_enat n "
  using assms by (cases m n rule: enat2_cases) auto

lemma ereal_of_enat_mult:
  "ereal_of_enat (m * n) = ereal_of_enat m * ereal_of_enat n"
  by (cases m n rule: enat2_cases) auto

lemmas ereal_of_enat_pushin = ereal_of_enat_add ereal_of_enat_sub ereal_of_enat_mult
lemmas ereal_of_enat_pushout = ereal_of_enat_pushin[symmetric]


subsection "Limits on @{typ ereal}"

subsubsection "Topological space"

instantiation ereal :: linear_continuum_topology
begin

definition "open_ereal" :: "ereal set \<Rightarrow> bool" where
  open_ereal_generated: "open_ereal = generate_topology (range lessThan \<union> range greaterThan)"

instance
  by default (simp add: open_ereal_generated)

end

lemma open_PInfty: "open A \<Longrightarrow> \<infinity> \<in> A \<Longrightarrow> (\<exists>x. {ereal x<..} \<subseteq> A)"
  unfolding open_ereal_generated
proof (induct rule: generate_topology.induct)
  case (Int A B)
  then obtain x z where "\<infinity> \<in> A \<Longrightarrow> {ereal x <..} \<subseteq> A" "\<infinity> \<in> B \<Longrightarrow> {ereal z <..} \<subseteq> B"
    by auto
  with Int show ?case
    by (intro exI[of _ "max x z"]) fastforce
next
  case (Basis S)
  {
    fix x
    have "x \<noteq> \<infinity> \<Longrightarrow> \<exists>t. x \<le> ereal t"
      by (cases x) auto
  }
  moreover note Basis
  ultimately show ?case
    by (auto split: ereal.split)
qed (fastforce simp add: vimage_Union)+

lemma open_MInfty: "open A \<Longrightarrow> -\<infinity> \<in> A \<Longrightarrow> (\<exists>x. {..<ereal x} \<subseteq> A)"
  unfolding open_ereal_generated
proof (induct rule: generate_topology.induct)
  case (Int A B)
  then obtain x z where "-\<infinity> \<in> A \<Longrightarrow> {..< ereal x} \<subseteq> A" "-\<infinity> \<in> B \<Longrightarrow> {..< ereal z} \<subseteq> B"
    by auto
  with Int show ?case
    by (intro exI[of _ "min x z"]) fastforce
next
  case (Basis S)
  {
    fix x
    have "x \<noteq> - \<infinity> \<Longrightarrow> \<exists>t. ereal t \<le> x"
      by (cases x) auto
  }
  moreover note Basis
  ultimately show ?case
    by (auto split: ereal.split)
qed (fastforce simp add: vimage_Union)+

lemma open_ereal_vimage: "open S \<Longrightarrow> open (ereal -` S)"
  unfolding open_ereal_generated
proof (induct rule: generate_topology.induct)
  case (Int A B)
  then show ?case
    by auto
next
  case (Basis S)
  {
    fix x have
      "ereal -` {..<x} = (case x of PInfty \<Rightarrow> UNIV | MInfty \<Rightarrow> {} | ereal r \<Rightarrow> {..<r})"
      "ereal -` {x<..} = (case x of PInfty \<Rightarrow> {} | MInfty \<Rightarrow> UNIV | ereal r \<Rightarrow> {r<..})"
      by (induct x) auto
  }
  moreover note Basis
  ultimately show ?case
    by (auto split: ereal.split)
qed (fastforce simp add: vimage_Union)+

lemma open_ereal: "open S \<Longrightarrow> open (ereal ` S)"
  unfolding open_generated_order[where 'a=real]
proof (induct rule: generate_topology.induct)
  case (Basis S)
  moreover {
    fix x
    have "ereal ` {..< x} = { -\<infinity> <..< ereal x }"
      apply auto
      apply (case_tac xa)
      apply auto
      done
  }
  moreover {
    fix x
    have "ereal ` {x <..} = { ereal x <..< \<infinity> }"
      apply auto
      apply (case_tac xa)
      apply auto
      done
  }
  ultimately show ?case
     by auto
qed (auto simp add: image_Union image_Int)

lemma open_ereal_def:
  "open A \<longleftrightarrow> open (ereal -` A) \<and> (\<infinity> \<in> A \<longrightarrow> (\<exists>x. {ereal x <..} \<subseteq> A)) \<and> (-\<infinity> \<in> A \<longrightarrow> (\<exists>x. {..<ereal x} \<subseteq> A))"
  (is "open A \<longleftrightarrow> ?rhs")
proof
  assume "open A"
  then show ?rhs
    using open_PInfty open_MInfty open_ereal_vimage by auto
next
  assume "?rhs"
  then obtain x y where A: "open (ereal -` A)" "\<infinity> \<in> A \<Longrightarrow> {ereal x<..} \<subseteq> A" "-\<infinity> \<in> A \<Longrightarrow> {..< ereal y} \<subseteq> A"
    by auto
  have *: "A = ereal ` (ereal -` A) \<union> (if \<infinity> \<in> A then {ereal x<..} else {}) \<union> (if -\<infinity> \<in> A then {..< ereal y} else {})"
    using A(2,3) by auto
  from open_ereal[OF A(1)] show "open A"
    by (subst *) (auto simp: open_Un)
qed

lemma open_PInfty2:
  assumes "open A"
    and "\<infinity> \<in> A"
  obtains x where "{ereal x<..} \<subseteq> A"
  using open_PInfty[OF assms] by auto

lemma open_MInfty2:
  assumes "open A"
    and "-\<infinity> \<in> A"
  obtains x where "{..<ereal x} \<subseteq> A"
  using open_MInfty[OF assms] by auto

lemma ereal_openE:
  assumes "open A"
  obtains x y where "open (ereal -` A)"
    and "\<infinity> \<in> A \<Longrightarrow> {ereal x<..} \<subseteq> A"
    and "-\<infinity> \<in> A \<Longrightarrow> {..<ereal y} \<subseteq> A"
  using assms open_ereal_def by auto

lemmas open_ereal_lessThan = open_lessThan[where 'a=ereal]
lemmas open_ereal_greaterThan = open_greaterThan[where 'a=ereal]
lemmas ereal_open_greaterThanLessThan = open_greaterThanLessThan[where 'a=ereal]
lemmas closed_ereal_atLeast = closed_atLeast[where 'a=ereal]
lemmas closed_ereal_atMost = closed_atMost[where 'a=ereal]
lemmas closed_ereal_atLeastAtMost = closed_atLeastAtMost[where 'a=ereal]
lemmas closed_ereal_singleton = closed_singleton[where 'a=ereal]

lemma ereal_open_cont_interval:
  fixes S :: "ereal set"
  assumes "open S"
    and "x \<in> S"
    and "\<bar>x\<bar> \<noteq> \<infinity>"
  obtains e where "e > 0" and "{x-e <..< x+e} \<subseteq> S"
proof -
  from `open S`
  have "open (ereal -` S)"
    by (rule ereal_openE)
  then obtain e where "e > 0" and e: "\<And>y. dist y (real x) < e \<Longrightarrow> ereal y \<in> S"
    using assms unfolding open_dist by force
  show thesis
  proof (intro that subsetI)
    show "0 < ereal e"
      using `0 < e` by auto
    fix y
    assume "y \<in> {x - ereal e<..<x + ereal e}"
    with assms obtain t where "y = ereal t" "dist t (real x) < e"
      by (cases y) (auto simp: dist_real_def)
    then show "y \<in> S"
      using e[of t] by auto
  qed
qed

lemma ereal_open_cont_interval2:
  fixes S :: "ereal set"
  assumes "open S"
    and "x \<in> S"
    and x: "\<bar>x\<bar> \<noteq> \<infinity>"
  obtains a b where "a < x" and "x < b" and "{a <..< b} \<subseteq> S"
proof -
  obtain e where "0 < e" "{x - e<..<x + e} \<subseteq> S"
    using assms by (rule ereal_open_cont_interval)
  with that[of "x - e" "x + e"] ereal_between[OF x, of e]
  show thesis
    by auto
qed


subsubsection {* Convergent sequences *}

lemma lim_ereal[simp]: "((\<lambda>n. ereal (f n)) ---> ereal x) net \<longleftrightarrow> (f ---> x) net"
  (is "?l = ?r")
proof (intro iffI topological_tendstoI)
  fix S
  assume "?l" and "open S" and "x \<in> S"
  then show "eventually (\<lambda>x. f x \<in> S) net"
    using `?l`[THEN topological_tendstoD, OF open_ereal, OF `open S`]
    by (simp add: inj_image_mem_iff)
next
  fix S
  assume "?r" and "open S" and "ereal x \<in> S"
  show "eventually (\<lambda>x. ereal (f x) \<in> S) net"
    using `?r`[THEN topological_tendstoD, OF open_ereal_vimage, OF `open S`]
    using `ereal x \<in> S`
    by auto
qed

lemma lim_real_of_ereal[simp]:
  assumes lim: "(f ---> ereal x) net"
  shows "((\<lambda>x. real (f x)) ---> x) net"
proof (intro topological_tendstoI)
  fix S
  assume "open S" and "x \<in> S"
  then have S: "open S" "ereal x \<in> ereal ` S"
    by (simp_all add: inj_image_mem_iff)
  have "\<forall>x. f x \<in> ereal ` S \<longrightarrow> real (f x) \<in> S"
    by auto
  from this lim[THEN topological_tendstoD, OF open_ereal, OF S]
  show "eventually (\<lambda>x. real (f x) \<in> S) net"
    by (rule eventually_mono)
qed

lemma tendsto_PInfty: "(f ---> \<infinity>) F \<longleftrightarrow> (\<forall>r. eventually (\<lambda>x. ereal r < f x) F)"
proof -
  {
    fix l :: ereal
    assume "\<forall>r. eventually (\<lambda>x. ereal r < f x) F"
    from this[THEN spec, of "real l"] have "l \<noteq> \<infinity> \<Longrightarrow> eventually (\<lambda>x. l < f x) F"
      by (cases l) (auto elim: eventually_elim1)
  }
  then show ?thesis
    by (auto simp: order_tendsto_iff)
qed

lemma tendsto_MInfty: "(f ---> -\<infinity>) F \<longleftrightarrow> (\<forall>r. eventually (\<lambda>x. f x < ereal r) F)"
  unfolding tendsto_def
proof safe
  fix S :: "ereal set"
  assume "open S" "-\<infinity> \<in> S"
  from open_MInfty[OF this] obtain B where "{..<ereal B} \<subseteq> S" ..
  moreover
  assume "\<forall>r::real. eventually (\<lambda>z. f z < r) F"
  then have "eventually (\<lambda>z. f z \<in> {..< B}) F"
    by auto
  ultimately show "eventually (\<lambda>z. f z \<in> S) F"
    by (auto elim!: eventually_elim1)
next
  fix x
  assume "\<forall>S. open S \<longrightarrow> -\<infinity> \<in> S \<longrightarrow> eventually (\<lambda>x. f x \<in> S) F"
  from this[rule_format, of "{..< ereal x}"] show "eventually (\<lambda>y. f y < ereal x) F"
    by auto
qed

lemma Lim_PInfty: "f ----> \<infinity> \<longleftrightarrow> (\<forall>B. \<exists>N. \<forall>n\<ge>N. f n \<ge> ereal B)"
  unfolding tendsto_PInfty eventually_sequentially
proof safe
  fix r
  assume "\<forall>r. \<exists>N. \<forall>n\<ge>N. ereal r \<le> f n"
  then obtain N where "\<forall>n\<ge>N. ereal (r + 1) \<le> f n"
    by blast
  moreover have "ereal r < ereal (r + 1)"
    by auto
  ultimately show "\<exists>N. \<forall>n\<ge>N. ereal r < f n"
    by (blast intro: less_le_trans)
qed (blast intro: less_imp_le)

lemma Lim_MInfty: "f ----> -\<infinity> \<longleftrightarrow> (\<forall>B. \<exists>N. \<forall>n\<ge>N. ereal B \<ge> f n)"
  unfolding tendsto_MInfty eventually_sequentially
proof safe
  fix r
  assume "\<forall>r. \<exists>N. \<forall>n\<ge>N. f n \<le> ereal r"
  then obtain N where "\<forall>n\<ge>N. f n \<le> ereal (r - 1)"
    by blast
  moreover have "ereal (r - 1) < ereal r"
    by auto
  ultimately show "\<exists>N. \<forall>n\<ge>N. f n < ereal r"
    by (blast intro: le_less_trans)
qed (blast intro: less_imp_le)

lemma Lim_bounded_PInfty: "f ----> l \<Longrightarrow> (\<And>n. f n \<le> ereal B) \<Longrightarrow> l \<noteq> \<infinity>"
  using LIMSEQ_le_const2[of f l "ereal B"] by auto

lemma Lim_bounded_MInfty: "f ----> l \<Longrightarrow> (\<And>n. ereal B \<le> f n) \<Longrightarrow> l \<noteq> -\<infinity>"
  using LIMSEQ_le_const[of f l "ereal B"] by auto

lemma tendsto_explicit:
  "f ----> f0 \<longleftrightarrow> (\<forall>S. open S \<longrightarrow> f0 \<in> S \<longrightarrow> (\<exists>N. \<forall>n\<ge>N. f n \<in> S))"
  unfolding tendsto_def eventually_sequentially by auto

lemma Lim_bounded_PInfty2: "f ----> l \<Longrightarrow> \<forall>n\<ge>N. f n \<le> ereal B \<Longrightarrow> l \<noteq> \<infinity>"
  using LIMSEQ_le_const2[of f l "ereal B"] by fastforce

lemma Lim_bounded_ereal: "f ----> (l :: 'a::linorder_topology) \<Longrightarrow> \<forall>n\<ge>M. f n \<le> C \<Longrightarrow> l \<le> C"
  by (intro LIMSEQ_le_const2) auto

lemma Lim_bounded2_ereal:
  assumes lim:"f ----> (l :: 'a::linorder_topology)"
    and ge: "\<forall>n\<ge>N. f n \<ge> C"
  shows "l \<ge> C"
  using ge
  by (intro tendsto_le[OF trivial_limit_sequentially lim tendsto_const])
     (auto simp: eventually_sequentially)

lemma real_of_ereal_mult[simp]:
  fixes a b :: ereal
  shows "real (a * b) = real a * real b"
  by (cases rule: ereal2_cases[of a b]) auto

lemma real_of_ereal_eq_0:
  fixes x :: ereal
  shows "real x = 0 \<longleftrightarrow> x = \<infinity> \<or> x = -\<infinity> \<or> x = 0"
  by (cases x) auto

lemma tendsto_ereal_realD:
  fixes f :: "'a \<Rightarrow> ereal"
  assumes "x \<noteq> 0"
    and tendsto: "((\<lambda>x. ereal (real (f x))) ---> x) net"
  shows "(f ---> x) net"
proof (intro topological_tendstoI)
  fix S
  assume S: "open S" "x \<in> S"
  with `x \<noteq> 0` have "open (S - {0})" "x \<in> S - {0}"
    by auto
  from tendsto[THEN topological_tendstoD, OF this]
  show "eventually (\<lambda>x. f x \<in> S) net"
    by (rule eventually_rev_mp) (auto simp: ereal_real)
qed

lemma tendsto_ereal_realI:
  fixes f :: "'a \<Rightarrow> ereal"
  assumes x: "\<bar>x\<bar> \<noteq> \<infinity>" and tendsto: "(f ---> x) net"
  shows "((\<lambda>x. ereal (real (f x))) ---> x) net"
proof (intro topological_tendstoI)
  fix S
  assume "open S" and "x \<in> S"
  with x have "open (S - {\<infinity>, -\<infinity>})" "x \<in> S - {\<infinity>, -\<infinity>}"
    by auto
  from tendsto[THEN topological_tendstoD, OF this]
  show "eventually (\<lambda>x. ereal (real (f x)) \<in> S) net"
    by (elim eventually_elim1) (auto simp: ereal_real)
qed

lemma ereal_mult_cancel_left:
  fixes a b c :: ereal
  shows "a * b = a * c \<longleftrightarrow> (\<bar>a\<bar> = \<infinity> \<and> 0 < b * c) \<or> a = 0 \<or> b = c"
  by (cases rule: ereal3_cases[of a b c]) (simp_all add: zero_less_mult_iff)

lemma ereal_inj_affinity:
  fixes m t :: ereal
  assumes "\<bar>m\<bar> \<noteq> \<infinity>"
    and "m \<noteq> 0"
    and "\<bar>t\<bar> \<noteq> \<infinity>"
  shows "inj_on (\<lambda>x. m * x + t) A"
  using assms
  by (cases rule: ereal2_cases[of m t])
     (auto intro!: inj_onI simp: ereal_add_cancel_right ereal_mult_cancel_left)

lemma ereal_PInfty_eq_plus[simp]:
  fixes a b :: ereal
  shows "\<infinity> = a + b \<longleftrightarrow> a = \<infinity> \<or> b = \<infinity>"
  by (cases rule: ereal2_cases[of a b]) auto

lemma ereal_MInfty_eq_plus[simp]:
  fixes a b :: ereal
  shows "-\<infinity> = a + b \<longleftrightarrow> (a = -\<infinity> \<and> b \<noteq> \<infinity>) \<or> (b = -\<infinity> \<and> a \<noteq> \<infinity>)"
  by (cases rule: ereal2_cases[of a b]) auto

lemma ereal_less_divide_pos:
  fixes x y :: ereal
  shows "x > 0 \<Longrightarrow> x \<noteq> \<infinity> \<Longrightarrow> y < z / x \<longleftrightarrow> x * y < z"
  by (cases rule: ereal3_cases[of x y z]) (auto simp: field_simps)

lemma ereal_divide_less_pos:
  fixes x y z :: ereal
  shows "x > 0 \<Longrightarrow> x \<noteq> \<infinity> \<Longrightarrow> y / x < z \<longleftrightarrow> y < x * z"
  by (cases rule: ereal3_cases[of x y z]) (auto simp: field_simps)

lemma ereal_divide_eq:
  fixes a b c :: ereal
  shows "b \<noteq> 0 \<Longrightarrow> \<bar>b\<bar> \<noteq> \<infinity> \<Longrightarrow> a / b = c \<longleftrightarrow> a = b * c"
  by (cases rule: ereal3_cases[of a b c])
     (simp_all add: field_simps)

lemma ereal_inverse_not_MInfty[simp]: "inverse (a::ereal) \<noteq> -\<infinity>"
  by (cases a) auto

lemma ereal_mult_m1[simp]: "x * ereal (-1) = -x"
  by (cases x) auto

lemma ereal_real':
  assumes "\<bar>x\<bar> \<noteq> \<infinity>"
  shows "ereal (real x) = x"
  using assms by auto

lemma real_ereal_id: "real \<circ> ereal = id"
proof -
  {
    fix x
    have "(real o ereal) x = id x"
      by auto
  }
  then show ?thesis
    using ext by blast
qed

lemma open_image_ereal: "open(UNIV-{ \<infinity> , (-\<infinity> :: ereal)})"
  by (metis range_ereal open_ereal open_UNIV)

lemma ereal_le_distrib:
  fixes a b c :: ereal
  shows "c * (a + b) \<le> c * a + c * b"
  by (cases rule: ereal3_cases[of a b c])
     (auto simp add: field_simps not_le mult_le_0_iff mult_less_0_iff)

lemma ereal_pos_distrib:
  fixes a b c :: ereal
  assumes "0 \<le> c"
    and "c \<noteq> \<infinity>"
  shows "c * (a + b) = c * a + c * b"
  using assms
  by (cases rule: ereal3_cases[of a b c])
    (auto simp add: field_simps not_le mult_le_0_iff mult_less_0_iff)

lemma ereal_pos_le_distrib:
  fixes a b c :: ereal
  assumes "c \<ge> 0"
  shows "c * (a + b) \<le> c * a + c * b"
  using assms
  by (cases rule: ereal3_cases[of a b c]) (auto simp add: field_simps)

lemma ereal_max_mono: "(a::ereal) \<le> b \<Longrightarrow> c \<le> d \<Longrightarrow> max a c \<le> max b d"
  by (metis sup_ereal_def sup_mono)

lemma ereal_max_least: "(a::ereal) \<le> x \<Longrightarrow> c \<le> x \<Longrightarrow> max a c \<le> x"
  by (metis sup_ereal_def sup_least)

lemma ereal_LimI_finite:
  fixes x :: ereal
  assumes "\<bar>x\<bar> \<noteq> \<infinity>"
    and "\<And>r. 0 < r \<Longrightarrow> \<exists>N. \<forall>n\<ge>N. u n < x + r \<and> x < u n + r"
  shows "u ----> x"
proof (rule topological_tendstoI, unfold eventually_sequentially)
  obtain rx where rx: "x = ereal rx"
    using assms by (cases x) auto
  fix S
  assume "open S" and "x \<in> S"
  then have "open (ereal -` S)"
    unfolding open_ereal_def by auto
  with `x \<in> S` obtain r where "0 < r" and dist: "\<And>y. dist y rx < r \<Longrightarrow> ereal y \<in> S"
    unfolding open_real_def rx by auto
  then obtain n where
    upper: "\<And>N. n \<le> N \<Longrightarrow> u N < x + ereal r" and
    lower: "\<And>N. n \<le> N \<Longrightarrow> x < u N + ereal r"
    using assms(2)[of "ereal r"] by auto
  show "\<exists>N. \<forall>n\<ge>N. u n \<in> S"
  proof (safe intro!: exI[of _ n])
    fix N
    assume "n \<le> N"
    from upper[OF this] lower[OF this] assms `0 < r`
    have "u N \<notin> {\<infinity>,(-\<infinity>)}"
      by auto
    then obtain ra where ra_def: "(u N) = ereal ra"
      by (cases "u N") auto
    then have "rx < ra + r" and "ra < rx + r"
      using rx assms `0 < r` lower[OF `n \<le> N`] upper[OF `n \<le> N`]
      by auto
    then have "dist (real (u N)) rx < r"
      using rx ra_def
      by (auto simp: dist_real_def abs_diff_less_iff field_simps)
    from dist[OF this] show "u N \<in> S"
      using `u N  \<notin> {\<infinity>, -\<infinity>}`
      by (auto simp: ereal_real split: split_if_asm)
  qed
qed

lemma tendsto_obtains_N:
  assumes "f ----> f0"
  assumes "open S"
    and "f0 \<in> S"
  obtains N where "\<forall>n\<ge>N. f n \<in> S"
  using assms using tendsto_def
  using tendsto_explicit[of f f0] assms by auto

lemma ereal_LimI_finite_iff:
  fixes x :: ereal
  assumes "\<bar>x\<bar> \<noteq> \<infinity>"
  shows "u ----> x \<longleftrightarrow> (\<forall>r. 0 < r \<longrightarrow> (\<exists>N. \<forall>n\<ge>N. u n < x + r \<and> x < u n + r))"
  (is "?lhs \<longleftrightarrow> ?rhs")
proof
  assume lim: "u ----> x"
  {
    fix r :: ereal
    assume "r > 0"
    then obtain N where "\<forall>n\<ge>N. u n \<in> {x - r <..< x + r}"
       apply (subst tendsto_obtains_N[of u x "{x - r <..< x + r}"])
       using lim ereal_between[of x r] assms `r > 0`
       apply auto
       done
    then have "\<exists>N. \<forall>n\<ge>N. u n < x + r \<and> x < u n + r"
      using ereal_minus_less[of r x]
      by (cases r) auto
  }
  then show ?rhs
    by auto
next
  assume ?rhs
  then show "u ----> x"
    using ereal_LimI_finite[of x] assms by auto
qed

lemma ereal_Limsup_uminus:
  fixes f :: "'a \<Rightarrow> ereal"
  shows "Limsup net (\<lambda>x. - (f x)) = - Liminf net f"
  unfolding Limsup_def Liminf_def ereal_SUP_uminus ereal_INF_uminus ..

lemma liminf_bounded_iff:
  fixes x :: "nat \<Rightarrow> ereal"
  shows "C \<le> liminf x \<longleftrightarrow> (\<forall>B<C. \<exists>N. \<forall>n\<ge>N. B < x n)"
  (is "?lhs \<longleftrightarrow> ?rhs")
  unfolding le_Liminf_iff eventually_sequentially ..


subsubsection {* Tests for code generator *}

(* A small list of simple arithmetic expressions *)

value [code] "- \<infinity> :: ereal"
value [code] "\<bar>-\<infinity>\<bar> :: ereal"
value [code] "4 + 5 / 4 - ereal 2 :: ereal"
value [code] "ereal 3 < \<infinity>"
value [code] "real (\<infinity>::ereal) = 0"

end
