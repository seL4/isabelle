(*  Title:      HOL/Library/Extended_Reals.thy
    Author:     Johannes Hölzl, TU München
    Author:     Robert Himmelmann, TU München
    Author:     Armin Heller, TU München
    Author:     Bogdan Grechuk, University of Edinburgh
*)

header {* Extended real number line *}

theory Extended_Reals
  imports Complex_Main
begin

text {*

For more lemmas about the extended real numbers go to
  @{text "src/HOL/Multivaraite_Analysis/Extended_Real_Limits.thy"}

*}

lemma (in complete_lattice) atLeast_eq_UNIV_iff: "{x..} = UNIV \<longleftrightarrow> x = bot"
proof
  assume "{x..} = UNIV"
  show "x = bot"
  proof (rule ccontr)
    assume "x \<noteq> bot" then have "bot \<notin> {x..}" by (simp add: le_less)
    then show False using `{x..} = UNIV` by simp
  qed
qed auto

lemma SUPR_pair:
  "(SUP i : A. SUP j : B. f i j) = (SUP p : A \<times> B. f (fst p) (snd p))"
  by (rule antisym) (auto intro!: SUP_leI le_SUPI2)

lemma INFI_pair:
  "(INF i : A. INF j : B. f i j) = (INF p : A \<times> B. f (fst p) (snd p))"
  by (rule antisym) (auto intro!: le_INFI INF_leI2)

subsection {* Definition and basic properties *}

datatype extreal = extreal real | PInfty | MInfty

notation (xsymbols)
  PInfty  ("\<infinity>")

notation (HTML output)
  PInfty  ("\<infinity>")

declare [[coercion "extreal :: real \<Rightarrow> extreal"]]

instantiation extreal :: uminus
begin
  fun uminus_extreal where
    "- (extreal r) = extreal (- r)"
  | "- \<infinity> = MInfty"
  | "- MInfty = \<infinity>"
  instance ..
end

lemma inj_extreal[simp]: "inj_on extreal A"
  unfolding inj_on_def by auto

lemma MInfty_neq_PInfty[simp]:
  "\<infinity> \<noteq> - \<infinity>" "- \<infinity> \<noteq> \<infinity>" by simp_all

lemma MInfty_neq_extreal[simp]:
  "extreal r \<noteq> - \<infinity>" "- \<infinity> \<noteq> extreal r" by simp_all

lemma MInfinity_cases[simp]:
  "(case - \<infinity> of extreal r \<Rightarrow> f r | \<infinity> \<Rightarrow> y | MInfinity \<Rightarrow> z) = z"
  by simp

lemma extreal_uminus_uminus[simp]:
  fixes a :: extreal shows "- (- a) = a"
  by (cases a) simp_all

lemma MInfty_eq[simp]:
  "MInfty = - \<infinity>" by simp

declare uminus_extreal.simps(2)[simp del]

lemma extreal_cases[case_names real PInf MInf, cases type: extreal]:
  assumes "\<And>r. x = extreal r \<Longrightarrow> P"
  assumes "x = \<infinity> \<Longrightarrow> P"
  assumes "x = -\<infinity> \<Longrightarrow> P"
  shows P
  using assms by (cases x) auto

lemmas extreal2_cases = extreal_cases[case_product extreal_cases]
lemmas extreal3_cases = extreal2_cases[case_product extreal_cases]

lemma extreal_uminus_eq_iff[simp]:
  fixes a b :: extreal shows "-a = -b \<longleftrightarrow> a = b"
  by (cases rule: extreal2_cases[of a b]) simp_all

function of_extreal :: "extreal \<Rightarrow> real" where
"of_extreal (extreal r) = r" |
"of_extreal \<infinity> = 0" |
"of_extreal (-\<infinity>) = 0"
  by (auto intro: extreal_cases)
termination proof qed (rule wf_empty)

defs (overloaded)
  real_of_extreal_def [code_unfold]: "real \<equiv> of_extreal"

lemma real_of_extreal[simp]:
    "real (- x :: extreal) = - (real x)"
    "real (extreal r) = r"
    "real \<infinity> = 0"
  by (cases x) (simp_all add: real_of_extreal_def)

lemma range_extreal[simp]: "range extreal = UNIV - {\<infinity>, -\<infinity>}"
proof safe
  fix x assume "x \<notin> range extreal" "x \<noteq> \<infinity>"
  then show "x = -\<infinity>" by (cases x) auto
qed auto

lemma extreal_range_uminus[simp]: "range uminus = (UNIV::extreal set)"
proof safe
  fix x :: extreal show "x \<in> range uminus" by (intro image_eqI[of _ _ "-x"]) auto
qed auto

instantiation extreal :: number
begin
definition [simp]: "number_of x = extreal (number_of x)"
instance proof qed
end

instantiation extreal :: abs
begin
  function abs_extreal where
    "\<bar>extreal r\<bar> = extreal \<bar>r\<bar>"
  | "\<bar>-\<infinity>\<bar> = \<infinity>"
  | "\<bar>\<infinity>\<bar> = \<infinity>"
  by (auto intro: extreal_cases)
  termination proof qed (rule wf_empty)
  instance ..
end

lemma abs_eq_infinity_cases[elim!]: "\<lbrakk> \<bar>x\<bar> = \<infinity> ; x = \<infinity> \<Longrightarrow> P ; x = -\<infinity> \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  by (cases x) auto

lemma abs_neq_infinity_cases[elim!]: "\<lbrakk> \<bar>x\<bar> \<noteq> \<infinity> ; \<And>r. x = extreal r \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  by (cases x) auto

lemma abs_extreal_uminus[simp]: "\<bar>- x\<bar> = \<bar>x::extreal\<bar>"
  by (cases x) auto

subsubsection "Addition"

instantiation extreal :: comm_monoid_add
begin

definition "0 = extreal 0"

function plus_extreal where
"extreal r + extreal p = extreal (r + p)" |
"\<infinity> + a = \<infinity>" |
"a + \<infinity> = \<infinity>" |
"extreal r + -\<infinity> = - \<infinity>" |
"-\<infinity> + extreal p = -\<infinity>" |
"-\<infinity> + -\<infinity> = -\<infinity>"
proof -
  case (goal1 P x)
  moreover then obtain a b where "x = (a, b)" by (cases x) auto
  ultimately show P
   by (cases rule: extreal2_cases[of a b]) auto
qed auto
termination proof qed (rule wf_empty)

lemma Infty_neq_0[simp]:
  "\<infinity> \<noteq> 0" "0 \<noteq> \<infinity>"
  "-\<infinity> \<noteq> 0" "0 \<noteq> -\<infinity>"
  by (simp_all add: zero_extreal_def)

lemma extreal_eq_0[simp]:
  "extreal r = 0 \<longleftrightarrow> r = 0"
  "0 = extreal r \<longleftrightarrow> r = 0"
  unfolding zero_extreal_def by simp_all

instance
proof
  fix a :: extreal show "0 + a = a"
    by (cases a) (simp_all add: zero_extreal_def)
  fix b :: extreal show "a + b = b + a"
    by (cases rule: extreal2_cases[of a b]) simp_all
  fix c :: extreal show "a + b + c = a + (b + c)"
    by (cases rule: extreal3_cases[of a b c]) simp_all
qed
end

lemma abs_extreal_zero[simp]: "\<bar>0\<bar> = (0::extreal)"
  unfolding zero_extreal_def abs_extreal.simps by simp

lemma extreal_uminus_zero[simp]:
  "- 0 = (0::extreal)"
  by (simp add: zero_extreal_def)

lemma extreal_uminus_zero_iff[simp]:
  fixes a :: extreal shows "-a = 0 \<longleftrightarrow> a = 0"
  by (cases a) simp_all

lemma extreal_plus_eq_PInfty[simp]:
  shows "a + b = \<infinity> \<longleftrightarrow> a = \<infinity> \<or> b = \<infinity>"
  by (cases rule: extreal2_cases[of a b]) auto

lemma extreal_plus_eq_MInfty[simp]:
  shows "a + b = -\<infinity> \<longleftrightarrow>
    (a = -\<infinity> \<or> b = -\<infinity>) \<and> a \<noteq> \<infinity> \<and> b \<noteq> \<infinity>"
  by (cases rule: extreal2_cases[of a b]) auto

lemma extreal_add_cancel_left:
  assumes "a \<noteq> -\<infinity>"
  shows "a + b = a + c \<longleftrightarrow> (a = \<infinity> \<or> b = c)"
  using assms by (cases rule: extreal3_cases[of a b c]) auto

lemma extreal_add_cancel_right:
  assumes "a \<noteq> -\<infinity>"
  shows "b + a = c + a \<longleftrightarrow> (a = \<infinity> \<or> b = c)"
  using assms by (cases rule: extreal3_cases[of a b c]) auto

lemma extreal_real:
  "extreal (real x) = (if \<bar>x\<bar> = \<infinity> then 0 else x)"
  by (cases x) simp_all

lemma real_of_extreal_add:
  fixes a b :: extreal
  shows "real (a + b) = (if (\<bar>a\<bar> = \<infinity>) \<and> (\<bar>b\<bar> = \<infinity>) \<or> (\<bar>a\<bar> \<noteq> \<infinity>) \<and> (\<bar>b\<bar> \<noteq> \<infinity>) then real a + real b else 0)"
  by (cases rule: extreal2_cases[of a b]) auto

subsubsection "Linear order on @{typ extreal}"

instantiation extreal :: linorder
begin

function less_extreal where
"extreal x < extreal y \<longleftrightarrow> x < y" |
"        \<infinity> < a         \<longleftrightarrow> False" |
"        a < -\<infinity>        \<longleftrightarrow> False" |
"extreal x < \<infinity>         \<longleftrightarrow> True" |
"       -\<infinity> < extreal r \<longleftrightarrow> True" |
"       -\<infinity> < \<infinity>         \<longleftrightarrow> True"
proof -
  case (goal1 P x)
  moreover then obtain a b where "x = (a,b)" by (cases x) auto
  ultimately show P by (cases rule: extreal2_cases[of a b]) auto
qed simp_all
termination by (relation "{}") simp

definition "x \<le> (y::extreal) \<longleftrightarrow> x < y \<or> x = y"

lemma extreal_infty_less[simp]:
  "x < \<infinity> \<longleftrightarrow> (x \<noteq> \<infinity>)"
  "-\<infinity> < x \<longleftrightarrow> (x \<noteq> -\<infinity>)"
  by (cases x, simp_all) (cases x, simp_all)

lemma extreal_infty_less_eq[simp]:
  "\<infinity> \<le> x \<longleftrightarrow> x = \<infinity>"
  "x \<le> -\<infinity> \<longleftrightarrow> x = -\<infinity>"
  by (auto simp add: less_eq_extreal_def)

lemma extreal_less[simp]:
  "extreal r < 0 \<longleftrightarrow> (r < 0)"
  "0 < extreal r \<longleftrightarrow> (0 < r)"
  "0 < \<infinity>"
  "-\<infinity> < 0"
  by (simp_all add: zero_extreal_def)

lemma extreal_less_eq[simp]:
  "x \<le> \<infinity>"
  "-\<infinity> \<le> x"
  "extreal r \<le> extreal p \<longleftrightarrow> r \<le> p"
  "extreal r \<le> 0 \<longleftrightarrow> r \<le> 0"
  "0 \<le> extreal r \<longleftrightarrow> 0 \<le> r"
  by (auto simp add: less_eq_extreal_def zero_extreal_def)

lemma extreal_infty_less_eq2:
  "a \<le> b \<Longrightarrow> a = \<infinity> \<Longrightarrow> b = \<infinity>"
  "a \<le> b \<Longrightarrow> b = -\<infinity> \<Longrightarrow> a = -\<infinity>"
  by simp_all

instance
proof
  fix x :: extreal show "x \<le> x"
    by (cases x) simp_all
  fix y :: extreal show "x < y \<longleftrightarrow> x \<le> y \<and> \<not> y \<le> x"
    by (cases rule: extreal2_cases[of x y]) auto
  show "x \<le> y \<or> y \<le> x "
    by (cases rule: extreal2_cases[of x y]) auto
  { assume "x \<le> y" "y \<le> x" then show "x = y"
    by (cases rule: extreal2_cases[of x y]) auto }
  { fix z assume "x \<le> y" "y \<le> z" then show "x \<le> z"
    by (cases rule: extreal3_cases[of x y z]) auto }
qed
end

instance extreal :: ordered_ab_semigroup_add
proof
  fix a b c :: extreal assume "a \<le> b" then show "c + a \<le> c + b"
    by (cases rule: extreal3_cases[of a b c]) auto
qed

lemma extreal_MInfty_lessI[intro, simp]:
  "a \<noteq> -\<infinity> \<Longrightarrow> -\<infinity> < a"
  by (cases a) auto

lemma extreal_less_PInfty[intro, simp]:
  "a \<noteq> \<infinity> \<Longrightarrow> a < \<infinity>"
  by (cases a) auto

lemma extreal_less_extreal_Ex:
  fixes a b :: extreal
  shows "x < extreal r \<longleftrightarrow> x = -\<infinity> \<or> (\<exists>p. p < r \<and> x = extreal p)"
  by (cases x) auto

lemma less_PInf_Ex_of_nat: "x \<noteq> \<infinity> \<longleftrightarrow> (\<exists>n::nat. x < extreal (real n))"
proof (cases x)
  case (real r) then show ?thesis
    using reals_Archimedean2[of r] by simp
qed simp_all

lemma extreal_add_mono:
  fixes a b c d :: extreal assumes "a \<le> b" "c \<le> d" shows "a + c \<le> b + d"
  using assms
  apply (cases a)
  apply (cases rule: extreal3_cases[of b c d], auto)
  apply (cases rule: extreal3_cases[of b c d], auto)
  done

lemma extreal_minus_le_minus[simp]:
  fixes a b :: extreal shows "- a \<le> - b \<longleftrightarrow> b \<le> a"
  by (cases rule: extreal2_cases[of a b]) auto

lemma extreal_minus_less_minus[simp]:
  fixes a b :: extreal shows "- a < - b \<longleftrightarrow> b < a"
  by (cases rule: extreal2_cases[of a b]) auto

lemma extreal_le_real_iff:
  "x \<le> real y \<longleftrightarrow> ((\<bar>y\<bar> \<noteq> \<infinity> \<longrightarrow> extreal x \<le> y) \<and> (\<bar>y\<bar> = \<infinity> \<longrightarrow> x \<le> 0))"
  by (cases y) auto

lemma real_le_extreal_iff:
  "real y \<le> x \<longleftrightarrow> ((\<bar>y\<bar> \<noteq> \<infinity> \<longrightarrow> y \<le> extreal x) \<and> (\<bar>y\<bar> = \<infinity> \<longrightarrow> 0 \<le> x))"
  by (cases y) auto

lemma extreal_less_real_iff:
  "x < real y \<longleftrightarrow> ((\<bar>y\<bar> \<noteq> \<infinity> \<longrightarrow> extreal x < y) \<and> (\<bar>y\<bar> = \<infinity> \<longrightarrow> x < 0))"
  by (cases y) auto

lemma real_less_extreal_iff:
  "real y < x \<longleftrightarrow> ((\<bar>y\<bar> \<noteq> \<infinity> \<longrightarrow> y < extreal x) \<and> (\<bar>y\<bar> = \<infinity> \<longrightarrow> 0 < x))"
  by (cases y) auto

lemma real_of_extreal_positive_mono:
  assumes "x \<noteq> \<infinity>" "y \<noteq> \<infinity>" "0 \<le> x" "x \<le> y"
  shows "real x \<le> real y"
  using assms by (cases rule: extreal2_cases[of x y]) auto

lemma real_of_extreal_pos:
  fixes x :: extreal shows "0 \<le> x \<Longrightarrow> 0 \<le> real x" by (cases x) auto

lemmas real_of_extreal_ord_simps =
  extreal_le_real_iff real_le_extreal_iff extreal_less_real_iff real_less_extreal_iff

lemma extreal_dense:
  fixes x y :: extreal assumes "x < y"
  shows "EX z. x < z & z < y"
proof -
{ assume a: "x = (-\<infinity>)"
  { assume "y = \<infinity>" hence ?thesis using a by (auto intro!: exI[of _ "0"]) }
  moreover
  { assume "y ~= \<infinity>"
    with `x < y` obtain r where r: "y = extreal r" by (cases y) auto
    hence ?thesis using `x < y` a by (auto intro!: exI[of _ "extreal (r - 1)"])
  } ultimately have ?thesis by auto
}
moreover
{ assume "x ~= (-\<infinity>)"
  with `x < y` obtain p where p: "x = extreal p" by (cases x) auto
  { assume "y = \<infinity>" hence ?thesis using `x < y` p
       by (auto intro!: exI[of _ "extreal (p + 1)"]) }
  moreover
  { assume "y ~= \<infinity>"
    with `x < y` obtain r where r: "y = extreal r" by (cases y) auto
    with p `x < y` have "p < r" by auto
    with dense obtain z where "p < z" "z < r" by auto
    hence ?thesis using r p by (auto intro!: exI[of _ "extreal z"])
  } ultimately have ?thesis by auto
} ultimately show ?thesis by auto
qed

lemma extreal_dense2:
  fixes x y :: extreal assumes "x < y"
  shows "EX z. x < extreal z & extreal z < y"
  by (metis extreal_dense[OF `x < y`] extreal_cases less_extreal.simps(2,3))

lemma extreal_add_strict_mono:
  fixes a b c d :: extreal
  assumes "a = b" "0 \<le> a" "a \<noteq> \<infinity>" "c < d"
  shows "a + c < b + d"
  using assms by (cases rule: extreal3_cases[case_product extreal_cases, of a b c d]) auto

lemma extreal_less_add: "\<bar>a\<bar> \<noteq> \<infinity> \<Longrightarrow> c < b \<Longrightarrow> a + c < a + b"
  by (cases rule: extreal2_cases[of b c]) auto

lemma extreal_uminus_eq_reorder: "- a = b \<longleftrightarrow> a = (-b::extreal)" by auto

lemma extreal_uminus_less_reorder: "- a < b \<longleftrightarrow> -b < (a::extreal)"
  by (subst (3) extreal_uminus_uminus[symmetric]) (simp only: extreal_minus_less_minus)

lemma extreal_uminus_le_reorder: "- a \<le> b \<longleftrightarrow> -b \<le> (a::extreal)"
  by (subst (3) extreal_uminus_uminus[symmetric]) (simp only: extreal_minus_le_minus)

lemmas extreal_uminus_reorder =
  extreal_uminus_eq_reorder extreal_uminus_less_reorder extreal_uminus_le_reorder

lemma extreal_bot:
  fixes x :: extreal assumes "\<And>B. x \<le> extreal B" shows "x = - \<infinity>"
proof (cases x)
  case (real r) with assms[of "r - 1"] show ?thesis by auto
next case PInf with assms[of 0] show ?thesis by auto
next case MInf then show ?thesis by simp
qed

lemma extreal_top:
  fixes x :: extreal assumes "\<And>B. x \<ge> extreal B" shows "x = \<infinity>"
proof (cases x)
  case (real r) with assms[of "r + 1"] show ?thesis by auto
next case MInf with assms[of 0] show ?thesis by auto
next case PInf then show ?thesis by simp
qed

lemma
  shows extreal_max[simp]: "extreal (max x y) = max (extreal x) (extreal y)"
    and extreal_min[simp]: "extreal (min x y) = min (extreal x) (extreal y)"
  by (simp_all add: min_def max_def)

lemma extreal_max_0: "max 0 (extreal r) = extreal (max 0 r)"
  by (auto simp: zero_extreal_def)

lemma
  fixes f :: "nat \<Rightarrow> extreal"
  shows incseq_uminus[simp]: "incseq (\<lambda>x. - f x) \<longleftrightarrow> decseq f"
  and decseq_uminus[simp]: "decseq (\<lambda>x. - f x) \<longleftrightarrow> incseq f"
  unfolding decseq_def incseq_def by auto

lemma extreal_add_nonneg_nonneg:
  fixes a b :: extreal shows "0 \<le> a \<Longrightarrow> 0 \<le> b \<Longrightarrow> 0 \<le> a + b"
  using add_mono[of 0 a 0 b] by simp

lemma image_eqD: "f ` A = B \<Longrightarrow> (\<forall>x\<in>A. f x \<in> B)"
  by auto

lemma incseq_setsumI:
  fixes f :: "nat \<Rightarrow> 'a::{comm_monoid_add, ordered_ab_semigroup_add}"
  assumes "\<And>i. 0 \<le> f i"
  shows "incseq (\<lambda>i. setsum f {..< i})"
proof (intro incseq_SucI)
  fix n have "setsum f {..< n} + 0 \<le> setsum f {..<n} + f n"
    using assms by (rule add_left_mono)
  then show "setsum f {..< n} \<le> setsum f {..< Suc n}"
    by auto
qed

lemma incseq_setsumI2:
  fixes f :: "'i \<Rightarrow> nat \<Rightarrow> 'a::{comm_monoid_add, ordered_ab_semigroup_add}"
  assumes "\<And>n. n \<in> A \<Longrightarrow> incseq (f n)"
  shows "incseq (\<lambda>i. \<Sum>n\<in>A. f n i)"
  using assms unfolding incseq_def by (auto intro: setsum_mono)

subsubsection "Multiplication"

instantiation extreal :: "{comm_monoid_mult, sgn}"
begin

definition "1 = extreal 1"

function sgn_extreal where
  "sgn (extreal r) = extreal (sgn r)"
| "sgn \<infinity> = 1"
| "sgn (-\<infinity>) = -1"
by (auto intro: extreal_cases)
termination proof qed (rule wf_empty)

function times_extreal where
"extreal r * extreal p = extreal (r * p)" |
"extreal r * \<infinity> = (if r = 0 then 0 else if r > 0 then \<infinity> else -\<infinity>)" |
"\<infinity> * extreal r = (if r = 0 then 0 else if r > 0 then \<infinity> else -\<infinity>)" |
"extreal r * -\<infinity> = (if r = 0 then 0 else if r > 0 then -\<infinity> else \<infinity>)" |
"-\<infinity> * extreal r = (if r = 0 then 0 else if r > 0 then -\<infinity> else \<infinity>)" |
"\<infinity> * \<infinity> = \<infinity>" |
"-\<infinity> * \<infinity> = -\<infinity>" |
"\<infinity> * -\<infinity> = -\<infinity>" |
"-\<infinity> * -\<infinity> = \<infinity>"
proof -
  case (goal1 P x)
  moreover then obtain a b where "x = (a, b)" by (cases x) auto
  ultimately show P by (cases rule: extreal2_cases[of a b]) auto
qed simp_all
termination by (relation "{}") simp

instance
proof
  fix a :: extreal show "1 * a = a"
    by (cases a) (simp_all add: one_extreal_def)
  fix b :: extreal show "a * b = b * a"
    by (cases rule: extreal2_cases[of a b]) simp_all
  fix c :: extreal show "a * b * c = a * (b * c)"
    by (cases rule: extreal3_cases[of a b c])
       (simp_all add: zero_extreal_def zero_less_mult_iff)
qed
end

lemma abs_extreal_one[simp]: "\<bar>1\<bar> = (1::extreal)"
  unfolding one_extreal_def by simp

lemma extreal_mult_zero[simp]:
  fixes a :: extreal shows "a * 0 = 0"
  by (cases a) (simp_all add: zero_extreal_def)

lemma extreal_zero_mult[simp]:
  fixes a :: extreal shows "0 * a = 0"
  by (cases a) (simp_all add: zero_extreal_def)

lemma extreal_m1_less_0[simp]:
  "-(1::extreal) < 0"
  by (simp add: zero_extreal_def one_extreal_def)

lemma extreal_zero_m1[simp]:
  "1 \<noteq> (0::extreal)"
  by (simp add: zero_extreal_def one_extreal_def)

lemma extreal_times_0[simp]:
  fixes x :: extreal shows "0 * x = 0"
  by (cases x) (auto simp: zero_extreal_def)

lemma extreal_times[simp]:
  "1 \<noteq> \<infinity>" "\<infinity> \<noteq> 1"
  "1 \<noteq> -\<infinity>" "-\<infinity> \<noteq> 1"
  by (auto simp add: times_extreal_def one_extreal_def)

lemma extreal_plus_1[simp]:
  "1 + extreal r = extreal (r + 1)" "extreal r + 1 = extreal (r + 1)"
  "1 + -\<infinity> = -\<infinity>" "-\<infinity> + 1 = -\<infinity>"
  unfolding one_extreal_def by auto

lemma extreal_zero_times[simp]:
  fixes a b :: extreal shows "a * b = 0 \<longleftrightarrow> a = 0 \<or> b = 0"
  by (cases rule: extreal2_cases[of a b]) auto

lemma extreal_mult_eq_PInfty[simp]:
  shows "a * b = \<infinity> \<longleftrightarrow>
    (a = \<infinity> \<and> b > 0) \<or> (a > 0 \<and> b = \<infinity>) \<or> (a = -\<infinity> \<and> b < 0) \<or> (a < 0 \<and> b = -\<infinity>)"
  by (cases rule: extreal2_cases[of a b]) auto

lemma extreal_mult_eq_MInfty[simp]:
  shows "a * b = -\<infinity> \<longleftrightarrow>
    (a = \<infinity> \<and> b < 0) \<or> (a < 0 \<and> b = \<infinity>) \<or> (a = -\<infinity> \<and> b > 0) \<or> (a > 0 \<and> b = -\<infinity>)"
  by (cases rule: extreal2_cases[of a b]) auto

lemma extreal_0_less_1[simp]: "0 < (1::extreal)"
  by (simp_all add: zero_extreal_def one_extreal_def)

lemma extreal_zero_one[simp]: "0 \<noteq> (1::extreal)"
  by (simp_all add: zero_extreal_def one_extreal_def)

lemma extreal_mult_minus_left[simp]:
  fixes a b :: extreal shows "-a * b = - (a * b)"
  by (cases rule: extreal2_cases[of a b]) auto

lemma extreal_mult_minus_right[simp]:
  fixes a b :: extreal shows "a * -b = - (a * b)"
  by (cases rule: extreal2_cases[of a b]) auto

lemma extreal_mult_infty[simp]:
  "a * \<infinity> = (if a = 0 then 0 else if 0 < a then \<infinity> else - \<infinity>)"
  by (cases a) auto

lemma extreal_infty_mult[simp]:
  "\<infinity> * a = (if a = 0 then 0 else if 0 < a then \<infinity> else - \<infinity>)"
  by (cases a) auto

lemma extreal_mult_strict_right_mono:
  assumes "a < b" and "0 < c" "c < \<infinity>"
  shows "a * c < b * c"
  using assms
  by (cases rule: extreal3_cases[of a b c])
     (auto simp: zero_le_mult_iff extreal_less_PInfty)

lemma extreal_mult_strict_left_mono:
  "\<lbrakk> a < b ; 0 < c ; c < \<infinity>\<rbrakk> \<Longrightarrow> c * a < c * b"
  using extreal_mult_strict_right_mono by (simp add: mult_commute[of c])

lemma extreal_mult_right_mono:
  fixes a b c :: extreal shows "\<lbrakk>a \<le> b; 0 \<le> c\<rbrakk> \<Longrightarrow> a*c \<le> b*c"
  using assms
  apply (cases "c = 0") apply simp
  by (cases rule: extreal3_cases[of a b c])
     (auto simp: zero_le_mult_iff extreal_less_PInfty)

lemma extreal_mult_left_mono:
  fixes a b c :: extreal shows "\<lbrakk>a \<le> b; 0 \<le> c\<rbrakk> \<Longrightarrow> c * a \<le> c * b"
  using extreal_mult_right_mono by (simp add: mult_commute[of c])

lemma zero_less_one_extreal[simp]: "0 \<le> (1::extreal)"
  by (simp add: one_extreal_def zero_extreal_def)

lemma extreal_0_le_mult[simp]: "0 \<le> a \<Longrightarrow> 0 \<le> b \<Longrightarrow> 0 \<le> a * (b :: extreal)"
  by (cases rule: extreal2_cases[of a b]) (auto simp: mult_nonneg_nonneg)

lemma extreal_right_distrib:
  fixes r a b :: extreal shows "0 \<le> a \<Longrightarrow> 0 \<le> b \<Longrightarrow> r * (a + b) = r * a + r * b"
  by (cases rule: extreal3_cases[of r a b]) (simp_all add: field_simps)

lemma extreal_left_distrib:
  fixes r a b :: extreal shows "0 \<le> a \<Longrightarrow> 0 \<le> b \<Longrightarrow> (a + b) * r = a * r + b * r"
  by (cases rule: extreal3_cases[of r a b]) (simp_all add: field_simps)

lemma extreal_mult_le_0_iff:
  fixes a b :: extreal
  shows "a * b \<le> 0 \<longleftrightarrow> (0 \<le> a \<and> b \<le> 0) \<or> (a \<le> 0 \<and> 0 \<le> b)"
  by (cases rule: extreal2_cases[of a b]) (simp_all add: mult_le_0_iff)

lemma extreal_zero_le_0_iff:
  fixes a b :: extreal
  shows "0 \<le> a * b \<longleftrightarrow> (0 \<le> a \<and> 0 \<le> b) \<or> (a \<le> 0 \<and> b \<le> 0)"
  by (cases rule: extreal2_cases[of a b]) (simp_all add: zero_le_mult_iff)

lemma extreal_mult_less_0_iff:
  fixes a b :: extreal
  shows "a * b < 0 \<longleftrightarrow> (0 < a \<and> b < 0) \<or> (a < 0 \<and> 0 < b)"
  by (cases rule: extreal2_cases[of a b]) (simp_all add: mult_less_0_iff)

lemma extreal_zero_less_0_iff:
  fixes a b :: extreal
  shows "0 < a * b \<longleftrightarrow> (0 < a \<and> 0 < b) \<or> (a < 0 \<and> b < 0)"
  by (cases rule: extreal2_cases[of a b]) (simp_all add: zero_less_mult_iff)

lemma extreal_distrib:
  fixes a b c :: extreal
  assumes "a \<noteq> \<infinity> \<or> b \<noteq> -\<infinity>" "a \<noteq> -\<infinity> \<or> b \<noteq> \<infinity>" "\<bar>c\<bar> \<noteq> \<infinity>"
  shows "(a + b) * c = a * c + b * c"
  using assms
  by (cases rule: extreal3_cases[of a b c]) (simp_all add: field_simps)

lemma extreal_le_epsilon:
  fixes x y :: extreal
  assumes "ALL e. 0 < e --> x <= y + e"
  shows "x <= y"
proof-
{ assume a: "EX r. y = extreal r"
  from this obtain r where r_def: "y = extreal r" by auto
  { assume "x=(-\<infinity>)" hence ?thesis by auto }
  moreover
  { assume "~(x=(-\<infinity>))"
    from this obtain p where p_def: "x = extreal p"
    using a assms[rule_format, of 1] by (cases x) auto
    { fix e have "0 < e --> p <= r + e"
      using assms[rule_format, of "extreal e"] p_def r_def by auto }
    hence "p <= r" apply (subst field_le_epsilon) by auto
    hence ?thesis using r_def p_def by auto
  } ultimately have ?thesis by blast
}
moreover
{ assume "y=(-\<infinity>) | y=\<infinity>" hence ?thesis
    using assms[rule_format, of 1] by (cases x) auto
} ultimately show ?thesis by (cases y) auto
qed


lemma extreal_le_epsilon2:
  fixes x y :: extreal
  assumes "ALL e. 0 < e --> x <= y + extreal e"
  shows "x <= y"
proof-
{ fix e :: extreal assume "e>0"
  { assume "e=\<infinity>" hence "x<=y+e" by auto }
  moreover
  { assume "e~=\<infinity>"
    from this obtain r where "e = extreal r" using `e>0` apply (cases e) by auto
    hence "x<=y+e" using assms[rule_format, of r] `e>0` by auto
  } ultimately have "x<=y+e" by blast
} from this show ?thesis using extreal_le_epsilon by auto
qed

lemma extreal_le_real:
  fixes x y :: extreal
  assumes "ALL z. x <= extreal z --> y <= extreal z"
  shows "y <= x"
by (metis assms extreal.exhaust extreal_bot extreal_less_eq(1)
          extreal_less_eq(2) order_refl uminus_extreal.simps(2))

lemma extreal_le_extreal:
  fixes x y :: extreal
  assumes "\<And>B. B < x \<Longrightarrow> B <= y"
  shows "x <= y"
by (metis assms extreal_dense leD linorder_le_less_linear)

lemma extreal_ge_extreal:
  fixes x y :: extreal
  assumes "ALL B. B>x --> B >= y"
  shows "x >= y"
by (metis assms extreal_dense leD linorder_le_less_linear)

subsubsection {* Power *}

instantiation extreal :: power
begin
primrec power_extreal where
  "power_extreal x 0 = 1" |
  "power_extreal x (Suc n) = x * x ^ n"
instance ..
end

lemma extreal_power[simp]: "(extreal x) ^ n = extreal (x^n)"
  by (induct n) (auto simp: one_extreal_def)

lemma extreal_power_PInf[simp]: "\<infinity> ^ n = (if n = 0 then 1 else \<infinity>)"
  by (induct n) (auto simp: one_extreal_def)

lemma extreal_power_uminus[simp]:
  fixes x :: extreal
  shows "(- x) ^ n = (if even n then x ^ n else - (x^n))"
  by (induct n) (auto simp: one_extreal_def)

lemma extreal_power_number_of[simp]:
  "(number_of num :: extreal) ^ n = extreal (number_of num ^ n)"
  by (induct n) (auto simp: one_extreal_def)

lemma zero_le_power_extreal[simp]:
  fixes a :: extreal assumes "0 \<le> a"
  shows "0 \<le> a ^ n"
  using assms by (induct n) (auto simp: extreal_zero_le_0_iff)

subsubsection {* Subtraction *}

lemma extreal_minus_minus_image[simp]:
  fixes S :: "extreal set"
  shows "uminus ` uminus ` S = S"
  by (auto simp: image_iff)

lemma extreal_uminus_lessThan[simp]:
  fixes a :: extreal shows "uminus ` {..<a} = {-a<..}"
proof (safe intro!: image_eqI)
  fix x assume "-a < x"
  then have "- x < - (- a)" by (simp del: extreal_uminus_uminus)
  then show "- x < a" by simp
qed auto

lemma extreal_uminus_greaterThan[simp]:
  "uminus ` {(a::extreal)<..} = {..<-a}"
  by (metis extreal_uminus_lessThan extreal_uminus_uminus
            extreal_minus_minus_image)

instantiation extreal :: minus
begin
definition "x - y = x + -(y::extreal)"
instance ..
end

lemma extreal_minus[simp]:
  "extreal r - extreal p = extreal (r - p)"
  "-\<infinity> - extreal r = -\<infinity>"
  "extreal r - \<infinity> = -\<infinity>"
  "\<infinity> - x = \<infinity>"
  "-\<infinity> - \<infinity> = -\<infinity>"
  "x - -y = x + y"
  "x - 0 = x"
  "0 - x = -x"
  by (simp_all add: minus_extreal_def)

lemma extreal_x_minus_x[simp]:
  "x - x = (if \<bar>x\<bar> = \<infinity> then \<infinity> else 0)"
  by (cases x) simp_all

lemma extreal_eq_minus_iff:
  fixes x y z :: extreal
  shows "x = z - y \<longleftrightarrow>
    (\<bar>y\<bar> \<noteq> \<infinity> \<longrightarrow> x + y = z) \<and>
    (y = -\<infinity> \<longrightarrow> x = \<infinity>) \<and>
    (y = \<infinity> \<longrightarrow> z = \<infinity> \<longrightarrow> x = \<infinity>) \<and>
    (y = \<infinity> \<longrightarrow> z \<noteq> \<infinity> \<longrightarrow> x = -\<infinity>)"
  by (cases rule: extreal3_cases[of x y z]) auto

lemma extreal_eq_minus:
  fixes x y z :: extreal
  shows "\<bar>y\<bar> \<noteq> \<infinity> \<Longrightarrow> x = z - y \<longleftrightarrow> x + y = z"
  by (auto simp: extreal_eq_minus_iff)

lemma extreal_less_minus_iff:
  fixes x y z :: extreal
  shows "x < z - y \<longleftrightarrow>
    (y = \<infinity> \<longrightarrow> z = \<infinity> \<and> x \<noteq> \<infinity>) \<and>
    (y = -\<infinity> \<longrightarrow> x \<noteq> \<infinity>) \<and>
    (\<bar>y\<bar> \<noteq> \<infinity>\<longrightarrow> x + y < z)"
  by (cases rule: extreal3_cases[of x y z]) auto

lemma extreal_less_minus:
  fixes x y z :: extreal
  shows "\<bar>y\<bar> \<noteq> \<infinity> \<Longrightarrow> x < z - y \<longleftrightarrow> x + y < z"
  by (auto simp: extreal_less_minus_iff)

lemma extreal_le_minus_iff:
  fixes x y z :: extreal
  shows "x \<le> z - y \<longleftrightarrow>
    (y = \<infinity> \<longrightarrow> z \<noteq> \<infinity> \<longrightarrow> x = -\<infinity>) \<and>
    (\<bar>y\<bar> \<noteq> \<infinity> \<longrightarrow> x + y \<le> z)"
  by (cases rule: extreal3_cases[of x y z]) auto

lemma extreal_le_minus:
  fixes x y z :: extreal
  shows "\<bar>y\<bar> \<noteq> \<infinity> \<Longrightarrow> x \<le> z - y \<longleftrightarrow> x + y \<le> z"
  by (auto simp: extreal_le_minus_iff)

lemma extreal_minus_less_iff:
  fixes x y z :: extreal
  shows "x - y < z \<longleftrightarrow>
    y \<noteq> -\<infinity> \<and> (y = \<infinity> \<longrightarrow> x \<noteq> \<infinity> \<and> z \<noteq> -\<infinity>) \<and>
    (y \<noteq> \<infinity> \<longrightarrow> x < z + y)"
  by (cases rule: extreal3_cases[of x y z]) auto

lemma extreal_minus_less:
  fixes x y z :: extreal
  shows "\<bar>y\<bar> \<noteq> \<infinity> \<Longrightarrow> x - y < z \<longleftrightarrow> x < z + y"
  by (auto simp: extreal_minus_less_iff)

lemma extreal_minus_le_iff:
  fixes x y z :: extreal
  shows "x - y \<le> z \<longleftrightarrow>
    (y = -\<infinity> \<longrightarrow> z = \<infinity>) \<and>
    (y = \<infinity> \<longrightarrow> x = \<infinity> \<longrightarrow> z = \<infinity>) \<and>
    (\<bar>y\<bar> \<noteq> \<infinity> \<longrightarrow> x \<le> z + y)"
  by (cases rule: extreal3_cases[of x y z]) auto

lemma extreal_minus_le:
  fixes x y z :: extreal
  shows "\<bar>y\<bar> \<noteq> \<infinity> \<Longrightarrow> x - y \<le> z \<longleftrightarrow> x \<le> z + y"
  by (auto simp: extreal_minus_le_iff)

lemma extreal_minus_eq_minus_iff:
  fixes a b c :: extreal
  shows "a - b = a - c \<longleftrightarrow>
    b = c \<or> a = \<infinity> \<or> (a = -\<infinity> \<and> b \<noteq> -\<infinity> \<and> c \<noteq> -\<infinity>)"
  by (cases rule: extreal3_cases[of a b c]) auto

lemma extreal_add_le_add_iff:
  "c + a \<le> c + b \<longleftrightarrow>
    a \<le> b \<or> c = \<infinity> \<or> (c = -\<infinity> \<and> a \<noteq> \<infinity> \<and> b \<noteq> \<infinity>)"
  by (cases rule: extreal3_cases[of a b c]) (simp_all add: field_simps)

lemma extreal_mult_le_mult_iff:
  "\<bar>c\<bar> \<noteq> \<infinity> \<Longrightarrow> c * a \<le> c * b \<longleftrightarrow> (0 < c \<longrightarrow> a \<le> b) \<and> (c < 0 \<longrightarrow> b \<le> a)"
  by (cases rule: extreal3_cases[of a b c]) (simp_all add: mult_le_cancel_left)

lemma extreal_minus_mono:
  fixes A B C D :: extreal assumes "A \<le> B" "D \<le> C"
  shows "A - C \<le> B - D"
  using assms
  by (cases rule: extreal3_cases[case_product extreal_cases, of A B C D]) simp_all

lemma real_of_extreal_minus:
  "real (a - b) = (if \<bar>a\<bar> = \<infinity> \<or> \<bar>b\<bar> = \<infinity> then 0 else real a - real b)"
  by (cases rule: extreal2_cases[of a b]) auto

lemma extreal_diff_positive:
  fixes a b :: extreal shows "a \<le> b \<Longrightarrow> 0 \<le> b - a"
  by (cases rule: extreal2_cases[of a b]) auto

lemma extreal_between:
  fixes x e :: extreal
  assumes "\<bar>x\<bar> \<noteq> \<infinity>" "0 < e"
  shows "x - e < x" "x < x + e"
using assms apply (cases x, cases e) apply auto
using assms by (cases x, cases e) auto

subsubsection {* Division *}

instantiation extreal :: inverse
begin

function inverse_extreal where
"inverse (extreal r) = (if r = 0 then \<infinity> else extreal (inverse r))" |
"inverse \<infinity> = 0" |
"inverse (-\<infinity>) = 0"
  by (auto intro: extreal_cases)
termination by (relation "{}") simp

definition "x / y = x * inverse (y :: extreal)"

instance proof qed
end

lemma extreal_inverse[simp]:
  "inverse 0 = \<infinity>"
  "inverse (1::extreal) = 1"
  by (simp_all add: one_extreal_def zero_extreal_def)

lemma extreal_divide[simp]:
  "extreal r / extreal p = (if p = 0 then extreal r * \<infinity> else extreal (r / p))"
  unfolding divide_extreal_def by (auto simp: divide_real_def)

lemma extreal_divide_same[simp]:
  "x / x = (if \<bar>x\<bar> = \<infinity> \<or> x = 0 then 0 else 1)"
  by (cases x)
     (simp_all add: divide_real_def divide_extreal_def one_extreal_def)

lemma extreal_inv_inv[simp]:
  "inverse (inverse x) = (if x \<noteq> -\<infinity> then x else \<infinity>)"
  by (cases x) auto

lemma extreal_inverse_minus[simp]:
  "inverse (- x) = (if x = 0 then \<infinity> else -inverse x)"
  by (cases x) simp_all

lemma extreal_uminus_divide[simp]:
  fixes x y :: extreal shows "- x / y = - (x / y)"
  unfolding divide_extreal_def by simp

lemma extreal_divide_Infty[simp]:
  "x / \<infinity> = 0" "x / -\<infinity> = 0"
  unfolding divide_extreal_def by simp_all

lemma extreal_divide_one[simp]:
  "x / 1 = (x::extreal)"
  unfolding divide_extreal_def by simp

lemma extreal_divide_extreal[simp]:
  "\<infinity> / extreal r = (if 0 \<le> r then \<infinity> else -\<infinity>)"
  unfolding divide_extreal_def by simp

lemma zero_le_divide_extreal[simp]:
  fixes a :: extreal assumes "0 \<le> a" "0 \<le> b"
  shows "0 \<le> a / b"
  using assms by (cases rule: extreal2_cases[of a b]) (auto simp: zero_le_divide_iff)

lemma extreal_le_divide_pos:
  "x > 0 \<Longrightarrow> x \<noteq> \<infinity> \<Longrightarrow> y \<le> z / x \<longleftrightarrow> x * y \<le> z"
  by (cases rule: extreal3_cases[of x y z]) (auto simp: field_simps)

lemma extreal_divide_le_pos:
  "x > 0 \<Longrightarrow> x \<noteq> \<infinity> \<Longrightarrow> z / x \<le> y \<longleftrightarrow> z \<le> x * y"
  by (cases rule: extreal3_cases[of x y z]) (auto simp: field_simps)

lemma extreal_le_divide_neg:
  "x < 0 \<Longrightarrow> x \<noteq> -\<infinity> \<Longrightarrow> y \<le> z / x \<longleftrightarrow> z \<le> x * y"
  by (cases rule: extreal3_cases[of x y z]) (auto simp: field_simps)

lemma extreal_divide_le_neg:
  "x < 0 \<Longrightarrow> x \<noteq> -\<infinity> \<Longrightarrow> z / x \<le> y \<longleftrightarrow> x * y \<le> z"
  by (cases rule: extreal3_cases[of x y z]) (auto simp: field_simps)

lemma extreal_inverse_antimono_strict:
  fixes x y :: extreal
  shows "0 \<le> x \<Longrightarrow> x < y \<Longrightarrow> inverse y < inverse x"
  by (cases rule: extreal2_cases[of x y]) auto

lemma extreal_inverse_antimono:
  fixes x y :: extreal
  shows "0 \<le> x \<Longrightarrow> x <= y \<Longrightarrow> inverse y <= inverse x"
  by (cases rule: extreal2_cases[of x y]) auto

lemma inverse_inverse_Pinfty_iff[simp]:
  "inverse x = \<infinity> \<longleftrightarrow> x = 0"
  by (cases x) auto

lemma extreal_inverse_eq_0:
  "inverse x = 0 \<longleftrightarrow> x = \<infinity> \<or> x = -\<infinity>"
  by (cases x) auto

lemma extreal_0_gt_inverse:
  fixes x :: extreal shows "0 < inverse x \<longleftrightarrow> x \<noteq> \<infinity> \<and> 0 \<le> x"
  by (cases x) auto

lemma extreal_mult_less_right:
  assumes "b * a < c * a" "0 < a" "a < \<infinity>"
  shows "b < c"
  using assms
  by (cases rule: extreal3_cases[of a b c])
     (auto split: split_if_asm simp: zero_less_mult_iff zero_le_mult_iff)

lemma extreal_power_divide:
  "y \<noteq> 0 \<Longrightarrow> (x / y :: extreal) ^ n = x^n / y^n"
  by (cases rule: extreal2_cases[of x y])
     (auto simp: one_extreal_def zero_extreal_def power_divide not_le
                 power_less_zero_eq zero_le_power_iff)

lemma extreal_le_mult_one_interval:
  fixes x y :: extreal
  assumes y: "y \<noteq> -\<infinity>"
  assumes z: "\<And>z. \<lbrakk> 0 < z ; z < 1 \<rbrakk> \<Longrightarrow> z * x \<le> y"
  shows "x \<le> y"
proof (cases x)
  case PInf with z[of "1 / 2"] show "x \<le> y" by (simp add: one_extreal_def)
next
  case (real r) note r = this
  show "x \<le> y"
  proof (cases y)
    case (real p) note p = this
    have "r \<le> p"
    proof (rule field_le_mult_one_interval)
      fix z :: real assume "0 < z" and "z < 1"
      with z[of "extreal z"]
      show "z * r \<le> p" using p r by (auto simp: zero_le_mult_iff one_extreal_def)
    qed
    then show "x \<le> y" using p r by simp
  qed (insert y, simp_all)
qed simp

subsection "Complete lattice"

instantiation extreal :: lattice
begin
definition [simp]: "sup x y = (max x y :: extreal)"
definition [simp]: "inf x y = (min x y :: extreal)"
instance proof qed simp_all
end

instantiation extreal :: complete_lattice
begin

definition "bot = -\<infinity>"
definition "top = \<infinity>"

definition "Sup S = (LEAST z. ALL x:S. x <= z :: extreal)"
definition "Inf S = (GREATEST z. ALL x:S. z <= x :: extreal)"

lemma extreal_complete_Sup:
  fixes S :: "extreal set" assumes "S \<noteq> {}"
  shows "\<exists>x. (\<forall>y\<in>S. y \<le> x) \<and> (\<forall>z. (\<forall>y\<in>S. y \<le> z) \<longrightarrow> x \<le> z)"
proof cases
  assume "\<exists>x. \<forall>a\<in>S. a \<le> extreal x"
  then obtain y where y: "\<And>a. a\<in>S \<Longrightarrow> a \<le> extreal y" by auto
  then have "\<infinity> \<notin> S" by force
  show ?thesis
  proof cases
    assume "S = {-\<infinity>}"
    then show ?thesis by (auto intro!: exI[of _ "-\<infinity>"])
  next
    assume "S \<noteq> {-\<infinity>}"
    with `S \<noteq> {}` `\<infinity> \<notin> S` obtain x where "x \<in> S - {-\<infinity>}" "x \<noteq> \<infinity>" by auto
    with y `\<infinity> \<notin> S` have "\<forall>z\<in>real ` (S - {-\<infinity>}). z \<le> y"
      by (auto simp: real_of_extreal_ord_simps)
    with reals_complete2[of "real ` (S - {-\<infinity>})"] `x \<in> S - {-\<infinity>}`
    obtain s where s:
       "\<forall>y\<in>S - {-\<infinity>}. real y \<le> s" "\<And>z. (\<forall>y\<in>S - {-\<infinity>}. real y \<le> z) \<Longrightarrow> s \<le> z"
       by auto
    show ?thesis
    proof (safe intro!: exI[of _ "extreal s"])
      fix z assume "z \<in> S" with `\<infinity> \<notin> S` show "z \<le> extreal s"
      proof (cases z)
        case (real r)
        then show ?thesis
          using s(1)[rule_format, of z] `z \<in> S` `z = extreal r` by auto
      qed auto
    next
      fix z assume *: "\<forall>y\<in>S. y \<le> z"
      with `S \<noteq> {-\<infinity>}` `S \<noteq> {}` show "extreal s \<le> z"
      proof (cases z)
        case (real u)
        with * have "s \<le> u"
          by (intro s(2)[of u]) (auto simp: real_of_extreal_ord_simps)
        then show ?thesis using real by simp
      qed auto
    qed
  qed
next
  assume *: "\<not> (\<exists>x. \<forall>a\<in>S. a \<le> extreal x)"
  show ?thesis
  proof (safe intro!: exI[of _ \<infinity>])
    fix y assume **: "\<forall>z\<in>S. z \<le> y"
    with * show "\<infinity> \<le> y"
    proof (cases y)
      case MInf with * ** show ?thesis by (force simp: not_le)
    qed auto
  qed simp
qed

lemma extreal_complete_Inf:
  fixes S :: "extreal set" assumes "S ~= {}"
  shows "EX x. (ALL y:S. x <= y) & (ALL z. (ALL y:S. z <= y) --> z <= x)"
proof-
def S1 == "uminus ` S"
hence "S1 ~= {}" using assms by auto
from this obtain x where x_def: "(ALL y:S1. y <= x) & (ALL z. (ALL y:S1. y <= z) --> x <= z)"
   using extreal_complete_Sup[of S1] by auto
{ fix z assume "ALL y:S. z <= y"
  hence "ALL y:S1. y <= -z" unfolding S1_def by auto
  hence "x <= -z" using x_def by auto
  hence "z <= -x"
    apply (subst extreal_uminus_uminus[symmetric])
    unfolding extreal_minus_le_minus . }
moreover have "(ALL y:S. -x <= y)"
   using x_def unfolding S1_def
   apply simp
   apply (subst (3) extreal_uminus_uminus[symmetric])
   unfolding extreal_minus_le_minus by simp
ultimately show ?thesis by auto
qed

lemma extreal_complete_uminus_eq:
  fixes S :: "extreal set"
  shows "(\<forall>y\<in>uminus`S. y \<le> x) \<and> (\<forall>z. (\<forall>y\<in>uminus`S. y \<le> z) \<longrightarrow> x \<le> z)
     \<longleftrightarrow> (\<forall>y\<in>S. -x \<le> y) \<and> (\<forall>z. (\<forall>y\<in>S. z \<le> y) \<longrightarrow> z \<le> -x)"
  by simp (metis extreal_minus_le_minus extreal_uminus_uminus)

lemma extreal_Sup_uminus_image_eq:
  fixes S :: "extreal set"
  shows "Sup (uminus ` S) = - Inf S"
proof cases
  assume "S = {}"
  moreover have "(THE x. All (op \<le> x)) = (-\<infinity>::extreal)"
    by (rule the_equality) (auto intro!: extreal_bot)
  moreover have "(SOME x. \<forall>y. y \<le> x) = (\<infinity>::extreal)"
    by (rule some_equality) (auto intro!: extreal_top)
  ultimately show ?thesis unfolding Inf_extreal_def Sup_extreal_def
    Least_def Greatest_def GreatestM_def by simp
next
  assume "S \<noteq> {}"
  with extreal_complete_Sup[of "uminus`S"]
  obtain x where x: "(\<forall>y\<in>S. -x \<le> y) \<and> (\<forall>z. (\<forall>y\<in>S. z \<le> y) \<longrightarrow> z \<le> -x)"
    unfolding extreal_complete_uminus_eq by auto
  show "Sup (uminus ` S) = - Inf S"
    unfolding Inf_extreal_def Greatest_def GreatestM_def
  proof (intro someI2[of _ _ "\<lambda>x. Sup (uminus`S) = - x"])
    show "(\<forall>y\<in>S. -x \<le> y) \<and> (\<forall>y. (\<forall>z\<in>S. y \<le> z) \<longrightarrow> y \<le> -x)"
      using x .
    fix x' assume "(\<forall>y\<in>S. x' \<le> y) \<and> (\<forall>y. (\<forall>z\<in>S. y \<le> z) \<longrightarrow> y \<le> x')"
    then have "(\<forall>y\<in>uminus`S. y \<le> - x') \<and> (\<forall>y. (\<forall>z\<in>uminus`S. z \<le> y) \<longrightarrow> - x' \<le> y)"
      unfolding extreal_complete_uminus_eq by simp
    then show "Sup (uminus ` S) = -x'"
      unfolding Sup_extreal_def extreal_uminus_eq_iff
      by (intro Least_equality) auto
  qed
qed

instance
proof
  { fix x :: extreal and A
    show "bot <= x" by (cases x) (simp_all add: bot_extreal_def)
    show "x <= top" by (simp add: top_extreal_def) }

  { fix x :: extreal and A assume "x : A"
    with extreal_complete_Sup[of A]
    obtain s where s: "\<forall>y\<in>A. y <= s" "\<forall>z. (\<forall>y\<in>A. y <= z) \<longrightarrow> s <= z" by auto
    hence "x <= s" using `x : A` by auto
    also have "... = Sup A" using s unfolding Sup_extreal_def
      by (auto intro!: Least_equality[symmetric])
    finally show "x <= Sup A" . }
  note le_Sup = this

  { fix x :: extreal and A assume *: "!!z. (z : A ==> z <= x)"
    show "Sup A <= x"
    proof (cases "A = {}")
      case True
      hence "Sup A = -\<infinity>" unfolding Sup_extreal_def
        by (auto intro!: Least_equality)
      thus "Sup A <= x" by simp
    next
      case False
      with extreal_complete_Sup[of A]
      obtain s where s: "\<forall>y\<in>A. y <= s" "\<forall>z. (\<forall>y\<in>A. y <= z) \<longrightarrow> s <= z" by auto
      hence "Sup A = s"
        unfolding Sup_extreal_def by (auto intro!: Least_equality)
      also have "s <= x" using * s by auto
      finally show "Sup A <= x" .
    qed }
  note Sup_le = this

  { fix x :: extreal and A assume "x \<in> A"
    with le_Sup[of "-x" "uminus`A"] show "Inf A \<le> x"
      unfolding extreal_Sup_uminus_image_eq by simp }

  { fix x :: extreal and A assume *: "!!z. (z : A ==> x <= z)"
    with Sup_le[of "uminus`A" "-x"] show "x \<le> Inf A"
      unfolding extreal_Sup_uminus_image_eq by force }
qed
end

lemma extreal_SUPR_uminus:
  fixes f :: "'a => extreal"
  shows "(SUP i : R. -(f i)) = -(INF i : R. f i)"
  unfolding SUPR_def INFI_def
  using extreal_Sup_uminus_image_eq[of "f`R"]
  by (simp add: image_image)

lemma extreal_INFI_uminus:
  fixes f :: "'a => extreal"
  shows "(INF i : R. -(f i)) = -(SUP i : R. f i)"
  using extreal_SUPR_uminus[of _ "\<lambda>x. - f x"] by simp

lemma extreal_Inf_uminus_image_eq: "Inf (uminus ` S) = - Sup (S::extreal set)"
  using extreal_Sup_uminus_image_eq[of "uminus ` S"] by (simp add: image_image)

lemma extreal_inj_on_uminus[intro, simp]: "inj_on uminus (A :: extreal set)"
  by (auto intro!: inj_onI)

lemma extreal_image_uminus_shift:
  fixes X Y :: "extreal set" shows "uminus ` X = Y \<longleftrightarrow> X = uminus ` Y"
proof
  assume "uminus ` X = Y"
  then have "uminus ` uminus ` X = uminus ` Y"
    by (simp add: inj_image_eq_iff)
  then show "X = uminus ` Y" by (simp add: image_image)
qed (simp add: image_image)

lemma Inf_extreal_iff:
  fixes z :: extreal
  shows "(!!x. x:X ==> z <= x) ==> (EX x:X. x<y) <-> Inf X < y"
  by (metis complete_lattice_class.Inf_greatest complete_lattice_class.Inf_lower less_le_not_le linear
            order_less_le_trans)

lemma Sup_eq_MInfty:
  fixes S :: "extreal set" shows "Sup S = -\<infinity> \<longleftrightarrow> S = {} \<or> S = {-\<infinity>}"
proof
  assume a: "Sup S = -\<infinity>"
  with complete_lattice_class.Sup_upper[of _ S]
  show "S={} \<or> S={-\<infinity>}" by auto
next
  assume "S={} \<or> S={-\<infinity>}" then show "Sup S = -\<infinity>"
    unfolding Sup_extreal_def by (auto intro!: Least_equality)
qed

lemma Inf_eq_PInfty:
  fixes S :: "extreal set" shows "Inf S = \<infinity> \<longleftrightarrow> S = {} \<or> S = {\<infinity>}"
  using Sup_eq_MInfty[of "uminus`S"]
  unfolding extreal_Sup_uminus_image_eq extreal_image_uminus_shift by simp

lemma Inf_eq_MInfty: "-\<infinity> : S ==> Inf S = -\<infinity>"
  unfolding Inf_extreal_def
  by (auto intro!: Greatest_equality)

lemma Sup_eq_PInfty: "\<infinity> : S ==> Sup S = \<infinity>"
  unfolding Sup_extreal_def
  by (auto intro!: Least_equality)

lemma extreal_SUPI:
  fixes x :: extreal
  assumes "!!i. i : A ==> f i <= x"
  assumes "!!y. (!!i. i : A ==> f i <= y) ==> x <= y"
  shows "(SUP i:A. f i) = x"
  unfolding SUPR_def Sup_extreal_def
  using assms by (auto intro!: Least_equality)

lemma extreal_INFI:
  fixes x :: extreal
  assumes "!!i. i : A ==> f i >= x"
  assumes "!!y. (!!i. i : A ==> f i >= y) ==> x >= y"
  shows "(INF i:A. f i) = x"
  unfolding INFI_def Inf_extreal_def
  using assms by (auto intro!: Greatest_equality)

lemma Sup_extreal_close:
  fixes e :: extreal
  assumes "0 < e" and S: "\<bar>Sup S\<bar> \<noteq> \<infinity>" "S \<noteq> {}"
  shows "\<exists>x\<in>S. Sup S - e < x"
  using assms by (cases e) (auto intro!: less_Sup_iff[THEN iffD1])

lemma Inf_extreal_close:
  fixes e :: extreal assumes "\<bar>Inf X\<bar> \<noteq> \<infinity>" "0 < e"
  shows "\<exists>x\<in>X. x < Inf X + e"
proof (rule Inf_less_iff[THEN iffD1])
  show "Inf X < Inf X + e" using assms
    by (cases e) auto
qed

lemma Sup_eq_top_iff:
  fixes A :: "'a::{complete_lattice, linorder} set"
  shows "Sup A = top \<longleftrightarrow> (\<forall>x<top. \<exists>i\<in>A. x < i)"
proof
  assume *: "Sup A = top"
  show "(\<forall>x<top. \<exists>i\<in>A. x < i)" unfolding *[symmetric]
  proof (intro allI impI)
    fix x assume "x < Sup A" then show "\<exists>i\<in>A. x < i"
      unfolding less_Sup_iff by auto
  qed
next
  assume *: "\<forall>x<top. \<exists>i\<in>A. x < i"
  show "Sup A = top"
  proof (rule ccontr)
    assume "Sup A \<noteq> top"
    with top_greatest[of "Sup A"]
    have "Sup A < top" unfolding le_less by auto
    then have "Sup A < Sup A"
      using * unfolding less_Sup_iff by auto
    then show False by auto
  qed
qed

lemma SUP_eq_top_iff:
  fixes f :: "'a \<Rightarrow> 'b::{complete_lattice, linorder}"
  shows "(SUP i:A. f i) = top \<longleftrightarrow> (\<forall>x<top. \<exists>i\<in>A. x < f i)"
  unfolding SUPR_def Sup_eq_top_iff by auto

lemma SUP_nat_Infty: "(SUP i::nat. extreal (real i)) = \<infinity>"
proof -
  { fix x assume "x \<noteq> \<infinity>"
    then have "\<exists>k::nat. x < extreal (real k)"
    proof (cases x)
      case MInf then show ?thesis by (intro exI[of _ 0]) auto
    next
      case (real r)
      moreover obtain k :: nat where "r < real k"
        using ex_less_of_nat by (auto simp: real_eq_of_nat)
      ultimately show ?thesis by auto
    qed simp }
  then show ?thesis
    using SUP_eq_top_iff[of UNIV "\<lambda>n::nat. extreal (real n)"]
    by (auto simp: top_extreal_def)
qed

lemma extreal_le_Sup:
  fixes x :: extreal
  shows "(x <= (SUP i:A. f i)) <-> (ALL y. y < x --> (EX i. i : A & y <= f i))"
(is "?lhs <-> ?rhs")
proof-
{ assume "?rhs"
  { assume "~(x <= (SUP i:A. f i))" hence "(SUP i:A. f i)<x" by (simp add: not_le)
    from this obtain y where y_def: "(SUP i:A. f i)<y & y<x" using extreal_dense by auto
    from this obtain i where "i : A & y <= f i" using `?rhs` by auto
    hence "y <= (SUP i:A. f i)" using le_SUPI[of i A f] by auto
    hence False using y_def by auto
  } hence "?lhs" by auto
}
moreover
{ assume "?lhs" hence "?rhs"
  by (metis Collect_def Collect_mem_eq SUP_leI assms atLeastatMost_empty atLeastatMost_empty_iff
      inf_sup_ord(4) linorder_le_cases sup_absorb1 xt1(8))
} ultimately show ?thesis by auto
qed

lemma extreal_Inf_le:
  fixes x :: extreal
  shows "((INF i:A. f i) <= x) <-> (ALL y. x < y --> (EX i. i : A & f i <= y))"
(is "?lhs <-> ?rhs")
proof-
{ assume "?rhs"
  { assume "~((INF i:A. f i) <= x)" hence "x < (INF i:A. f i)" by (simp add: not_le)
    from this obtain y where y_def: "x<y & y<(INF i:A. f i)" using extreal_dense by auto
    from this obtain i where "i : A & f i <= y" using `?rhs` by auto
    hence "(INF i:A. f i) <= y" using INF_leI[of i A f] by auto
    hence False using y_def by auto
  } hence "?lhs" by auto
}
moreover
{ assume "?lhs" hence "?rhs"
  by (metis Collect_def Collect_mem_eq le_INFI assms atLeastatMost_empty atLeastatMost_empty_iff
      inf_sup_ord(4) linorder_le_cases sup_absorb1 xt1(8))
} ultimately show ?thesis by auto
qed

lemma Inf_less:
  fixes x :: extreal
  assumes "(INF i:A. f i) < x"
  shows "EX i. i : A & f i <= x"
proof(rule ccontr)
  assume "~ (EX i. i : A & f i <= x)"
  hence "ALL i:A. f i > x" by auto
  hence "(INF i:A. f i) >= x" apply (subst le_INFI) by auto
  thus False using assms by auto
qed

lemma same_INF:
  assumes "ALL e:A. f e = g e"
  shows "(INF e:A. f e) = (INF e:A. g e)"
proof-
have "f ` A = g ` A" unfolding image_def using assms by auto
thus ?thesis unfolding INFI_def by auto
qed

lemma same_SUP:
  assumes "ALL e:A. f e = g e"
  shows "(SUP e:A. f e) = (SUP e:A. g e)"
proof-
have "f ` A = g ` A" unfolding image_def using assms by auto
thus ?thesis unfolding SUPR_def by auto
qed

lemma SUPR_eq:
  assumes "\<forall>i\<in>A. \<exists>j\<in>B. f i \<le> g j"
  assumes "\<forall>j\<in>B. \<exists>i\<in>A. g j \<le> f i"
  shows "(SUP i:A. f i) = (SUP j:B. g j)"
proof (intro antisym)
  show "(SUP i:A. f i) \<le> (SUP j:B. g j)"
    using assms by (metis SUP_leI le_SUPI2)
  show "(SUP i:B. g i) \<le> (SUP j:A. f j)"
    using assms by (metis SUP_leI le_SUPI2)
qed

lemma SUP_extreal_le_addI:
  assumes "\<And>i. f i + y \<le> z" and "y \<noteq> -\<infinity>"
  shows "SUPR UNIV f + y \<le> z"
proof (cases y)
  case (real r)
  then have "\<And>i. f i \<le> z - y" using assms by (simp add: extreal_le_minus_iff)
  then have "SUPR UNIV f \<le> z - y" by (rule SUP_leI)
  then show ?thesis using real by (simp add: extreal_le_minus_iff)
qed (insert assms, auto)

lemma SUPR_extreal_add:
  fixes f g :: "nat \<Rightarrow> extreal"
  assumes "incseq f" "incseq g" and pos: "\<And>i. f i \<noteq> -\<infinity>" "\<And>i. g i \<noteq> -\<infinity>"
  shows "(SUP i. f i + g i) = SUPR UNIV f + SUPR UNIV g"
proof (rule extreal_SUPI)
  fix y assume *: "\<And>i. i \<in> UNIV \<Longrightarrow> f i + g i \<le> y"
  have f: "SUPR UNIV f \<noteq> -\<infinity>" using pos
    unfolding SUPR_def Sup_eq_MInfty by (auto dest: image_eqD)
  { fix j
    { fix i
      have "f i + g j \<le> f i + g (max i j)"
        using `incseq g`[THEN incseqD] by (rule add_left_mono) auto
      also have "\<dots> \<le> f (max i j) + g (max i j)"
        using `incseq f`[THEN incseqD] by (rule add_right_mono) auto
      also have "\<dots> \<le> y" using * by auto
      finally have "f i + g j \<le> y" . }
    then have "SUPR UNIV f + g j \<le> y"
      using assms(4)[of j] by (intro SUP_extreal_le_addI) auto
    then have "g j + SUPR UNIV f \<le> y" by (simp add: ac_simps) }
  then have "SUPR UNIV g + SUPR UNIV f \<le> y"
    using f by (rule SUP_extreal_le_addI)
  then show "SUPR UNIV f + SUPR UNIV g \<le> y" by (simp add: ac_simps)
qed (auto intro!: add_mono le_SUPI)

lemma SUPR_extreal_add_pos:
  fixes f g :: "nat \<Rightarrow> extreal"
  assumes inc: "incseq f" "incseq g" and pos: "\<And>i. 0 \<le> f i" "\<And>i. 0 \<le> g i"
  shows "(SUP i. f i + g i) = SUPR UNIV f + SUPR UNIV g"
proof (intro SUPR_extreal_add inc)
  fix i show "f i \<noteq> -\<infinity>" "g i \<noteq> -\<infinity>" using pos[of i] by auto
qed

lemma SUPR_extreal_setsum:
  fixes f g :: "'a \<Rightarrow> nat \<Rightarrow> extreal"
  assumes "\<And>n. n \<in> A \<Longrightarrow> incseq (f n)" and pos: "\<And>n i. n \<in> A \<Longrightarrow> 0 \<le> f n i"
  shows "(SUP i. \<Sum>n\<in>A. f n i) = (\<Sum>n\<in>A. SUPR UNIV (f n))"
proof cases
  assume "finite A" then show ?thesis using assms
    by induct (auto simp: incseq_setsumI2 setsum_nonneg SUPR_extreal_add_pos)
qed simp

lemma SUPR_extreal_cmult:
  fixes f :: "nat \<Rightarrow> extreal" assumes "\<And>i. 0 \<le> f i" "0 \<le> c"
  shows "(SUP i. c * f i) = c * SUPR UNIV f"
proof (rule extreal_SUPI)
  fix i have "f i \<le> SUPR UNIV f" by (rule le_SUPI) auto
  then show "c * f i \<le> c * SUPR UNIV f"
    using `0 \<le> c` by (rule extreal_mult_left_mono)
next
  fix y assume *: "\<And>i. i \<in> UNIV \<Longrightarrow> c * f i \<le> y"
  show "c * SUPR UNIV f \<le> y"
  proof cases
    assume c: "0 < c \<and> c \<noteq> \<infinity>"
    with * have "SUPR UNIV f \<le> y / c"
      by (intro SUP_leI) (auto simp: extreal_le_divide_pos)
    with c show ?thesis
      by (auto simp: extreal_le_divide_pos)
  next
    { assume "c = \<infinity>" have ?thesis
      proof cases
        assume "\<forall>i. f i = 0"
        moreover then have "range f = {0}" by auto
        ultimately show "c * SUPR UNIV f \<le> y" using * by (auto simp: SUPR_def)
      next
        assume "\<not> (\<forall>i. f i = 0)"
        then obtain i where "f i \<noteq> 0" by auto
        with *[of i] `c = \<infinity>` `0 \<le> f i` show ?thesis by (auto split: split_if_asm)
      qed }
    moreover assume "\<not> (0 < c \<and> c \<noteq> \<infinity>)"
    ultimately show ?thesis using * `0 \<le> c` by auto
  qed
qed

lemma SUP_PInfty:
  fixes f :: "'a \<Rightarrow> extreal"
  assumes "\<And>n::nat. \<exists>i\<in>A. extreal (real n) \<le> f i"
  shows "(SUP i:A. f i) = \<infinity>"
  unfolding SUPR_def Sup_eq_top_iff[where 'a=extreal, unfolded top_extreal_def]
  apply simp
proof safe
  fix x assume "x \<noteq> \<infinity>"
  show "\<exists>i\<in>A. x < f i"
  proof (cases x)
    case PInf with `x \<noteq> \<infinity>` show ?thesis by simp
  next
    case MInf with assms[of "0"] show ?thesis by force
  next
    case (real r)
    with less_PInf_Ex_of_nat[of x] obtain n :: nat where "x < extreal (real n)" by auto
    moreover from assms[of n] guess i ..
    ultimately show ?thesis
      by (auto intro!: bexI[of _ i])
  qed
qed

lemma Sup_countable_SUPR:
  assumes "A \<noteq> {}"
  shows "\<exists>f::nat \<Rightarrow> extreal. range f \<subseteq> A \<and> Sup A = SUPR UNIV f"
proof (cases "Sup A")
  case (real r)
  have "\<forall>n::nat. \<exists>x. x \<in> A \<and> Sup A < x + 1 / extreal (real n)"
  proof
    fix n ::nat have "\<exists>x\<in>A. Sup A - 1 / extreal (real n) < x"
      using assms real by (intro Sup_extreal_close) (auto simp: one_extreal_def)
    then guess x ..
    then show "\<exists>x. x \<in> A \<and> Sup A < x + 1 / extreal (real n)"
      by (auto intro!: exI[of _ x] simp: extreal_minus_less_iff)
  qed
  from choice[OF this] guess f .. note f = this
  have "SUPR UNIV f = Sup A"
  proof (rule extreal_SUPI)
    fix i show "f i \<le> Sup A" using f
      by (auto intro!: complete_lattice_class.Sup_upper)
  next
    fix y assume bound: "\<And>i. i \<in> UNIV \<Longrightarrow> f i \<le> y"
    show "Sup A \<le> y"
    proof (rule extreal_le_epsilon, intro allI impI)
      fix e :: extreal assume "0 < e"
      show "Sup A \<le> y + e"
      proof (cases e)
        case (real r)
        hence "0 < r" using `0 < e` by auto
        then obtain n ::nat where *: "1 / real n < r" "0 < n"
          using ex_inverse_of_nat_less by (auto simp: real_eq_of_nat inverse_eq_divide)
        have "Sup A \<le> f n + 1 / extreal (real n)" using f[THEN spec, of n] by auto
        also have "1 / extreal (real n) \<le> e" using real * by (auto simp: one_extreal_def )
        with bound have "f n + 1 / extreal (real n) \<le> y + e" by (rule add_mono) simp
        finally show "Sup A \<le> y + e" .
      qed (insert `0 < e`, auto)
    qed
  qed
  with f show ?thesis by (auto intro!: exI[of _ f])
next
  case PInf
  from `A \<noteq> {}` obtain x where "x \<in> A" by auto
  show ?thesis
  proof cases
    assume "\<infinity> \<in> A"
    moreover then have "\<infinity> \<le> Sup A" by (intro complete_lattice_class.Sup_upper)
    ultimately show ?thesis by (auto intro!: exI[of _ "\<lambda>x. \<infinity>"])
  next
    assume "\<infinity> \<notin> A"
    have "\<exists>x\<in>A. 0 \<le> x"
      by (metis Infty_neq_0 PInf complete_lattice_class.Sup_least extreal_infty_less_eq2 linorder_linear)
    then obtain x where "x \<in> A" "0 \<le> x" by auto
    have "\<forall>n::nat. \<exists>f. f \<in> A \<and> x + extreal (real n) \<le> f"
    proof (rule ccontr)
      assume "\<not> ?thesis"
      then have "\<exists>n::nat. Sup A \<le> x + extreal (real n)"
        by (simp add: Sup_le_iff not_le less_imp_le Ball_def) (metis less_imp_le)
      then show False using `x \<in> A` `\<infinity> \<notin> A` PInf
        by(cases x) auto
    qed
    from choice[OF this] guess f .. note f = this
    have "SUPR UNIV f = \<infinity>"
    proof (rule SUP_PInfty)
      fix n :: nat show "\<exists>i\<in>UNIV. extreal (real n) \<le> f i"
        using f[THEN spec, of n] `0 \<le> x`
        by (cases rule: extreal2_cases[of "f n" x]) (auto intro!: exI[of _ n])
    qed
    then show ?thesis using f PInf by (auto intro!: exI[of _ f])
  qed
next
  case MInf
  with `A \<noteq> {}` have "A = {-\<infinity>}" by (auto simp: Sup_eq_MInfty)
  then show ?thesis using MInf by (auto intro!: exI[of _ "\<lambda>x. -\<infinity>"])
qed

lemma SUPR_countable_SUPR:
  "A \<noteq> {} \<Longrightarrow> \<exists>f::nat \<Rightarrow> extreal. range f \<subseteq> g`A \<and> SUPR A g = SUPR UNIV f"
  using Sup_countable_SUPR[of "g`A"] by (auto simp: SUPR_def)


lemma Sup_extreal_cadd:
  fixes A :: "extreal set" assumes "A \<noteq> {}" and "a \<noteq> -\<infinity>"
  shows "Sup ((\<lambda>x. a + x) ` A) = a + Sup A"
proof (rule antisym)
  have *: "\<And>a::extreal. \<And>A. Sup ((\<lambda>x. a + x) ` A) \<le> a + Sup A"
    by (auto intro!: add_mono complete_lattice_class.Sup_least complete_lattice_class.Sup_upper)
  then show "Sup ((\<lambda>x. a + x) ` A) \<le> a + Sup A" .
  show "a + Sup A \<le> Sup ((\<lambda>x. a + x) ` A)"
  proof (cases a)
    case PInf with `A \<noteq> {}` show ?thesis by (auto simp: image_constant)
  next
    case (real r)
    then have **: "op + (- a) ` op + a ` A = A"
      by (auto simp: image_iff ac_simps zero_extreal_def[symmetric])
    from *[of "-a" "(\<lambda>x. a + x) ` A"] real show ?thesis unfolding **
      by (cases rule: extreal2_cases[of "Sup A" "Sup (op + a ` A)"]) auto
  qed (insert `a \<noteq> -\<infinity>`, auto)
qed

lemma Sup_extreal_cminus:
  fixes A :: "extreal set" assumes "A \<noteq> {}" and "a \<noteq> -\<infinity>"
  shows "Sup ((\<lambda>x. a - x) ` A) = a - Inf A"
  using Sup_extreal_cadd[of "uminus ` A" a] assms
  by (simp add: comp_def image_image minus_extreal_def
                 extreal_Sup_uminus_image_eq)

lemma SUPR_extreal_cminus:
  fixes A assumes "A \<noteq> {}" and "a \<noteq> -\<infinity>"
  shows "(SUP x:A. a - f x) = a - (INF x:A. f x)"
  using Sup_extreal_cminus[of "f`A" a] assms
  unfolding SUPR_def INFI_def image_image by auto

lemma Inf_extreal_cminus:
  fixes A :: "extreal set" assumes "A \<noteq> {}" and "\<bar>a\<bar> \<noteq> \<infinity>"
  shows "Inf ((\<lambda>x. a - x) ` A) = a - Sup A"
proof -
  { fix x have "-a - -x = -(a - x)" using assms by (cases x) auto }
  moreover then have "(\<lambda>x. -a - x)`uminus`A = uminus ` (\<lambda>x. a - x) ` A"
    by (auto simp: image_image)
  ultimately show ?thesis
    using Sup_extreal_cminus[of "uminus ` A" "-a"] assms
    by (auto simp add: extreal_Sup_uminus_image_eq extreal_Inf_uminus_image_eq)
qed

lemma INFI_extreal_cminus:
  fixes A assumes "A \<noteq> {}" and "\<bar>a\<bar> \<noteq> \<infinity>"
  shows "(INF x:A. a - f x) = a - (SUP x:A. f x)"
  using Inf_extreal_cminus[of "f`A" a] assms
  unfolding SUPR_def INFI_def image_image
  by auto

subsection "Limits on @{typ extreal}"

subsubsection "Topological space"

instantiation extreal :: topological_space
begin

definition "open A \<longleftrightarrow> open (extreal -` A)
       \<and> (\<infinity> \<in> A \<longrightarrow> (\<exists>x. {extreal x <..} \<subseteq> A))
       \<and> (-\<infinity> \<in> A \<longrightarrow> (\<exists>x. {..<extreal x} \<subseteq> A))"

lemma open_PInfty: "open A \<Longrightarrow> \<infinity> \<in> A \<Longrightarrow> (\<exists>x. {extreal x<..} \<subseteq> A)"
  unfolding open_extreal_def by auto

lemma open_MInfty: "open A \<Longrightarrow> -\<infinity> \<in> A \<Longrightarrow> (\<exists>x. {..<extreal x} \<subseteq> A)"
  unfolding open_extreal_def by auto

lemma open_PInfty2: assumes "open A" "\<infinity> \<in> A" obtains x where "{extreal x<..} \<subseteq> A"
  using open_PInfty[OF assms] by auto

lemma open_MInfty2: assumes "open A" "-\<infinity> \<in> A" obtains x where "{..<extreal x} \<subseteq> A"
  using open_MInfty[OF assms] by auto

lemma extreal_openE: assumes "open A" obtains x y where
  "open (extreal -` A)"
  "\<infinity> \<in> A \<Longrightarrow> {extreal x<..} \<subseteq> A"
  "-\<infinity> \<in> A \<Longrightarrow> {..<extreal y} \<subseteq> A"
  using assms open_extreal_def by auto

instance
proof
  let ?U = "UNIV::extreal set"
  show "open ?U" unfolding open_extreal_def
    by (auto intro!: exI[of _ 0])
next
  fix S T::"extreal set" assume "open S" and "open T"
  from `open S`[THEN extreal_openE] guess xS yS .
  moreover from `open T`[THEN extreal_openE] guess xT yT .
  ultimately have
    "open (extreal -` (S \<inter> T))"
    "\<infinity> \<in> S \<inter> T \<Longrightarrow> {extreal (max xS xT) <..} \<subseteq> S \<inter> T"
    "-\<infinity> \<in> S \<inter> T \<Longrightarrow> {..< extreal (min yS yT)} \<subseteq> S \<inter> T"
    by auto
  then show "open (S Int T)" unfolding open_extreal_def by blast
next
  fix K :: "extreal set set" assume "\<forall>S\<in>K. open S"
  then have *: "\<forall>S. \<exists>x y. S \<in> K \<longrightarrow> open (extreal -` S) \<and>
    (\<infinity> \<in> S \<longrightarrow> {extreal x <..} \<subseteq> S) \<and> (-\<infinity> \<in> S \<longrightarrow> {..< extreal y} \<subseteq> S)"
    by (auto simp: open_extreal_def)
  then show "open (Union K)" unfolding open_extreal_def
  proof (intro conjI impI)
    show "open (extreal -` \<Union>K)"
      using *[THEN choice] by (auto simp: vimage_Union)
  qed ((metis UnionE Union_upper subset_trans *)+)
qed
end

lemma open_extreal: "open S \<Longrightarrow> open (extreal ` S)"
  by (auto simp: inj_vimage_image_eq open_extreal_def)

lemma open_extreal_vimage: "open S \<Longrightarrow> open (extreal -` S)"
  unfolding open_extreal_def by auto

lemma open_extreal_lessThan[intro, simp]: "open {..< a :: extreal}"
proof -
  have "\<And>x. extreal -` {..<extreal x} = {..< x}"
    "extreal -` {..< \<infinity>} = UNIV" "extreal -` {..< -\<infinity>} = {}" by auto
  then show ?thesis by (cases a) (auto simp: open_extreal_def)
qed

lemma open_extreal_greaterThan[intro, simp]:
  "open {a :: extreal <..}"
proof -
  have "\<And>x. extreal -` {extreal x<..} = {x<..}"
    "extreal -` {\<infinity><..} = {}" "extreal -` {-\<infinity><..} = UNIV" by auto
  then show ?thesis by (cases a) (auto simp: open_extreal_def)
qed

lemma extreal_open_greaterThanLessThan[intro, simp]: "open {a::extreal <..< b}"
  unfolding greaterThanLessThan_def by auto

lemma closed_extreal_atLeast[simp, intro]: "closed {a :: extreal ..}"
proof -
  have "- {a ..} = {..< a}" by auto
  then show "closed {a ..}"
    unfolding closed_def using open_extreal_lessThan by auto
qed

lemma closed_extreal_atMost[simp, intro]: "closed {.. b :: extreal}"
proof -
  have "- {.. b} = {b <..}" by auto
  then show "closed {.. b}"
    unfolding closed_def using open_extreal_greaterThan by auto
qed

lemma closed_extreal_atLeastAtMost[simp, intro]:
  shows "closed {a :: extreal .. b}"
  unfolding atLeastAtMost_def by auto

lemma closed_extreal_singleton:
  "closed {a :: extreal}"
by (metis atLeastAtMost_singleton closed_extreal_atLeastAtMost)

lemma extreal_open_cont_interval:
  assumes "open S" "x \<in> S" "\<bar>x\<bar> \<noteq> \<infinity>"
  obtains e where "e>0" "{x-e <..< x+e} \<subseteq> S"
proof-
  from `open S` have "open (extreal -` S)" by (rule extreal_openE)
  then obtain e where "0 < e" and e: "\<And>y. dist y (real x) < e \<Longrightarrow> extreal y \<in> S"
    using assms unfolding open_dist by force
  show thesis
  proof (intro that subsetI)
    show "0 < extreal e" using `0 < e` by auto
    fix y assume "y \<in> {x - extreal e<..<x + extreal e}"
    with assms obtain t where "y = extreal t" "dist t (real x) < e"
      apply (cases y) by (auto simp: dist_real_def)
    then show "y \<in> S" using e[of t] by auto
  qed
qed

lemma extreal_open_cont_interval2:
  assumes "open S" "x \<in> S" and x: "\<bar>x\<bar> \<noteq> \<infinity>"
  obtains a b where "a < x" "x < b" "{a <..< b} \<subseteq> S"
proof-
  guess e using extreal_open_cont_interval[OF assms] .
  with that[of "x-e" "x+e"] extreal_between[OF x, of e]
  show thesis by auto
qed

instance extreal :: t2_space
proof
  fix x y :: extreal assume "x ~= y"
  let "?P x (y::extreal)" = "EX U V. open U & open V & x : U & y : V & U Int V = {}"

  { fix x y :: extreal assume "x < y"
    from extreal_dense[OF this] obtain z where z: "x < z" "z < y" by auto
    have "?P x y"
      apply (rule exI[of _ "{..<z}"])
      apply (rule exI[of _ "{z<..}"])
      using z by auto }
  note * = this

  from `x ~= y`
  show "EX U V. open U & open V & x : U & y : V & U Int V = {}"
  proof (cases rule: linorder_cases)
    assume "x = y" with `x ~= y` show ?thesis by simp
  next assume "x < y" from *[OF this] show ?thesis by auto
  next assume "y < x" from *[OF this] show ?thesis by auto
  qed
qed

subsubsection {* Convergent sequences *}

lemma lim_extreal[simp]:
  "((\<lambda>n. extreal (f n)) ---> extreal x) net \<longleftrightarrow> (f ---> x) net" (is "?l = ?r")
proof (intro iffI topological_tendstoI)
  fix S assume "?l" "open S" "x \<in> S"
  then show "eventually (\<lambda>x. f x \<in> S) net"
    using `?l`[THEN topological_tendstoD, OF open_extreal, OF `open S`]
    by (simp add: inj_image_mem_iff)
next
  fix S assume "?r" "open S" "extreal x \<in> S"
  show "eventually (\<lambda>x. extreal (f x) \<in> S) net"
    using `?r`[THEN topological_tendstoD, OF open_extreal_vimage, OF `open S`]
    using `extreal x \<in> S` by auto
qed

lemma lim_real_of_extreal[simp]:
  assumes lim: "(f ---> extreal x) net"
  shows "((\<lambda>x. real (f x)) ---> x) net"
proof (intro topological_tendstoI)
  fix S assume "open S" "x \<in> S"
  then have S: "open S" "extreal x \<in> extreal ` S"
    by (simp_all add: inj_image_mem_iff)
  have "\<forall>x. f x \<in> extreal ` S \<longrightarrow> real (f x) \<in> S" by auto
  from this lim[THEN topological_tendstoD, OF open_extreal, OF S]
  show "eventually (\<lambda>x. real (f x) \<in> S) net"
    by (rule eventually_mono)
qed

lemma Lim_PInfty: "f ----> \<infinity> <-> (ALL B. EX N. ALL n>=N. f n >= extreal B)" (is "?l = ?r")
proof assume ?r show ?l apply(rule topological_tendstoI)
    unfolding eventually_sequentially
  proof- fix S assume "open S" "\<infinity> : S"
    from open_PInfty[OF this] guess B .. note B=this
    from `?r`[rule_format,of "B+1"] guess N .. note N=this
    show "EX N. ALL n>=N. f n : S" apply(rule_tac x=N in exI)
    proof safe case goal1
      have "extreal B < extreal (B + 1)" by auto
      also have "... <= f n" using goal1 N by auto
      finally show ?case using B by fastsimp
    qed
  qed
next assume ?l show ?r
  proof fix B::real have "open {extreal B<..}" "\<infinity> : {extreal B<..}" by auto
    from topological_tendstoD[OF `?l` this,unfolded eventually_sequentially]
    guess N .. note N=this
    show "EX N. ALL n>=N. extreal B <= f n" apply(rule_tac x=N in exI) using N by auto
  qed
qed


lemma Lim_MInfty: "f ----> (-\<infinity>) <-> (ALL B. EX N. ALL n>=N. f n <= extreal B)" (is "?l = ?r")
proof assume ?r show ?l apply(rule topological_tendstoI)
    unfolding eventually_sequentially
  proof- fix S assume "open S" "(-\<infinity>) : S"
    from open_MInfty[OF this] guess B .. note B=this
    from `?r`[rule_format,of "B-(1::real)"] guess N .. note N=this
    show "EX N. ALL n>=N. f n : S" apply(rule_tac x=N in exI)
    proof safe case goal1
      have "extreal (B - 1) >= f n" using goal1 N by auto
      also have "... < extreal B" by auto
      finally show ?case using B by fastsimp
    qed
  qed
next assume ?l show ?r
  proof fix B::real have "open {..<extreal B}" "(-\<infinity>) : {..<extreal B}" by auto
    from topological_tendstoD[OF `?l` this,unfolded eventually_sequentially]
    guess N .. note N=this
    show "EX N. ALL n>=N. extreal B >= f n" apply(rule_tac x=N in exI) using N by auto
  qed
qed


lemma Lim_bounded_PInfty: assumes lim:"f ----> l" and "!!n. f n <= extreal B" shows "l ~= \<infinity>"
proof(rule ccontr,unfold not_not) let ?B = "B + 1" assume as:"l=\<infinity>"
  from lim[unfolded this Lim_PInfty,rule_format,of "?B"]
  guess N .. note N=this[rule_format,OF le_refl]
  hence "extreal ?B <= extreal B" using assms(2)[of N] by(rule order_trans)
  hence "extreal ?B < extreal ?B" apply (rule le_less_trans) by auto
  thus False by auto
qed


lemma Lim_bounded_MInfty: assumes lim:"f ----> l" and "!!n. f n >= extreal B" shows "l ~= (-\<infinity>)"
proof(rule ccontr,unfold not_not) let ?B = "B - 1" assume as:"l=(-\<infinity>)"
  from lim[unfolded this Lim_MInfty,rule_format,of "?B"]
  guess N .. note N=this[rule_format,OF le_refl]
  hence "extreal B <= extreal ?B" using assms(2)[of N] order_trans[of "extreal B" "f N" "extreal(B - 1)"] by blast
  thus False by auto
qed


lemma tendsto_explicit:
  "f ----> f0 <-> (ALL S. open S --> f0 : S --> (EX N. ALL n>=N. f n : S))"
  unfolding tendsto_def eventually_sequentially by auto


lemma tendsto_obtains_N:
  assumes "f ----> f0"
  assumes "open S" "f0 : S"
  obtains N where "ALL n>=N. f n : S"
  using tendsto_explicit[of f f0] assms by auto


lemma tail_same_limit:
  fixes X Y N
  assumes "X ----> L" "ALL n>=N. X n = Y n"
  shows "Y ----> L"
proof-
{ fix S assume "open S" and "L:S"
  from this obtain N1 where "ALL n>=N1. X n : S"
     using assms unfolding tendsto_def eventually_sequentially by auto
  hence "ALL n>=max N N1. Y n : S" using assms by auto
  hence "EX N. ALL n>=N. Y n : S" apply(rule_tac x="max N N1" in exI) by auto
}
thus ?thesis using tendsto_explicit by auto
qed


lemma Lim_bounded_PInfty2:
assumes lim:"f ----> l" and "ALL n>=N. f n <= extreal B"
shows "l ~= \<infinity>"
proof-
  def g == "(%n. if n>=N then f n else extreal B)"
  hence "g ----> l" using tail_same_limit[of f l N g] lim by auto
  moreover have "!!n. g n <= extreal B" using g_def assms by auto
  ultimately show ?thesis using  Lim_bounded_PInfty by auto
qed

lemma Lim_bounded_extreal:
  assumes lim:"f ----> (l :: extreal)"
  and "ALL n>=M. f n <= C"
  shows "l<=C"
proof-
{ assume "l=(-\<infinity>)" hence ?thesis by auto }
moreover
{ assume "~(l=(-\<infinity>))"
  { assume "C=\<infinity>" hence ?thesis by auto }
  moreover
  { assume "C=(-\<infinity>)" hence "ALL n>=M. f n = (-\<infinity>)" using assms by auto
    hence "l=(-\<infinity>)" using assms
       tendsto_unique[OF trivial_limit_sequentially] tail_same_limit[of "\<lambda>n. -\<infinity>" "-\<infinity>" M f, OF tendsto_const] by auto
    hence ?thesis by auto }
  moreover
  { assume "EX B. C = extreal B"
    from this obtain B where B_def: "C=extreal B" by auto
    hence "~(l=\<infinity>)" using Lim_bounded_PInfty2 assms by auto
    from this obtain m where m_def: "extreal m=l" using `~(l=(-\<infinity>))` by (cases l) auto
    from this obtain N where N_def: "ALL n>=N. f n : {extreal(m - 1) <..< extreal(m+1)}"
       apply (subst tendsto_obtains_N[of f l "{extreal(m - 1) <..< extreal(m+1)}"]) using assms by auto
    { fix n assume "n>=N"
      hence "EX r. extreal r = f n" using N_def by (cases "f n") auto
    } from this obtain g where g_def: "ALL n>=N. extreal (g n) = f n" by metis
    hence "(%n. extreal (g n)) ----> l" using tail_same_limit[of f l N] assms by auto
    hence *: "(%n. g n) ----> m" using m_def by auto
    { fix n assume "n>=max N M"
      hence "extreal (g n) <= extreal B" using assms g_def B_def by auto
      hence "g n <= B" by auto
    } hence "EX N. ALL n>=N. g n <= B" by blast
    hence "m<=B" using * LIMSEQ_le_const2[of g m B] by auto
    hence ?thesis using m_def B_def by auto
  } ultimately have ?thesis by (cases C) auto
} ultimately show ?thesis by blast
qed

lemma real_of_extreal_0[simp]: "real (0::extreal) = 0"
  unfolding real_of_extreal_def zero_extreal_def by simp

lemma real_of_extreal_mult[simp]:
  fixes a b :: extreal shows "real (a * b) = real a * real b"
  by (cases rule: extreal2_cases[of a b]) auto

lemma real_of_extreal_eq_0:
  "real x = 0 \<longleftrightarrow> x = \<infinity> \<or> x = -\<infinity> \<or> x = 0"
  by (cases x) auto

lemma tendsto_extreal_realD:
  fixes f :: "'a \<Rightarrow> extreal"
  assumes "x \<noteq> 0" and tendsto: "((\<lambda>x. extreal (real (f x))) ---> x) net"
  shows "(f ---> x) net"
proof (intro topological_tendstoI)
  fix S assume S: "open S" "x \<in> S"
  with `x \<noteq> 0` have "open (S - {0})" "x \<in> S - {0}" by auto
  from tendsto[THEN topological_tendstoD, OF this]
  show "eventually (\<lambda>x. f x \<in> S) net"
    by (rule eventually_rev_mp) (auto simp: extreal_real real_of_extreal_0)
qed

lemma tendsto_extreal_realI:
  fixes f :: "'a \<Rightarrow> extreal"
  assumes x: "\<bar>x\<bar> \<noteq> \<infinity>" and tendsto: "(f ---> x) net"
  shows "((\<lambda>x. extreal (real (f x))) ---> x) net"
proof (intro topological_tendstoI)
  fix S assume "open S" "x \<in> S"
  with x have "open (S - {\<infinity>, -\<infinity>})" "x \<in> S - {\<infinity>, -\<infinity>}" by auto
  from tendsto[THEN topological_tendstoD, OF this]
  show "eventually (\<lambda>x. extreal (real (f x)) \<in> S) net"
    by (elim eventually_elim1) (auto simp: extreal_real)
qed

lemma extreal_mult_cancel_left:
  fixes a b c :: extreal shows "a * b = a * c \<longleftrightarrow>
    ((\<bar>a\<bar> = \<infinity> \<and> 0 < b * c) \<or> a = 0 \<or> b = c)"
  by (cases rule: extreal3_cases[of a b c])
     (simp_all add: zero_less_mult_iff)

lemma extreal_inj_affinity:
  assumes "\<bar>m\<bar> \<noteq> \<infinity>" "m \<noteq> 0" "\<bar>t\<bar> \<noteq> \<infinity>"
  shows "inj_on (\<lambda>x. m * x + t) A"
  using assms
  by (cases rule: extreal2_cases[of m t])
     (auto intro!: inj_onI simp: extreal_add_cancel_right extreal_mult_cancel_left)

lemma extreal_PInfty_eq_plus[simp]:
  shows "\<infinity> = a + b \<longleftrightarrow> a = \<infinity> \<or> b = \<infinity>"
  by (cases rule: extreal2_cases[of a b]) auto

lemma extreal_MInfty_eq_plus[simp]:
  shows "-\<infinity> = a + b \<longleftrightarrow> (a = -\<infinity> \<and> b \<noteq> \<infinity>) \<or> (b = -\<infinity> \<and> a \<noteq> \<infinity>)"
  by (cases rule: extreal2_cases[of a b]) auto

lemma extreal_less_divide_pos:
  "x > 0 \<Longrightarrow> x \<noteq> \<infinity> \<Longrightarrow> y < z / x \<longleftrightarrow> x * y < z"
  by (cases rule: extreal3_cases[of x y z]) (auto simp: field_simps)

lemma extreal_divide_less_pos:
  "x > 0 \<Longrightarrow> x \<noteq> \<infinity> \<Longrightarrow> y / x < z \<longleftrightarrow> y < x * z"
  by (cases rule: extreal3_cases[of x y z]) (auto simp: field_simps)

lemma extreal_divide_eq:
  "b \<noteq> 0 \<Longrightarrow> \<bar>b\<bar> \<noteq> \<infinity> \<Longrightarrow> a / b = c \<longleftrightarrow> a = b * c"
  by (cases rule: extreal3_cases[of a b c])
     (simp_all add: field_simps)

lemma extreal_inverse_not_MInfty[simp]: "inverse a \<noteq> -\<infinity>"
  by (cases a) auto

lemma extreal_mult_m1[simp]: "x * extreal (-1) = -x"
  by (cases x) auto

lemma extreal_LimI_finite:
  assumes "\<bar>x\<bar> \<noteq> \<infinity>"
  assumes "!!r. 0 < r ==> EX N. ALL n>=N. u n < x + r & x < u n + r"
  shows "u ----> x"
proof (rule topological_tendstoI, unfold eventually_sequentially)
  obtain rx where rx_def: "x=extreal rx" using assms by (cases x) auto
  fix S assume "open S" "x : S"
  then have "open (extreal -` S)" unfolding open_extreal_def by auto
  with `x \<in> S` obtain r where "0 < r" and dist: "!!y. dist y rx < r ==> extreal y \<in> S"
    unfolding open_real_def rx_def by auto
  then obtain n where
    upper: "!!N. n <= N ==> u N < x + extreal r" and
    lower: "!!N. n <= N ==> x < u N + extreal r" using assms(2)[of "extreal r"] by auto
  show "EX N. ALL n>=N. u n : S"
  proof (safe intro!: exI[of _ n])
    fix N assume "n <= N"
    from upper[OF this] lower[OF this] assms `0 < r`
    have "u N ~: {\<infinity>,(-\<infinity>)}" by auto
    from this obtain ra where ra_def: "(u N) = extreal ra" by (cases "u N") auto
    hence "rx < ra + r" and "ra < rx + r"
       using rx_def assms `0 < r` lower[OF `n <= N`] upper[OF `n <= N`] by auto
    hence "dist (real (u N)) rx < r"
      using rx_def ra_def
      by (auto simp: dist_real_def abs_diff_less_iff field_simps)
    from dist[OF this] show "u N : S" using `u N  ~: {\<infinity>, -\<infinity>}`
      by (auto simp: extreal_real split: split_if_asm)
  qed
qed

lemma extreal_LimI_finite_iff:
  assumes "\<bar>x\<bar> \<noteq> \<infinity>"
  shows "u ----> x <-> (ALL r. 0 < r --> (EX N. ALL n>=N. u n < x + r & x < u n + r))"
  (is "?lhs <-> ?rhs")
proof
  assume lim: "u ----> x"
  { fix r assume "(r::extreal)>0"
    from this obtain N where N_def: "ALL n>=N. u n : {x - r <..< x + r}"
       apply (subst tendsto_obtains_N[of u x "{x - r <..< x + r}"])
       using lim extreal_between[of x r] assms `r>0` by auto
    hence "EX N. ALL n>=N. u n < x + r & x < u n + r"
      using extreal_minus_less[of r x] by (cases r) auto
  } then show "?rhs" by auto
next
  assume ?rhs then show "u ----> x"
    using extreal_LimI_finite[of x] assms by auto
qed


subsubsection {* @{text Liminf} and @{text Limsup} *}

definition
  "Liminf net f = (GREATEST l. \<forall>y<l. eventually (\<lambda>x. y < f x) net)"

definition
  "Limsup net f = (LEAST l. \<forall>y>l. eventually (\<lambda>x. f x < y) net)"

lemma Liminf_Sup:
  fixes f :: "'a => 'b::{complete_lattice, linorder}"
  shows "Liminf net f = Sup {l. \<forall>y<l. eventually (\<lambda>x. y < f x) net}"
  by (auto intro!: Greatest_equality complete_lattice_class.Sup_upper simp: less_Sup_iff Liminf_def)

lemma Limsup_Inf:
  fixes f :: "'a => 'b::{complete_lattice, linorder}"
  shows "Limsup net f = Inf {l. \<forall>y>l. eventually (\<lambda>x. f x < y) net}"
  by (auto intro!: Least_equality complete_lattice_class.Inf_lower simp: Inf_less_iff Limsup_def)

lemma extreal_SupI:
  fixes x :: extreal
  assumes "\<And>y. y \<in> A \<Longrightarrow> y \<le> x"
  assumes "\<And>y. (\<And>z. z \<in> A \<Longrightarrow> z \<le> y) \<Longrightarrow> x \<le> y"
  shows "Sup A = x"
  unfolding Sup_extreal_def
  using assms by (auto intro!: Least_equality)

lemma extreal_InfI:
  fixes x :: extreal
  assumes "\<And>i. i \<in> A \<Longrightarrow> x \<le> i"
  assumes "\<And>y. (\<And>i. i \<in> A \<Longrightarrow> y \<le> i) \<Longrightarrow> y \<le> x"
  shows "Inf A = x"
  unfolding Inf_extreal_def
  using assms by (auto intro!: Greatest_equality)

lemma Limsup_const:
  fixes c :: "'a::{complete_lattice, linorder}"
  assumes ntriv: "\<not> trivial_limit net"
  shows "Limsup net (\<lambda>x. c) = c"
  unfolding Limsup_Inf
proof (safe intro!: antisym complete_lattice_class.Inf_greatest complete_lattice_class.Inf_lower)
  fix x assume *: "\<forall>y>x. eventually (\<lambda>_. c < y) net"
  show "c \<le> x"
  proof (rule ccontr)
    assume "\<not> c \<le> x" then have "x < c" by auto
    then show False using ntriv * by (auto simp: trivial_limit_def)
  qed
qed auto

lemma Liminf_const:
  fixes c :: "'a::{complete_lattice, linorder}"
  assumes ntriv: "\<not> trivial_limit net"
  shows "Liminf net (\<lambda>x. c) = c"
  unfolding Liminf_Sup
proof (safe intro!: antisym complete_lattice_class.Sup_least complete_lattice_class.Sup_upper)
  fix x assume *: "\<forall>y<x. eventually (\<lambda>_. y < c) net"
  show "x \<le> c"
  proof (rule ccontr)
    assume "\<not> x \<le> c" then have "c < x" by auto
    then show False using ntriv * by (auto simp: trivial_limit_def)
  qed
qed auto

lemma mono_set:
  fixes S :: "('a::order) set"
  shows "mono S \<longleftrightarrow> (\<forall>x y. x \<le> y \<longrightarrow> x \<in> S \<longrightarrow> y \<in> S)"
  by (auto simp: mono_def mem_def)

lemma mono_greaterThan[intro, simp]: "mono {B<..}" unfolding mono_set by auto
lemma mono_atLeast[intro, simp]: "mono {B..}" unfolding mono_set by auto
lemma mono_UNIV[intro, simp]: "mono UNIV" unfolding mono_set by auto
lemma mono_empty[intro, simp]: "mono {}" unfolding mono_set by auto

lemma mono_set_iff:
  fixes S :: "'a::{linorder,complete_lattice} set"
  defines "a \<equiv> Inf S"
  shows "mono S \<longleftrightarrow> (S = {a <..} \<or> S = {a..})" (is "_ = ?c")
proof
  assume "mono S"
  then have mono: "\<And>x y. x \<le> y \<Longrightarrow> x \<in> S \<Longrightarrow> y \<in> S" by (auto simp: mono_set)
  show ?c
  proof cases
    assume "a \<in> S"
    show ?c
      using mono[OF _ `a \<in> S`]
      by (auto intro: complete_lattice_class.Inf_lower simp: a_def)
  next
    assume "a \<notin> S"
    have "S = {a <..}"
    proof safe
      fix x assume "x \<in> S"
      then have "a \<le> x" unfolding a_def by (rule complete_lattice_class.Inf_lower)
      then show "a < x" using `x \<in> S` `a \<notin> S` by (cases "a = x") auto
    next
      fix x assume "a < x"
      then obtain y where "y < x" "y \<in> S" unfolding a_def Inf_less_iff ..
      with mono[of y x] show "x \<in> S" by auto
    qed
    then show ?c ..
  qed
qed auto

lemma lim_imp_Liminf:
  fixes f :: "'a \<Rightarrow> extreal"
  assumes ntriv: "\<not> trivial_limit net"
  assumes lim: "(f ---> f0) net"
  shows "Liminf net f = f0"
  unfolding Liminf_Sup
proof (safe intro!: extreal_SupI)
  fix y assume *: "\<forall>y'<y. eventually (\<lambda>x. y' < f x) net"
  show "y \<le> f0"
  proof (rule extreal_le_extreal)
    fix B assume "B < y"
    { assume "f0 < B"
      then have "eventually (\<lambda>x. f x < B \<and> B < f x) net"
         using topological_tendstoD[OF lim, of "{..<B}"] *[rule_format, OF `B < y`]
         by (auto intro: eventually_conj)
      also have "(\<lambda>x. f x < B \<and> B < f x) = (\<lambda>x. False)" by (auto simp: fun_eq_iff)
      finally have False using ntriv[unfolded trivial_limit_def] by auto
    } then show "B \<le> f0" by (metis linorder_le_less_linear)
  qed
next
  fix y assume *: "\<forall>z. z \<in> {l. \<forall>y<l. eventually (\<lambda>x. y < f x) net} \<longrightarrow> z \<le> y"
  show "f0 \<le> y"
  proof (safe intro!: *[rule_format])
    fix y assume "y < f0" then show "eventually (\<lambda>x. y < f x) net"
      using lim[THEN topological_tendstoD, of "{y <..}"] by auto
  qed
qed

lemma extreal_Liminf_le_Limsup:
  fixes f :: "'a \<Rightarrow> extreal"
  assumes ntriv: "\<not> trivial_limit net"
  shows "Liminf net f \<le> Limsup net f"
  unfolding Limsup_Inf Liminf_Sup
proof (safe intro!: complete_lattice_class.Inf_greatest  complete_lattice_class.Sup_least)
  fix u v assume *: "\<forall>y<u. eventually (\<lambda>x. y < f x) net" "\<forall>y>v. eventually (\<lambda>x. f x < y) net"
  show "u \<le> v"
  proof (rule ccontr)
    assume "\<not> u \<le> v"
    then obtain t where "t < u" "v < t"
      using extreal_dense[of v u] by (auto simp: not_le)
    then have "eventually (\<lambda>x. t < f x \<and> f x < t) net"
      using * by (auto intro: eventually_conj)
    also have "(\<lambda>x. t < f x \<and> f x < t) = (\<lambda>x. False)" by (auto simp: fun_eq_iff)
    finally show False using ntriv by (auto simp: trivial_limit_def)
  qed
qed

lemma Liminf_mono:
  fixes f g :: "'a => extreal"
  assumes ev: "eventually (\<lambda>x. f x \<le> g x) net"
  shows "Liminf net f \<le> Liminf net g"
  unfolding Liminf_Sup
proof (safe intro!: Sup_mono bexI)
  fix a y assume "\<forall>y<a. eventually (\<lambda>x. y < f x) net" and "y < a"
  then have "eventually (\<lambda>x. y < f x) net" by auto
  then show "eventually (\<lambda>x. y < g x) net"
    by (rule eventually_rev_mp) (rule eventually_mono[OF _ ev], auto)
qed simp

lemma Liminf_eq:
  fixes f g :: "'a \<Rightarrow> extreal"
  assumes "eventually (\<lambda>x. f x = g x) net"
  shows "Liminf net f = Liminf net g"
  by (intro antisym Liminf_mono eventually_mono[OF _ assms]) auto

lemma Liminf_mono_all:
  fixes f g :: "'a \<Rightarrow> extreal"
  assumes "\<And>x. f x \<le> g x"
  shows "Liminf net f \<le> Liminf net g"
  using assms by (intro Liminf_mono always_eventually) auto

lemma Limsup_mono:
  fixes f g :: "'a \<Rightarrow> extreal"
  assumes ev: "eventually (\<lambda>x. f x \<le> g x) net"
  shows "Limsup net f \<le> Limsup net g"
  unfolding Limsup_Inf
proof (safe intro!: Inf_mono bexI)
  fix a y assume "\<forall>y>a. eventually (\<lambda>x. g x < y) net" and "a < y"
  then have "eventually (\<lambda>x. g x < y) net" by auto
  then show "eventually (\<lambda>x. f x < y) net"
    by (rule eventually_rev_mp) (rule eventually_mono[OF _ ev], auto)
qed simp

lemma Limsup_mono_all:
  fixes f g :: "'a \<Rightarrow> extreal"
  assumes "\<And>x. f x \<le> g x"
  shows "Limsup net f \<le> Limsup net g"
  using assms by (intro Limsup_mono always_eventually) auto

lemma Limsup_eq:
  fixes f g :: "'a \<Rightarrow> extreal"
  assumes "eventually (\<lambda>x. f x = g x) net"
  shows "Limsup net f = Limsup net g"
  by (intro antisym Limsup_mono eventually_mono[OF _ assms]) auto

abbreviation "liminf \<equiv> Liminf sequentially"

abbreviation "limsup \<equiv> Limsup sequentially"

lemma (in complete_lattice) less_INFD:
  assumes "y < INFI A f"" i \<in> A" shows "y < f i"
proof -
  note `y < INFI A f`
  also have "INFI A f \<le> f i" using `i \<in> A` by (rule INF_leI)
  finally show "y < f i" .
qed

lemma liminf_SUPR_INFI:
  fixes f :: "nat \<Rightarrow> extreal"
  shows "liminf f = (SUP n. INF m:{n..}. f m)"
  unfolding Liminf_Sup eventually_sequentially
proof (safe intro!: antisym complete_lattice_class.Sup_least)
  fix x assume *: "\<forall>y<x. \<exists>N. \<forall>n\<ge>N. y < f n" show "x \<le> (SUP n. INF m:{n..}. f m)"
  proof (rule extreal_le_extreal)
    fix y assume "y < x"
    with * obtain N where "\<And>n. N \<le> n \<Longrightarrow> y < f n" by auto
    then have "y \<le> (INF m:{N..}. f m)" by (force simp: le_INF_iff)
    also have "\<dots> \<le> (SUP n. INF m:{n..}. f m)" by (intro le_SUPI) auto
    finally show "y \<le> (SUP n. INF m:{n..}. f m)" .
  qed
next
  show "(SUP n. INF m:{n..}. f m) \<le> Sup {l. \<forall>y<l. \<exists>N. \<forall>n\<ge>N. y < f n}"
  proof (unfold SUPR_def, safe intro!: Sup_mono bexI)
    fix y n assume "y < INFI {n..} f"
    from less_INFD[OF this] show "\<exists>N. \<forall>n\<ge>N. y < f n" by (intro exI[of _ n]) auto
  qed (rule order_refl)
qed

lemma tail_same_limsup:
  fixes X Y :: "nat => extreal"
  assumes "\<And>n. N \<le> n \<Longrightarrow> X n = Y n"
  shows "limsup X = limsup Y"
  using Limsup_eq[of X Y sequentially] eventually_sequentially assms by auto

lemma tail_same_liminf:
  fixes X Y :: "nat => extreal"
  assumes "\<And>n. N \<le> n \<Longrightarrow> X n = Y n"
  shows "liminf X = liminf Y"
  using Liminf_eq[of X Y sequentially] eventually_sequentially assms by auto

lemma liminf_mono:
  fixes X Y :: "nat \<Rightarrow> extreal"
  assumes "\<And>n. N \<le> n \<Longrightarrow> X n <= Y n"
  shows "liminf X \<le> liminf Y"
  using Liminf_mono[of X Y sequentially] eventually_sequentially assms by auto

lemma limsup_mono:
  fixes X Y :: "nat => extreal"
  assumes "\<And>n. N \<le> n \<Longrightarrow> X n <= Y n"
  shows "limsup X \<le> limsup Y"
  using Limsup_mono[of X Y sequentially] eventually_sequentially assms by auto

declare trivial_limit_sequentially[simp]

lemma
  fixes X :: "nat \<Rightarrow> extreal"
  shows extreal_incseq_uminus[simp]: "incseq (\<lambda>i. - X i) = decseq X"
    and extreal_decseq_uminus[simp]: "decseq (\<lambda>i. - X i) = incseq X"
  unfolding incseq_def decseq_def by auto

lemma liminf_bounded:
  fixes X Y :: "nat \<Rightarrow> extreal"
  assumes "\<And>n. N \<le> n \<Longrightarrow> C \<le> X n"
  shows "C \<le> liminf X"
  using liminf_mono[of N "\<lambda>n. C" X] assms Liminf_const[of sequentially C] by simp

lemma limsup_bounded:
  fixes X Y :: "nat => extreal"
  assumes "\<And>n. N \<le> n \<Longrightarrow> X n <= C"
  shows "limsup X \<le> C"
  using limsup_mono[of N X "\<lambda>n. C"] assms Limsup_const[of sequentially C] by simp

lemma liminf_bounded_iff:
  fixes x :: "nat \<Rightarrow> extreal"
  shows "C \<le> liminf x \<longleftrightarrow> (\<forall>B<C. \<exists>N. \<forall>n\<ge>N. B < x n)" (is "?lhs <-> ?rhs")
proof safe
  fix B assume "B < C" "C \<le> liminf x"
  then have "B < liminf x" by auto
  then obtain N where "B < (INF m:{N..}. x m)"
    unfolding liminf_SUPR_INFI SUPR_def less_Sup_iff by auto
  from less_INFD[OF this] show "\<exists>N. \<forall>n\<ge>N. B < x n" by auto
next
  assume *: "\<forall>B<C. \<exists>N. \<forall>n\<ge>N. B < x n"
  { fix B assume "B<C"
    then obtain N where "\<forall>n\<ge>N. B < x n" using `?rhs` by auto
    hence "B \<le> (INF m:{N..}. x m)" by (intro le_INFI) auto
    also have "... \<le> liminf x" unfolding liminf_SUPR_INFI by (intro le_SUPI) simp
    finally have "B \<le> liminf x" .
  } then show "?lhs" by (metis * leD liminf_bounded linorder_le_less_linear)
qed

lemma liminf_subseq_mono:
  fixes X :: "nat \<Rightarrow> extreal"
  assumes "subseq r"
  shows "liminf X \<le> liminf (X \<circ> r) "
proof-
  have "\<And>n. (INF m:{n..}. X m) \<le> (INF m:{n..}. (X \<circ> r) m)"
  proof (safe intro!: INF_mono)
    fix n m :: nat assume "n \<le> m" then show "\<exists>ma\<in>{n..}. X ma \<le> (X \<circ> r) m"
      using seq_suble[OF `subseq r`, of m] by (intro bexI[of _ "r m"]) auto
  qed
  then show ?thesis by (auto intro!: SUP_mono simp: liminf_SUPR_INFI comp_def)
qed

lemma extreal_real': assumes "\<bar>x\<bar> \<noteq> \<infinity>" shows "extreal (real x) = x"
  using assms by auto

lemma extreal_le_extreal_bounded:
  fixes x y z :: extreal
  assumes "z \<le> y"
  assumes *: "\<And>B. z < B \<Longrightarrow> B < x \<Longrightarrow> B \<le> y"
  shows "x \<le> y"
proof (rule extreal_le_extreal)
  fix B assume "B < x"
  show "B \<le> y"
  proof cases
    assume "z < B" from *[OF this `B < x`] show "B \<le> y" .
  next
    assume "\<not> z < B" with `z \<le> y` show "B \<le> y" by auto
  qed
qed

lemma fixes x y :: extreal
  shows Sup_atMost[simp]: "Sup {.. y} = y"
    and Sup_lessThan[simp]: "Sup {..< y} = y"
    and Sup_atLeastAtMost[simp]: "x \<le> y \<Longrightarrow> Sup { x .. y} = y"
    and Sup_greaterThanAtMost[simp]: "x < y \<Longrightarrow> Sup { x <.. y} = y"
    and Sup_atLeastLessThan[simp]: "x < y \<Longrightarrow> Sup { x ..< y} = y"
  by (auto simp: Sup_extreal_def intro!: Least_equality
           intro: extreal_le_extreal extreal_le_extreal_bounded[of x])

lemma Sup_greaterThanlessThan[simp]:
  fixes x y :: extreal assumes "x < y" shows "Sup { x <..< y} = y"
  unfolding Sup_extreal_def
proof (intro Least_equality extreal_le_extreal_bounded[of _ _ y])
  fix z assume z: "\<forall>u\<in>{x<..<y}. u \<le> z"
  from extreal_dense[OF `x < y`] guess w .. note w = this
  with z[THEN bspec, of w] show "x \<le> z" by auto
qed auto

lemma real_extreal_id: "real o extreal = id"
proof-
{ fix x have "(real o extreal) x = id x" by auto }
from this show ?thesis using ext by blast
qed


lemma open_image_extreal: "open(UNIV-{\<infinity>,(-\<infinity>)})"
by (metis range_extreal open_extreal open_UNIV)

lemma extreal_le_distrib:
  fixes a b c :: extreal shows "c * (a + b) \<le> c * a + c * b"
  by (cases rule: extreal3_cases[of a b c])
     (auto simp add: field_simps not_le mult_le_0_iff mult_less_0_iff)

lemma extreal_pos_distrib:
  fixes a b c :: extreal assumes "0 \<le> c" "c \<noteq> \<infinity>" shows "c * (a + b) = c * a + c * b"
  using assms by (cases rule: extreal3_cases[of a b c])
                 (auto simp add: field_simps not_le mult_le_0_iff mult_less_0_iff)

lemma extreal_pos_le_distrib:
fixes a b c :: extreal
assumes "c>=0"
shows "c * (a + b) <= c * a + c * b"
  using assms by (cases rule: extreal3_cases[of a b c])
                 (auto simp add: field_simps)

lemma extreal_max_mono:
  "[| (a::extreal) <= b; c <= d |] ==> max a c <= max b d"
  by (metis sup_extreal_def sup_mono)


lemma extreal_max_least:
  "[| (a::extreal) <= x; c <= x |] ==> max a c <= x"
  by (metis sup_extreal_def sup_least)

end
