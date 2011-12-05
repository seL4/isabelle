(*  Title:      HOL/Library/Extended_Real.thy
    Author:     Johannes Hölzl, TU München
    Author:     Robert Himmelmann, TU München
    Author:     Armin Heller, TU München
    Author:     Bogdan Grechuk, University of Edinburgh
*)

header {* Extended real number line *}

theory Extended_Real
imports Complex_Main Extended_Nat
begin

text {*

For more lemmas about the extended real numbers go to
  @{text "src/HOL/Multivariate_Analysis/Extended_Real_Limits.thy"}

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
  by (rule antisym) (auto intro!: SUP_least SUP_upper2)

lemma INFI_pair:
  "(INF i : A. INF j : B. f i j) = (INF p : A \<times> B. f (fst p) (snd p))"
  by (rule antisym) (auto intro!: INF_greatest INF_lower2)

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

definition "ereal_of_enat n = (case n of enat n \<Rightarrow> ereal (real n) | \<infinity> \<Rightarrow> \<infinity>)"

declare [[coercion "ereal :: real \<Rightarrow> ereal"]]
declare [[coercion "ereal_of_enat :: enat \<Rightarrow> ereal"]]
declare [[coercion "(\<lambda>n. ereal (real n)) :: nat \<Rightarrow> ereal"]]

lemma ereal_uminus_uminus[simp]:
  fixes a :: ereal shows "- (- a) = a"
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
  "-PInfty = MInfty"
  by simp_all

lemma inj_ereal[simp]: "inj_on ereal A"
  unfolding inj_on_def by auto

lemma ereal_cases[case_names real PInf MInf, cases type: ereal]:
  assumes "\<And>r. x = ereal r \<Longrightarrow> P"
  assumes "x = \<infinity> \<Longrightarrow> P"
  assumes "x = -\<infinity> \<Longrightarrow> P"
  shows P
  using assms by (cases x) auto

lemmas ereal2_cases = ereal_cases[case_product ereal_cases]
lemmas ereal3_cases = ereal2_cases[case_product ereal_cases]

lemma ereal_uminus_eq_iff[simp]:
  fixes a b :: ereal shows "-a = -b \<longleftrightarrow> a = b"
  by (cases rule: ereal2_cases[of a b]) simp_all

function of_ereal :: "ereal \<Rightarrow> real" where
"of_ereal (ereal r) = r" |
"of_ereal \<infinity> = 0" |
"of_ereal (-\<infinity>) = 0"
  by (auto intro: ereal_cases)
termination proof qed (rule wf_empty)

defs (overloaded)
  real_of_ereal_def [code_unfold]: "real \<equiv> of_ereal"

lemma real_of_ereal[simp]:
    "real (- x :: ereal) = - (real x)"
    "real (ereal r) = r"
    "real (\<infinity>::ereal) = 0"
  by (cases x) (simp_all add: real_of_ereal_def)

lemma range_ereal[simp]: "range ereal = UNIV - {\<infinity>, -\<infinity>}"
proof safe
  fix x assume "x \<notin> range ereal" "x \<noteq> \<infinity>"
  then show "x = -\<infinity>" by (cases x) auto
qed auto

lemma ereal_range_uminus[simp]: "range uminus = (UNIV::ereal set)"
proof safe
  fix x :: ereal show "x \<in> range uminus" by (intro image_eqI[of _ _ "-x"]) auto
qed auto

instantiation ereal :: number
begin
definition [simp]: "number_of x = ereal (number_of x)"
instance proof qed
end

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

lemma abs_eq_infinity_cases[elim!]: "\<lbrakk> \<bar>x :: ereal\<bar> = \<infinity> ; x = \<infinity> \<Longrightarrow> P ; x = -\<infinity> \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  by (cases x) auto

lemma abs_neq_infinity_cases[elim!]: "\<lbrakk> \<bar>x :: ereal\<bar> \<noteq> \<infinity> ; \<And>r. x = ereal r \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  by (cases x) auto

lemma abs_ereal_uminus[simp]: "\<bar>- x\<bar> = \<bar>x::ereal\<bar>"
  by (cases x) auto

subsubsection "Addition"

instantiation ereal :: comm_monoid_add
begin

definition "0 = ereal 0"

function plus_ereal where
"ereal r + ereal p = ereal (r + p)" |
"\<infinity> + a = (\<infinity>::ereal)" |
"a + \<infinity> = (\<infinity>::ereal)" |
"ereal r + -\<infinity> = - \<infinity>" |
"-\<infinity> + ereal p = -(\<infinity>::ereal)" |
"-\<infinity> + -\<infinity> = -(\<infinity>::ereal)"
proof -
  case (goal1 P x)
  moreover then obtain a b where "x = (a, b)" by (cases x) auto
  ultimately show P
   by (cases rule: ereal2_cases[of a b]) auto
qed auto
termination proof qed (rule wf_empty)

lemma Infty_neq_0[simp]:
  "(\<infinity>::ereal) \<noteq> 0" "0 \<noteq> (\<infinity>::ereal)"
  "-(\<infinity>::ereal) \<noteq> 0" "0 \<noteq> -(\<infinity>::ereal)"
  by (simp_all add: zero_ereal_def)

lemma ereal_eq_0[simp]:
  "ereal r = 0 \<longleftrightarrow> r = 0"
  "0 = ereal r \<longleftrightarrow> r = 0"
  unfolding zero_ereal_def by simp_all

instance
proof
  fix a :: ereal show "0 + a = a"
    by (cases a) (simp_all add: zero_ereal_def)
  fix b :: ereal show "a + b = b + a"
    by (cases rule: ereal2_cases[of a b]) simp_all
  fix c :: ereal show "a + b + c = a + (b + c)"
    by (cases rule: ereal3_cases[of a b c]) simp_all
qed
end

lemma real_of_ereal_0[simp]: "real (0::ereal) = 0"
  unfolding real_of_ereal_def zero_ereal_def by simp

lemma abs_ereal_zero[simp]: "\<bar>0\<bar> = (0::ereal)"
  unfolding zero_ereal_def abs_ereal.simps by simp

lemma ereal_uminus_zero[simp]:
  "- 0 = (0::ereal)"
  by (simp add: zero_ereal_def)

lemma ereal_uminus_zero_iff[simp]:
  fixes a :: ereal shows "-a = 0 \<longleftrightarrow> a = 0"
  by (cases a) simp_all

lemma ereal_plus_eq_PInfty[simp]:
  fixes a b :: ereal shows "a + b = \<infinity> \<longleftrightarrow> a = \<infinity> \<or> b = \<infinity>"
  by (cases rule: ereal2_cases[of a b]) auto

lemma ereal_plus_eq_MInfty[simp]:
  fixes a b :: ereal shows "a + b = -\<infinity> \<longleftrightarrow>
    (a = -\<infinity> \<or> b = -\<infinity>) \<and> a \<noteq> \<infinity> \<and> b \<noteq> \<infinity>"
  by (cases rule: ereal2_cases[of a b]) auto

lemma ereal_add_cancel_left:
  fixes a b :: ereal assumes "a \<noteq> -\<infinity>"
  shows "a + b = a + c \<longleftrightarrow> (a = \<infinity> \<or> b = c)"
  using assms by (cases rule: ereal3_cases[of a b c]) auto

lemma ereal_add_cancel_right:
  fixes a b :: ereal assumes "a \<noteq> -\<infinity>"
  shows "b + a = c + a \<longleftrightarrow> (a = \<infinity> \<or> b = c)"
  using assms by (cases rule: ereal3_cases[of a b c]) auto

lemma ereal_real:
  "ereal (real x) = (if \<bar>x\<bar> = \<infinity> then 0 else x)"
  by (cases x) simp_all

lemma real_of_ereal_add:
  fixes a b :: ereal
  shows "real (a + b) = (if (\<bar>a\<bar> = \<infinity>) \<and> (\<bar>b\<bar> = \<infinity>) \<or> (\<bar>a\<bar> \<noteq> \<infinity>) \<and> (\<bar>b\<bar> \<noteq> \<infinity>) then real a + real b else 0)"
  by (cases rule: ereal2_cases[of a b]) auto

subsubsection "Linear order on @{typ ereal}"

instantiation ereal :: linorder
begin

function less_ereal where
"   ereal x < ereal y     \<longleftrightarrow> x < y" |
"(\<infinity>::ereal) < a           \<longleftrightarrow> False" |
"         a < -(\<infinity>::ereal) \<longleftrightarrow> False" |
"ereal x    < \<infinity>           \<longleftrightarrow> True" |
"        -\<infinity> < ereal r     \<longleftrightarrow> True" |
"        -\<infinity> < (\<infinity>::ereal) \<longleftrightarrow> True"
proof -
  case (goal1 P x)
  moreover then obtain a b where "x = (a,b)" by (cases x) auto
  ultimately show P by (cases rule: ereal2_cases[of a b]) auto
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
  "x \<le> -\<infinity> \<longleftrightarrow> x = -\<infinity>"
  by (auto simp add: less_eq_ereal_def)

lemma ereal_less[simp]:
  "ereal r < 0 \<longleftrightarrow> (r < 0)"
  "0 < ereal r \<longleftrightarrow> (0 < r)"
  "0 < (\<infinity>::ereal)"
  "-(\<infinity>::ereal) < 0"
  by (simp_all add: zero_ereal_def)

lemma ereal_less_eq[simp]:
  "x \<le> (\<infinity>::ereal)"
  "-(\<infinity>::ereal) \<le> x"
  "ereal r \<le> ereal p \<longleftrightarrow> r \<le> p"
  "ereal r \<le> 0 \<longleftrightarrow> r \<le> 0"
  "0 \<le> ereal r \<longleftrightarrow> 0 \<le> r"
  by (auto simp add: less_eq_ereal_def zero_ereal_def)

lemma ereal_infty_less_eq2:
  "a \<le> b \<Longrightarrow> a = \<infinity> \<Longrightarrow> b = (\<infinity>::ereal)"
  "a \<le> b \<Longrightarrow> b = -\<infinity> \<Longrightarrow> a = -(\<infinity>::ereal)"
  by simp_all

instance
proof
  fix x :: ereal show "x \<le> x"
    by (cases x) simp_all
  fix y :: ereal show "x < y \<longleftrightarrow> x \<le> y \<and> \<not> y \<le> x"
    by (cases rule: ereal2_cases[of x y]) auto
  show "x \<le> y \<or> y \<le> x "
    by (cases rule: ereal2_cases[of x y]) auto
  { assume "x \<le> y" "y \<le> x" then show "x = y"
    by (cases rule: ereal2_cases[of x y]) auto }
  { fix z assume "x \<le> y" "y \<le> z" then show "x \<le> z"
    by (cases rule: ereal3_cases[of x y z]) auto }
qed
end

instance ereal :: ordered_ab_semigroup_add
proof
  fix a b c :: ereal assume "a \<le> b" then show "c + a \<le> c + b"
    by (cases rule: ereal3_cases[of a b c]) auto
qed

lemma real_of_ereal_positive_mono:
  fixes x y :: ereal shows "\<lbrakk>0 \<le> x; x \<le> y; y \<noteq> \<infinity>\<rbrakk> \<Longrightarrow> real x \<le> real y"
  by (cases rule: ereal2_cases[of x y]) auto

lemma ereal_MInfty_lessI[intro, simp]:
  fixes a :: ereal shows "a \<noteq> -\<infinity> \<Longrightarrow> -\<infinity> < a"
  by (cases a) auto

lemma ereal_less_PInfty[intro, simp]:
  fixes a :: ereal shows "a \<noteq> \<infinity> \<Longrightarrow> a < \<infinity>"
  by (cases a) auto

lemma ereal_less_ereal_Ex:
  fixes a b :: ereal
  shows "x < ereal r \<longleftrightarrow> x = -\<infinity> \<or> (\<exists>p. p < r \<and> x = ereal p)"
  by (cases x) auto

lemma less_PInf_Ex_of_nat: "x \<noteq> \<infinity> \<longleftrightarrow> (\<exists>n::nat. x < ereal (real n))"
proof (cases x)
  case (real r) then show ?thesis
    using reals_Archimedean2[of r] by simp
qed simp_all

lemma ereal_add_mono:
  fixes a b c d :: ereal assumes "a \<le> b" "c \<le> d" shows "a + c \<le> b + d"
  using assms
  apply (cases a)
  apply (cases rule: ereal3_cases[of b c d], auto)
  apply (cases rule: ereal3_cases[of b c d], auto)
  done

lemma ereal_minus_le_minus[simp]:
  fixes a b :: ereal shows "- a \<le> - b \<longleftrightarrow> b \<le> a"
  by (cases rule: ereal2_cases[of a b]) auto

lemma ereal_minus_less_minus[simp]:
  fixes a b :: ereal shows "- a < - b \<longleftrightarrow> b < a"
  by (cases rule: ereal2_cases[of a b]) auto

lemma ereal_le_real_iff:
  "x \<le> real y \<longleftrightarrow> ((\<bar>y\<bar> \<noteq> \<infinity> \<longrightarrow> ereal x \<le> y) \<and> (\<bar>y\<bar> = \<infinity> \<longrightarrow> x \<le> 0))"
  by (cases y) auto

lemma real_le_ereal_iff:
  "real y \<le> x \<longleftrightarrow> ((\<bar>y\<bar> \<noteq> \<infinity> \<longrightarrow> y \<le> ereal x) \<and> (\<bar>y\<bar> = \<infinity> \<longrightarrow> 0 \<le> x))"
  by (cases y) auto

lemma ereal_less_real_iff:
  "x < real y \<longleftrightarrow> ((\<bar>y\<bar> \<noteq> \<infinity> \<longrightarrow> ereal x < y) \<and> (\<bar>y\<bar> = \<infinity> \<longrightarrow> x < 0))"
  by (cases y) auto

lemma real_less_ereal_iff:
  "real y < x \<longleftrightarrow> ((\<bar>y\<bar> \<noteq> \<infinity> \<longrightarrow> y < ereal x) \<and> (\<bar>y\<bar> = \<infinity> \<longrightarrow> 0 < x))"
  by (cases y) auto

lemma real_of_ereal_pos:
  fixes x :: ereal shows "0 \<le> x \<Longrightarrow> 0 \<le> real x" by (cases x) auto

lemmas real_of_ereal_ord_simps =
  ereal_le_real_iff real_le_ereal_iff ereal_less_real_iff real_less_ereal_iff

lemma abs_ereal_ge0[simp]: "0 \<le> x \<Longrightarrow> \<bar>x :: ereal\<bar> = x"
  by (cases x) auto

lemma abs_ereal_less0[simp]: "x < 0 \<Longrightarrow> \<bar>x :: ereal\<bar> = -x"
  by (cases x) auto

lemma abs_ereal_pos[simp]: "0 \<le> \<bar>x :: ereal\<bar>"
  by (cases x) auto

lemma real_of_ereal_le_0[simp]: "real (x :: ereal) \<le> 0 \<longleftrightarrow> (x \<le> 0 \<or> x = \<infinity>)"
  by (cases x) auto

lemma abs_real_of_ereal[simp]: "\<bar>real (x :: ereal)\<bar> = real \<bar>x\<bar>"
  by (cases x) auto

lemma zero_less_real_of_ereal:
  fixes x :: ereal shows "0 < real x \<longleftrightarrow> (0 < x \<and> x \<noteq> \<infinity>)"
  by (cases x) auto

lemma ereal_0_le_uminus_iff[simp]:
  fixes a :: ereal shows "0 \<le> -a \<longleftrightarrow> a \<le> 0"
  by (cases rule: ereal2_cases[of a]) auto

lemma ereal_uminus_le_0_iff[simp]:
  fixes a :: ereal shows "-a \<le> 0 \<longleftrightarrow> 0 \<le> a"
  by (cases rule: ereal2_cases[of a]) auto

lemma ereal_dense2: "x < y \<Longrightarrow> \<exists>z. x < ereal z \<and> ereal z < y"
  using lt_ex gt_ex dense by (cases x y rule: ereal2_cases) auto

lemma ereal_dense:
  fixes x y :: ereal assumes "x < y"
  shows "\<exists>z. x < z \<and> z < y"
  using ereal_dense2[OF `x < y`] by blast

lemma ereal_add_strict_mono:
  fixes a b c d :: ereal
  assumes "a = b" "0 \<le> a" "a \<noteq> \<infinity>" "c < d"
  shows "a + c < b + d"
  using assms by (cases rule: ereal3_cases[case_product ereal_cases, of a b c d]) auto

lemma ereal_less_add: 
  fixes a b c :: ereal shows "\<bar>a\<bar> \<noteq> \<infinity> \<Longrightarrow> c < b \<Longrightarrow> a + c < a + b"
  by (cases rule: ereal2_cases[of b c]) auto

lemma ereal_uminus_eq_reorder: "- a = b \<longleftrightarrow> a = (-b::ereal)" by auto

lemma ereal_uminus_less_reorder: "- a < b \<longleftrightarrow> -b < (a::ereal)"
  by (subst (3) ereal_uminus_uminus[symmetric]) (simp only: ereal_minus_less_minus)

lemma ereal_uminus_le_reorder: "- a \<le> b \<longleftrightarrow> -b \<le> (a::ereal)"
  by (subst (3) ereal_uminus_uminus[symmetric]) (simp only: ereal_minus_le_minus)

lemmas ereal_uminus_reorder =
  ereal_uminus_eq_reorder ereal_uminus_less_reorder ereal_uminus_le_reorder

lemma ereal_bot:
  fixes x :: ereal assumes "\<And>B. x \<le> ereal B" shows "x = - \<infinity>"
proof (cases x)
  case (real r) with assms[of "r - 1"] show ?thesis by auto
next case PInf with assms[of 0] show ?thesis by auto
next case MInf then show ?thesis by simp
qed

lemma ereal_top:
  fixes x :: ereal assumes "\<And>B. x \<ge> ereal B" shows "x = \<infinity>"
proof (cases x)
  case (real r) with assms[of "r + 1"] show ?thesis by auto
next case MInf with assms[of 0] show ?thesis by auto
next case PInf then show ?thesis by simp
qed

lemma
  shows ereal_max[simp]: "ereal (max x y) = max (ereal x) (ereal y)"
    and ereal_min[simp]: "ereal (min x y) = min (ereal x) (ereal y)"
  by (simp_all add: min_def max_def)

lemma ereal_max_0: "max 0 (ereal r) = ereal (max 0 r)"
  by (auto simp: zero_ereal_def)

lemma
  fixes f :: "nat \<Rightarrow> ereal"
  shows incseq_uminus[simp]: "incseq (\<lambda>x. - f x) \<longleftrightarrow> decseq f"
  and decseq_uminus[simp]: "decseq (\<lambda>x. - f x) \<longleftrightarrow> incseq f"
  unfolding decseq_def incseq_def by auto

lemma incseq_ereal: "incseq f \<Longrightarrow> incseq (\<lambda>x. ereal (f x))"
  unfolding incseq_def by auto

lemma ereal_add_nonneg_nonneg:
  fixes a b :: ereal shows "0 \<le> a \<Longrightarrow> 0 \<le> b \<Longrightarrow> 0 \<le> a + b"
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

instantiation ereal :: "{comm_monoid_mult, sgn}"
begin

definition "1 = ereal 1"

function sgn_ereal where
  "sgn (ereal r) = ereal (sgn r)"
| "sgn (\<infinity>::ereal) = 1"
| "sgn (-\<infinity>::ereal) = -1"
by (auto intro: ereal_cases)
termination proof qed (rule wf_empty)

function times_ereal where
"ereal r * ereal p = ereal (r * p)" |
"ereal r * \<infinity> = (if r = 0 then 0 else if r > 0 then \<infinity> else -\<infinity>)" |
"\<infinity> * ereal r = (if r = 0 then 0 else if r > 0 then \<infinity> else -\<infinity>)" |
"ereal r * -\<infinity> = (if r = 0 then 0 else if r > 0 then -\<infinity> else \<infinity>)" |
"-\<infinity> * ereal r = (if r = 0 then 0 else if r > 0 then -\<infinity> else \<infinity>)" |
"(\<infinity>::ereal) * \<infinity> = \<infinity>" |
"-(\<infinity>::ereal) * \<infinity> = -\<infinity>" |
"(\<infinity>::ereal) * -\<infinity> = -\<infinity>" |
"-(\<infinity>::ereal) * -\<infinity> = \<infinity>"
proof -
  case (goal1 P x)
  moreover then obtain a b where "x = (a, b)" by (cases x) auto
  ultimately show P by (cases rule: ereal2_cases[of a b]) auto
qed simp_all
termination by (relation "{}") simp

instance
proof
  fix a :: ereal show "1 * a = a"
    by (cases a) (simp_all add: one_ereal_def)
  fix b :: ereal show "a * b = b * a"
    by (cases rule: ereal2_cases[of a b]) simp_all
  fix c :: ereal show "a * b * c = a * (b * c)"
    by (cases rule: ereal3_cases[of a b c])
       (simp_all add: zero_ereal_def zero_less_mult_iff)
qed
end

lemma real_of_ereal_le_1:
  fixes a :: ereal shows "a \<le> 1 \<Longrightarrow> real a \<le> 1"
  by (cases a) (auto simp: one_ereal_def)

lemma abs_ereal_one[simp]: "\<bar>1\<bar> = (1::ereal)"
  unfolding one_ereal_def by simp

lemma ereal_mult_zero[simp]:
  fixes a :: ereal shows "a * 0 = 0"
  by (cases a) (simp_all add: zero_ereal_def)

lemma ereal_zero_mult[simp]:
  fixes a :: ereal shows "0 * a = 0"
  by (cases a) (simp_all add: zero_ereal_def)

lemma ereal_m1_less_0[simp]:
  "-(1::ereal) < 0"
  by (simp add: zero_ereal_def one_ereal_def)

lemma ereal_zero_m1[simp]:
  "1 \<noteq> (0::ereal)"
  by (simp add: zero_ereal_def one_ereal_def)

lemma ereal_times_0[simp]:
  fixes x :: ereal shows "0 * x = 0"
  by (cases x) (auto simp: zero_ereal_def)

lemma ereal_times[simp]:
  "1 \<noteq> (\<infinity>::ereal)" "(\<infinity>::ereal) \<noteq> 1"
  "1 \<noteq> -(\<infinity>::ereal)" "-(\<infinity>::ereal) \<noteq> 1"
  by (auto simp add: times_ereal_def one_ereal_def)

lemma ereal_plus_1[simp]:
  "1 + ereal r = ereal (r + 1)" "ereal r + 1 = ereal (r + 1)"
  "1 + -(\<infinity>::ereal) = -\<infinity>" "-(\<infinity>::ereal) + 1 = -\<infinity>"
  unfolding one_ereal_def by auto

lemma ereal_zero_times[simp]:
  fixes a b :: ereal shows "a * b = 0 \<longleftrightarrow> a = 0 \<or> b = 0"
  by (cases rule: ereal2_cases[of a b]) auto

lemma ereal_mult_eq_PInfty[simp]:
  shows "a * b = (\<infinity>::ereal) \<longleftrightarrow>
    (a = \<infinity> \<and> b > 0) \<or> (a > 0 \<and> b = \<infinity>) \<or> (a = -\<infinity> \<and> b < 0) \<or> (a < 0 \<and> b = -\<infinity>)"
  by (cases rule: ereal2_cases[of a b]) auto

lemma ereal_mult_eq_MInfty[simp]:
  shows "a * b = -(\<infinity>::ereal) \<longleftrightarrow>
    (a = \<infinity> \<and> b < 0) \<or> (a < 0 \<and> b = \<infinity>) \<or> (a = -\<infinity> \<and> b > 0) \<or> (a > 0 \<and> b = -\<infinity>)"
  by (cases rule: ereal2_cases[of a b]) auto

lemma ereal_0_less_1[simp]: "0 < (1::ereal)"
  by (simp_all add: zero_ereal_def one_ereal_def)

lemma ereal_zero_one[simp]: "0 \<noteq> (1::ereal)"
  by (simp_all add: zero_ereal_def one_ereal_def)

lemma ereal_mult_minus_left[simp]:
  fixes a b :: ereal shows "-a * b = - (a * b)"
  by (cases rule: ereal2_cases[of a b]) auto

lemma ereal_mult_minus_right[simp]:
  fixes a b :: ereal shows "a * -b = - (a * b)"
  by (cases rule: ereal2_cases[of a b]) auto

lemma ereal_mult_infty[simp]:
  "a * (\<infinity>::ereal) = (if a = 0 then 0 else if 0 < a then \<infinity> else - \<infinity>)"
  by (cases a) auto

lemma ereal_infty_mult[simp]:
  "(\<infinity>::ereal) * a = (if a = 0 then 0 else if 0 < a then \<infinity> else - \<infinity>)"
  by (cases a) auto

lemma ereal_mult_strict_right_mono:
  assumes "a < b" and "0 < c" "c < (\<infinity>::ereal)"
  shows "a * c < b * c"
  using assms
  by (cases rule: ereal3_cases[of a b c])
     (auto simp: zero_le_mult_iff)

lemma ereal_mult_strict_left_mono:
  "\<lbrakk> a < b ; 0 < c ; c < (\<infinity>::ereal)\<rbrakk> \<Longrightarrow> c * a < c * b"
  using ereal_mult_strict_right_mono by (simp add: mult_commute[of c])

lemma ereal_mult_right_mono:
  fixes a b c :: ereal shows "\<lbrakk>a \<le> b; 0 \<le> c\<rbrakk> \<Longrightarrow> a*c \<le> b*c"
  using assms
  apply (cases "c = 0") apply simp
  by (cases rule: ereal3_cases[of a b c])
     (auto simp: zero_le_mult_iff)

lemma ereal_mult_left_mono:
  fixes a b c :: ereal shows "\<lbrakk>a \<le> b; 0 \<le> c\<rbrakk> \<Longrightarrow> c * a \<le> c * b"
  using ereal_mult_right_mono by (simp add: mult_commute[of c])

lemma zero_less_one_ereal[simp]: "0 \<le> (1::ereal)"
  by (simp add: one_ereal_def zero_ereal_def)

lemma ereal_0_le_mult[simp]: "0 \<le> a \<Longrightarrow> 0 \<le> b \<Longrightarrow> 0 \<le> a * (b :: ereal)"
  by (cases rule: ereal2_cases[of a b]) (auto simp: mult_nonneg_nonneg)

lemma ereal_right_distrib:
  fixes r a b :: ereal shows "0 \<le> a \<Longrightarrow> 0 \<le> b \<Longrightarrow> r * (a + b) = r * a + r * b"
  by (cases rule: ereal3_cases[of r a b]) (simp_all add: field_simps)

lemma ereal_left_distrib:
  fixes r a b :: ereal shows "0 \<le> a \<Longrightarrow> 0 \<le> b \<Longrightarrow> (a + b) * r = a * r + b * r"
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

lemma ereal_distrib:
  fixes a b c :: ereal
  assumes "a \<noteq> \<infinity> \<or> b \<noteq> -\<infinity>" "a \<noteq> -\<infinity> \<or> b \<noteq> \<infinity>" "\<bar>c\<bar> \<noteq> \<infinity>"
  shows "(a + b) * c = a * c + b * c"
  using assms
  by (cases rule: ereal3_cases[of a b c]) (simp_all add: field_simps)

lemma ereal_le_epsilon:
  fixes x y :: ereal
  assumes "ALL e. 0 < e --> x <= y + e"
  shows "x <= y"
proof-
{ assume a: "EX r. y = ereal r"
  from this obtain r where r_def: "y = ereal r" by auto
  { assume "x=(-\<infinity>)" hence ?thesis by auto }
  moreover
  { assume "~(x=(-\<infinity>))"
    from this obtain p where p_def: "x = ereal p"
    using a assms[rule_format, of 1] by (cases x) auto
    { fix e have "0 < e --> p <= r + e"
      using assms[rule_format, of "ereal e"] p_def r_def by auto }
    hence "p <= r" apply (subst field_le_epsilon) by auto
    hence ?thesis using r_def p_def by auto
  } ultimately have ?thesis by blast
}
moreover
{ assume "y=(-\<infinity>) | y=\<infinity>" hence ?thesis
    using assms[rule_format, of 1] by (cases x) auto
} ultimately show ?thesis by (cases y) auto
qed


lemma ereal_le_epsilon2:
  fixes x y :: ereal
  assumes "ALL e. 0 < e --> x <= y + ereal e"
  shows "x <= y"
proof-
{ fix e :: ereal assume "e>0"
  { assume "e=\<infinity>" hence "x<=y+e" by auto }
  moreover
  { assume "e~=\<infinity>"
    from this obtain r where "e = ereal r" using `e>0` apply (cases e) by auto
    hence "x<=y+e" using assms[rule_format, of r] `e>0` by auto
  } ultimately have "x<=y+e" by blast
} from this show ?thesis using ereal_le_epsilon by auto
qed

lemma ereal_le_real:
  fixes x y :: ereal
  assumes "ALL z. x <= ereal z --> y <= ereal z"
  shows "y <= x"
by (metis assms ereal_bot ereal_cases ereal_infty_less_eq(2) ereal_less_eq(1) linorder_le_cases)

lemma ereal_le_ereal:
  fixes x y :: ereal
  assumes "\<And>B. B < x \<Longrightarrow> B <= y"
  shows "x <= y"
by (metis assms ereal_dense leD linorder_le_less_linear)

lemma ereal_ge_ereal:
  fixes x y :: ereal
  assumes "ALL B. B>x --> B >= y"
  shows "x >= y"
by (metis assms ereal_dense leD linorder_le_less_linear)

lemma setprod_ereal_0:
  fixes f :: "'a \<Rightarrow> ereal"
  shows "(\<Prod>i\<in>A. f i) = 0 \<longleftrightarrow> (finite A \<and> (\<exists>i\<in>A. f i = 0))"
proof cases
  assume "finite A"
  then show ?thesis by (induct A) auto
qed auto

lemma setprod_ereal_pos:
  fixes f :: "'a \<Rightarrow> ereal" assumes pos: "\<And>i. i \<in> I \<Longrightarrow> 0 \<le> f i" shows "0 \<le> (\<Prod>i\<in>I. f i)"
proof cases
  assume "finite I" from this pos show ?thesis by induct auto
qed simp

lemma setprod_PInf:
  fixes f :: "'a \<Rightarrow> ereal"
  assumes "\<And>i. i \<in> I \<Longrightarrow> 0 \<le> f i"
  shows "(\<Prod>i\<in>I. f i) = \<infinity> \<longleftrightarrow> finite I \<and> (\<exists>i\<in>I. f i = \<infinity>) \<and> (\<forall>i\<in>I. f i \<noteq> 0)"
proof cases
  assume "finite I" from this assms show ?thesis
  proof (induct I)
    case (insert i I)
    then have pos: "0 \<le> f i" "0 \<le> setprod f I" by (auto intro!: setprod_ereal_pos)
    from insert have "(\<Prod>j\<in>insert i I. f j) = \<infinity> \<longleftrightarrow> setprod f I * f i = \<infinity>" by auto
    also have "\<dots> \<longleftrightarrow> (setprod f I = \<infinity> \<or> f i = \<infinity>) \<and> f i \<noteq> 0 \<and> setprod f I \<noteq> 0"
      using setprod_ereal_pos[of I f] pos
      by (cases rule: ereal2_cases[of "f i" "setprod f I"]) auto
    also have "\<dots> \<longleftrightarrow> finite (insert i I) \<and> (\<exists>j\<in>insert i I. f j = \<infinity>) \<and> (\<forall>j\<in>insert i I. f j \<noteq> 0)"
      using insert by (auto simp: setprod_ereal_0)
    finally show ?case .
  qed simp
qed simp

lemma setprod_ereal: "(\<Prod>i\<in>A. ereal (f i)) = ereal (setprod f A)"
proof cases
  assume "finite A" then show ?thesis
    by induct (auto simp: one_ereal_def)
qed (simp add: one_ereal_def)

subsubsection {* Power *}

lemma ereal_power[simp]: "(ereal x) ^ n = ereal (x^n)"
  by (induct n) (auto simp: one_ereal_def)

lemma ereal_power_PInf[simp]: "(\<infinity>::ereal) ^ n = (if n = 0 then 1 else \<infinity>)"
  by (induct n) (auto simp: one_ereal_def)

lemma ereal_power_uminus[simp]:
  fixes x :: ereal
  shows "(- x) ^ n = (if even n then x ^ n else - (x^n))"
  by (induct n) (auto simp: one_ereal_def)

lemma ereal_power_number_of[simp]:
  "(number_of num :: ereal) ^ n = ereal (number_of num ^ n)"
  by (induct n) (auto simp: one_ereal_def)

lemma zero_le_power_ereal[simp]:
  fixes a :: ereal assumes "0 \<le> a"
  shows "0 \<le> a ^ n"
  using assms by (induct n) (auto simp: ereal_zero_le_0_iff)

subsubsection {* Subtraction *}

lemma ereal_minus_minus_image[simp]:
  fixes S :: "ereal set"
  shows "uminus ` uminus ` S = S"
  by (auto simp: image_iff)

lemma ereal_uminus_lessThan[simp]:
  fixes a :: ereal shows "uminus ` {..<a} = {-a<..}"
proof (safe intro!: image_eqI)
  fix x assume "-a < x"
  then have "- x < - (- a)" by (simp del: ereal_uminus_uminus)
  then show "- x < a" by simp
qed auto

lemma ereal_uminus_greaterThan[simp]:
  "uminus ` {(a::ereal)<..} = {..<-a}"
  by (metis ereal_uminus_lessThan ereal_uminus_uminus
            ereal_minus_minus_image)

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

lemma ereal_x_minus_x[simp]:
  "x - x = (if \<bar>x\<bar> = \<infinity> then \<infinity> else 0::ereal)"
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
  shows "x \<le> z - y \<longleftrightarrow>
    (y = \<infinity> \<longrightarrow> z \<noteq> \<infinity> \<longrightarrow> x = -\<infinity>) \<and>
    (\<bar>y\<bar> \<noteq> \<infinity> \<longrightarrow> x + y \<le> z)"
  by (cases rule: ereal3_cases[of x y z]) auto

lemma ereal_le_minus:
  fixes x y z :: ereal
  shows "\<bar>y\<bar> \<noteq> \<infinity> \<Longrightarrow> x \<le> z - y \<longleftrightarrow> x + y \<le> z"
  by (auto simp: ereal_le_minus_iff)

lemma ereal_minus_less_iff:
  fixes x y z :: ereal
  shows "x - y < z \<longleftrightarrow>
    y \<noteq> -\<infinity> \<and> (y = \<infinity> \<longrightarrow> x \<noteq> \<infinity> \<and> z \<noteq> -\<infinity>) \<and>
    (y \<noteq> \<infinity> \<longrightarrow> x < z + y)"
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
  assumes "\<bar>x\<bar> \<noteq> \<infinity>" "0 < e"
  shows "x - e < x" "x < x + e"
using assms apply (cases x, cases e) apply auto
using assms by (cases x, cases e) auto

subsubsection {* Division *}

instantiation ereal :: inverse
begin

function inverse_ereal where
"inverse (ereal r) = (if r = 0 then \<infinity> else ereal (inverse r))" |
"inverse (\<infinity>::ereal) = 0" |
"inverse (-\<infinity>::ereal) = 0"
  by (auto intro: ereal_cases)
termination by (relation "{}") simp

definition "x / y = x * inverse (y :: ereal)"

instance proof qed
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
  fixes x :: ereal shows "x / x = (if \<bar>x\<bar> = \<infinity> \<or> x = 0 then 0 else 1)"
  by (cases x)
     (simp_all add: divide_real_def divide_ereal_def one_ereal_def)

lemma ereal_inv_inv[simp]:
  fixes x :: ereal shows "inverse (inverse x) = (if x \<noteq> -\<infinity> then x else \<infinity>)"
  by (cases x) auto

lemma ereal_inverse_minus[simp]:
  fixes x :: ereal shows "inverse (- x) = (if x = 0 then \<infinity> else -inverse x)"
  by (cases x) simp_all

lemma ereal_uminus_divide[simp]:
  fixes x y :: ereal shows "- x / y = - (x / y)"
  unfolding divide_ereal_def by simp

lemma ereal_divide_Infty[simp]:
  fixes x :: ereal shows "x / \<infinity> = 0" "x / -\<infinity> = 0"
  unfolding divide_ereal_def by simp_all

lemma ereal_divide_one[simp]:
  "x / 1 = (x::ereal)"
  unfolding divide_ereal_def by simp

lemma ereal_divide_ereal[simp]:
  "\<infinity> / ereal r = (if 0 \<le> r then \<infinity> else -\<infinity>)"
  unfolding divide_ereal_def by simp

lemma zero_le_divide_ereal[simp]:
  fixes a :: ereal assumes "0 \<le> a" "0 \<le> b"
  shows "0 \<le> a / b"
  using assms by (cases rule: ereal2_cases[of a b]) (auto simp: zero_le_divide_iff)

lemma ereal_le_divide_pos:
  fixes x y z :: ereal shows "x > 0 \<Longrightarrow> x \<noteq> \<infinity> \<Longrightarrow> y \<le> z / x \<longleftrightarrow> x * y \<le> z"
  by (cases rule: ereal3_cases[of x y z]) (auto simp: field_simps)

lemma ereal_divide_le_pos:
  fixes x y z :: ereal shows "x > 0 \<Longrightarrow> x \<noteq> \<infinity> \<Longrightarrow> z / x \<le> y \<longleftrightarrow> z \<le> x * y"
  by (cases rule: ereal3_cases[of x y z]) (auto simp: field_simps)

lemma ereal_le_divide_neg:
  fixes x y z :: ereal shows "x < 0 \<Longrightarrow> x \<noteq> -\<infinity> \<Longrightarrow> y \<le> z / x \<longleftrightarrow> z \<le> x * y"
  by (cases rule: ereal3_cases[of x y z]) (auto simp: field_simps)

lemma ereal_divide_le_neg:
  fixes x y z :: ereal shows "x < 0 \<Longrightarrow> x \<noteq> -\<infinity> \<Longrightarrow> z / x \<le> y \<longleftrightarrow> x * y \<le> z"
  by (cases rule: ereal3_cases[of x y z]) (auto simp: field_simps)

lemma ereal_inverse_antimono_strict:
  fixes x y :: ereal
  shows "0 \<le> x \<Longrightarrow> x < y \<Longrightarrow> inverse y < inverse x"
  by (cases rule: ereal2_cases[of x y]) auto

lemma ereal_inverse_antimono:
  fixes x y :: ereal
  shows "0 \<le> x \<Longrightarrow> x <= y \<Longrightarrow> inverse y <= inverse x"
  by (cases rule: ereal2_cases[of x y]) auto

lemma inverse_inverse_Pinfty_iff[simp]:
  fixes x :: ereal shows "inverse x = \<infinity> \<longleftrightarrow> x = 0"
  by (cases x) auto

lemma ereal_inverse_eq_0:
  fixes x :: ereal shows "inverse x = 0 \<longleftrightarrow> x = \<infinity> \<or> x = -\<infinity>"
  by (cases x) auto

lemma ereal_0_gt_inverse:
  fixes x :: ereal shows "0 < inverse x \<longleftrightarrow> x \<noteq> \<infinity> \<and> 0 \<le> x"
  by (cases x) auto

lemma ereal_mult_less_right:
  fixes a b c :: ereal
  assumes "b * a < c * a" "0 < a" "a < \<infinity>"
  shows "b < c"
  using assms
  by (cases rule: ereal3_cases[of a b c])
     (auto split: split_if_asm simp: zero_less_mult_iff zero_le_mult_iff)

lemma ereal_power_divide:
  fixes x y :: ereal shows "y \<noteq> 0 \<Longrightarrow> (x / y) ^ n = x^n / y^n"
  by (cases rule: ereal2_cases[of x y])
     (auto simp: one_ereal_def zero_ereal_def power_divide not_le
                 power_less_zero_eq zero_le_power_iff)

lemma ereal_le_mult_one_interval:
  fixes x y :: ereal
  assumes y: "y \<noteq> -\<infinity>"
  assumes z: "\<And>z. \<lbrakk> 0 < z ; z < 1 \<rbrakk> \<Longrightarrow> z * x \<le> y"
  shows "x \<le> y"
proof (cases x)
  case PInf with z[of "1 / 2"] show "x \<le> y" by (simp add: one_ereal_def)
next
  case (real r) note r = this
  show "x \<le> y"
  proof (cases y)
    case (real p) note p = this
    have "r \<le> p"
    proof (rule field_le_mult_one_interval)
      fix z :: real assume "0 < z" and "z < 1"
      with z[of "ereal z"]
      show "z * r \<le> p" using p r by (auto simp: zero_le_mult_iff one_ereal_def)
    qed
    then show "x \<le> y" using p r by simp
  qed (insert y, simp_all)
qed simp

subsection "Complete lattice"

instantiation ereal :: lattice
begin
definition [simp]: "sup x y = (max x y :: ereal)"
definition [simp]: "inf x y = (min x y :: ereal)"
instance proof qed simp_all
end

instantiation ereal :: complete_lattice
begin

definition "bot = (-\<infinity>::ereal)"
definition "top = (\<infinity>::ereal)"

definition "Sup S = (LEAST z. \<forall>x\<in>S. x \<le> z :: ereal)"
definition "Inf S = (GREATEST z. \<forall>x\<in>S. z \<le> x :: ereal)"

lemma ereal_complete_Sup:
  fixes S :: "ereal set" assumes "S \<noteq> {}"
  shows "\<exists>x. (\<forall>y\<in>S. y \<le> x) \<and> (\<forall>z. (\<forall>y\<in>S. y \<le> z) \<longrightarrow> x \<le> z)"
proof cases
  assume "\<exists>x. \<forall>a\<in>S. a \<le> ereal x"
  then obtain y where y: "\<And>a. a\<in>S \<Longrightarrow> a \<le> ereal y" by auto
  then have "\<infinity> \<notin> S" by force
  show ?thesis
  proof cases
    assume "S = {-\<infinity>}"
    then show ?thesis by (auto intro!: exI[of _ "-\<infinity>"])
  next
    assume "S \<noteq> {-\<infinity>}"
    with `S \<noteq> {}` `\<infinity> \<notin> S` obtain x where "x \<in> S - {-\<infinity>}" "x \<noteq> \<infinity>" by auto
    with y `\<infinity> \<notin> S` have "\<forall>z\<in>real ` (S - {-\<infinity>}). z \<le> y"
      by (auto simp: real_of_ereal_ord_simps)
    with complete_real[of "real ` (S - {-\<infinity>})"] `x \<in> S - {-\<infinity>}`
    obtain s where s:
       "\<forall>y\<in>S - {-\<infinity>}. real y \<le> s" "\<And>z. (\<forall>y\<in>S - {-\<infinity>}. real y \<le> z) \<Longrightarrow> s \<le> z"
       by auto
    show ?thesis
    proof (safe intro!: exI[of _ "ereal s"])
      fix z assume "z \<in> S" with `\<infinity> \<notin> S` show "z \<le> ereal s"
      proof (cases z)
        case (real r)
        then show ?thesis
          using s(1)[rule_format, of z] `z \<in> S` `z = ereal r` by auto
      qed auto
    next
      fix z assume *: "\<forall>y\<in>S. y \<le> z"
      with `S \<noteq> {-\<infinity>}` `S \<noteq> {}` show "ereal s \<le> z"
      proof (cases z)
        case (real u)
        with * have "s \<le> u"
          by (intro s(2)[of u]) (auto simp: real_of_ereal_ord_simps)
        then show ?thesis using real by simp
      qed auto
    qed
  qed
next
  assume *: "\<not> (\<exists>x. \<forall>a\<in>S. a \<le> ereal x)"
  show ?thesis
  proof (safe intro!: exI[of _ \<infinity>])
    fix y assume **: "\<forall>z\<in>S. z \<le> y"
    with * show "\<infinity> \<le> y"
    proof (cases y)
      case MInf with * ** show ?thesis by (force simp: not_le)
    qed auto
  qed simp
qed

lemma ereal_complete_Inf:
  fixes S :: "ereal set" assumes "S ~= {}"
  shows "EX x. (ALL y:S. x <= y) & (ALL z. (ALL y:S. z <= y) --> z <= x)"
proof-
def S1 == "uminus ` S"
hence "S1 ~= {}" using assms by auto
from this obtain x where x_def: "(ALL y:S1. y <= x) & (ALL z. (ALL y:S1. y <= z) --> x <= z)"
   using ereal_complete_Sup[of S1] by auto
{ fix z assume "ALL y:S. z <= y"
  hence "ALL y:S1. y <= -z" unfolding S1_def by auto
  hence "x <= -z" using x_def by auto
  hence "z <= -x"
    apply (subst ereal_uminus_uminus[symmetric])
    unfolding ereal_minus_le_minus . }
moreover have "(ALL y:S. -x <= y)"
   using x_def unfolding S1_def
   apply simp
   apply (subst (3) ereal_uminus_uminus[symmetric])
   unfolding ereal_minus_le_minus by simp
ultimately show ?thesis by auto
qed

lemma ereal_complete_uminus_eq:
  fixes S :: "ereal set"
  shows "(\<forall>y\<in>uminus`S. y \<le> x) \<and> (\<forall>z. (\<forall>y\<in>uminus`S. y \<le> z) \<longrightarrow> x \<le> z)
     \<longleftrightarrow> (\<forall>y\<in>S. -x \<le> y) \<and> (\<forall>z. (\<forall>y\<in>S. z \<le> y) \<longrightarrow> z \<le> -x)"
  by simp (metis ereal_minus_le_minus ereal_uminus_uminus)

lemma ereal_Sup_uminus_image_eq:
  fixes S :: "ereal set"
  shows "Sup (uminus ` S) = - Inf S"
proof cases
  assume "S = {}"
  moreover have "(THE x. All (op \<le> x)) = (-\<infinity>::ereal)"
    by (rule the_equality) (auto intro!: ereal_bot)
  moreover have "(SOME x. \<forall>y. y \<le> x) = (\<infinity>::ereal)"
    by (rule some_equality) (auto intro!: ereal_top)
  ultimately show ?thesis unfolding Inf_ereal_def Sup_ereal_def
    Least_def Greatest_def GreatestM_def by simp
next
  assume "S \<noteq> {}"
  with ereal_complete_Sup[of "uminus`S"]
  obtain x where x: "(\<forall>y\<in>S. -x \<le> y) \<and> (\<forall>z. (\<forall>y\<in>S. z \<le> y) \<longrightarrow> z \<le> -x)"
    unfolding ereal_complete_uminus_eq by auto
  show "Sup (uminus ` S) = - Inf S"
    unfolding Inf_ereal_def Greatest_def GreatestM_def
  proof (intro someI2[of _ _ "\<lambda>x. Sup (uminus`S) = - x"])
    show "(\<forall>y\<in>S. -x \<le> y) \<and> (\<forall>y. (\<forall>z\<in>S. y \<le> z) \<longrightarrow> y \<le> -x)"
      using x .
    fix x' assume "(\<forall>y\<in>S. x' \<le> y) \<and> (\<forall>y. (\<forall>z\<in>S. y \<le> z) \<longrightarrow> y \<le> x')"
    then have "(\<forall>y\<in>uminus`S. y \<le> - x') \<and> (\<forall>y. (\<forall>z\<in>uminus`S. z \<le> y) \<longrightarrow> - x' \<le> y)"
      unfolding ereal_complete_uminus_eq by simp
    then show "Sup (uminus ` S) = -x'"
      unfolding Sup_ereal_def ereal_uminus_eq_iff
      by (intro Least_equality) auto
  qed
qed

instance
proof
  { fix x :: ereal and A
    show "bot <= x" by (cases x) (simp_all add: bot_ereal_def)
    show "x <= top" by (simp add: top_ereal_def) }

  { fix x :: ereal and A assume "x : A"
    with ereal_complete_Sup[of A]
    obtain s where s: "\<forall>y\<in>A. y <= s" "\<forall>z. (\<forall>y\<in>A. y <= z) \<longrightarrow> s <= z" by auto
    hence "x <= s" using `x : A` by auto
    also have "... = Sup A" using s unfolding Sup_ereal_def
      by (auto intro!: Least_equality[symmetric])
    finally show "x <= Sup A" . }
  note le_Sup = this

  { fix x :: ereal and A assume *: "!!z. (z : A ==> z <= x)"
    show "Sup A <= x"
    proof (cases "A = {}")
      case True
      hence "Sup A = -\<infinity>" unfolding Sup_ereal_def
        by (auto intro!: Least_equality)
      thus "Sup A <= x" by simp
    next
      case False
      with ereal_complete_Sup[of A]
      obtain s where s: "\<forall>y\<in>A. y <= s" "\<forall>z. (\<forall>y\<in>A. y <= z) \<longrightarrow> s <= z" by auto
      hence "Sup A = s"
        unfolding Sup_ereal_def by (auto intro!: Least_equality)
      also have "s <= x" using * s by auto
      finally show "Sup A <= x" .
    qed }
  note Sup_le = this

  { fix x :: ereal and A assume "x \<in> A"
    with le_Sup[of "-x" "uminus`A"] show "Inf A \<le> x"
      unfolding ereal_Sup_uminus_image_eq by simp }

  { fix x :: ereal and A assume *: "!!z. (z : A ==> x <= z)"
    with Sup_le[of "uminus`A" "-x"] show "x \<le> Inf A"
      unfolding ereal_Sup_uminus_image_eq by force }
qed

end

instance ereal :: complete_linorder ..

lemma ereal_SUPR_uminus:
  fixes f :: "'a => ereal"
  shows "(SUP i : R. -(f i)) = -(INF i : R. f i)"
  unfolding SUP_def INF_def
  using ereal_Sup_uminus_image_eq[of "f`R"]
  by (simp add: image_image)

lemma ereal_INFI_uminus:
  fixes f :: "'a => ereal"
  shows "(INF i : R. -(f i)) = -(SUP i : R. f i)"
  using ereal_SUPR_uminus[of _ "\<lambda>x. - f x"] by simp

lemma ereal_Inf_uminus_image_eq: "Inf (uminus ` S) = - Sup (S::ereal set)"
  using ereal_Sup_uminus_image_eq[of "uminus ` S"] by (simp add: image_image)

lemma ereal_inj_on_uminus[intro, simp]: "inj_on uminus (A :: ereal set)"
  by (auto intro!: inj_onI)

lemma ereal_image_uminus_shift:
  fixes X Y :: "ereal set" shows "uminus ` X = Y \<longleftrightarrow> X = uminus ` Y"
proof
  assume "uminus ` X = Y"
  then have "uminus ` uminus ` X = uminus ` Y"
    by (simp add: inj_image_eq_iff)
  then show "X = uminus ` Y" by (simp add: image_image)
qed (simp add: image_image)

lemma Inf_ereal_iff:
  fixes z :: ereal
  shows "(!!x. x:X ==> z <= x) ==> (EX x:X. x<y) <-> Inf X < y"
  by (metis complete_lattice_class.Inf_greatest complete_lattice_class.Inf_lower less_le_not_le linear
            order_less_le_trans)

lemma Sup_eq_MInfty:
  fixes S :: "ereal set" shows "Sup S = -\<infinity> \<longleftrightarrow> S = {} \<or> S = {-\<infinity>}"
proof
  assume a: "Sup S = -\<infinity>"
  with complete_lattice_class.Sup_upper[of _ S]
  show "S={} \<or> S={-\<infinity>}" by auto
next
  assume "S={} \<or> S={-\<infinity>}" then show "Sup S = -\<infinity>"
    unfolding Sup_ereal_def by (auto intro!: Least_equality)
qed

lemma Inf_eq_PInfty:
  fixes S :: "ereal set" shows "Inf S = \<infinity> \<longleftrightarrow> S = {} \<or> S = {\<infinity>}"
  using Sup_eq_MInfty[of "uminus`S"]
  unfolding ereal_Sup_uminus_image_eq ereal_image_uminus_shift by simp

lemma Inf_eq_MInfty: 
  fixes S :: "ereal set" shows "-\<infinity> \<in> S \<Longrightarrow> Inf S = -\<infinity>"
  unfolding Inf_ereal_def
  by (auto intro!: Greatest_equality)

lemma Sup_eq_PInfty:
  fixes S :: "ereal set" shows "\<infinity> \<in> S \<Longrightarrow> Sup S = \<infinity>"
  unfolding Sup_ereal_def
  by (auto intro!: Least_equality)

lemma ereal_SUPI:
  fixes x :: ereal
  assumes "!!i. i : A ==> f i <= x"
  assumes "!!y. (!!i. i : A ==> f i <= y) ==> x <= y"
  shows "(SUP i:A. f i) = x"
  unfolding SUP_def Sup_ereal_def
  using assms by (auto intro!: Least_equality)

lemma ereal_INFI:
  fixes x :: ereal
  assumes "!!i. i : A ==> f i >= x"
  assumes "!!y. (!!i. i : A ==> f i >= y) ==> x >= y"
  shows "(INF i:A. f i) = x"
  unfolding INF_def Inf_ereal_def
  using assms by (auto intro!: Greatest_equality)

lemma Sup_ereal_close:
  fixes e :: ereal
  assumes "0 < e" and S: "\<bar>Sup S\<bar> \<noteq> \<infinity>" "S \<noteq> {}"
  shows "\<exists>x\<in>S. Sup S - e < x"
  using assms by (cases e) (auto intro!: less_Sup_iff[THEN iffD1])

lemma Inf_ereal_close:
  fixes e :: ereal assumes "\<bar>Inf X\<bar> \<noteq> \<infinity>" "0 < e"
  shows "\<exists>x\<in>X. x < Inf X + e"
proof (rule Inf_less_iff[THEN iffD1])
  show "Inf X < Inf X + e" using assms
    by (cases e) auto
qed

lemma SUP_nat_Infty: "(SUP i::nat. ereal (real i)) = \<infinity>"
proof -
  { fix x ::ereal assume "x \<noteq> \<infinity>"
    then have "\<exists>k::nat. x < ereal (real k)"
    proof (cases x)
      case MInf then show ?thesis by (intro exI[of _ 0]) auto
    next
      case (real r)
      moreover obtain k :: nat where "r < real k"
        using ex_less_of_nat by (auto simp: real_eq_of_nat)
      ultimately show ?thesis by auto
    qed simp }
  then show ?thesis
    using SUP_eq_top_iff[of UNIV "\<lambda>n::nat. ereal (real n)"]
    by (auto simp: top_ereal_def)
qed

lemma ereal_le_Sup:
  fixes x :: ereal
  shows "(x <= (SUP i:A. f i)) <-> (ALL y. y < x --> (EX i. i : A & y <= f i))"
(is "?lhs <-> ?rhs")
proof-
{ assume "?rhs"
  { assume "~(x <= (SUP i:A. f i))" hence "(SUP i:A. f i)<x" by (simp add: not_le)
    from this obtain y where y_def: "(SUP i:A. f i)<y & y<x" using ereal_dense by auto
    from this obtain i where "i : A & y <= f i" using `?rhs` by auto
    hence "y <= (SUP i:A. f i)" using SUP_upper[of i A f] by auto
    hence False using y_def by auto
  } hence "?lhs" by auto
}
moreover
{ assume "?lhs" hence "?rhs"
  by (metis less_SUP_iff order_less_imp_le order_less_le_trans)
} ultimately show ?thesis by auto
qed

lemma ereal_Inf_le:
  fixes x :: ereal
  shows "((INF i:A. f i) <= x) <-> (ALL y. x < y --> (EX i. i : A & f i <= y))"
(is "?lhs <-> ?rhs")
proof-
{ assume "?rhs"
  { assume "~((INF i:A. f i) <= x)" hence "x < (INF i:A. f i)" by (simp add: not_le)
    from this obtain y where y_def: "x<y & y<(INF i:A. f i)" using ereal_dense by auto
    from this obtain i where "i : A & f i <= y" using `?rhs` by auto
    hence "(INF i:A. f i) <= y" using INF_lower[of i A f] by auto
    hence False using y_def by auto
  } hence "?lhs" by auto
}
moreover
{ assume "?lhs" hence "?rhs"
  by (metis INF_less_iff order_le_less order_less_le_trans)
} ultimately show ?thesis by auto
qed

lemma Inf_less:
  fixes x :: ereal
  assumes "(INF i:A. f i) < x"
  shows "EX i. i : A & f i <= x"
proof(rule ccontr)
  assume "~ (EX i. i : A & f i <= x)"
  hence "ALL i:A. f i > x" by auto
  hence "(INF i:A. f i) >= x" apply (subst INF_greatest) by auto
  thus False using assms by auto
qed

lemma same_INF:
  assumes "ALL e:A. f e = g e"
  shows "(INF e:A. f e) = (INF e:A. g e)"
proof-
have "f ` A = g ` A" unfolding image_def using assms by auto
thus ?thesis unfolding INF_def by auto
qed

lemma same_SUP:
  assumes "ALL e:A. f e = g e"
  shows "(SUP e:A. f e) = (SUP e:A. g e)"
proof-
have "f ` A = g ` A" unfolding image_def using assms by auto
thus ?thesis unfolding SUP_def by auto
qed

lemma SUPR_eq:
  assumes "\<forall>i\<in>A. \<exists>j\<in>B. f i \<le> g j"
  assumes "\<forall>j\<in>B. \<exists>i\<in>A. g j \<le> f i"
  shows "(SUP i:A. f i) = (SUP j:B. g j)"
proof (intro antisym)
  show "(SUP i:A. f i) \<le> (SUP j:B. g j)"
    using assms by (metis SUP_least SUP_upper2)
  show "(SUP i:B. g i) \<le> (SUP j:A. f j)"
    using assms by (metis SUP_least SUP_upper2)
qed

lemma SUP_ereal_le_addI:
  fixes f :: "'i \<Rightarrow> ereal"
  assumes "\<And>i. f i + y \<le> z" and "y \<noteq> -\<infinity>"
  shows "SUPR UNIV f + y \<le> z"
proof (cases y)
  case (real r)
  then have "\<And>i. f i \<le> z - y" using assms by (simp add: ereal_le_minus_iff)
  then have "SUPR UNIV f \<le> z - y" by (rule SUP_least)
  then show ?thesis using real by (simp add: ereal_le_minus_iff)
qed (insert assms, auto)

lemma SUPR_ereal_add:
  fixes f g :: "nat \<Rightarrow> ereal"
  assumes "incseq f" "incseq g" and pos: "\<And>i. f i \<noteq> -\<infinity>" "\<And>i. g i \<noteq> -\<infinity>"
  shows "(SUP i. f i + g i) = SUPR UNIV f + SUPR UNIV g"
proof (rule ereal_SUPI)
  fix y assume *: "\<And>i. i \<in> UNIV \<Longrightarrow> f i + g i \<le> y"
  have f: "SUPR UNIV f \<noteq> -\<infinity>" using pos
    unfolding SUP_def Sup_eq_MInfty by (auto dest: image_eqD)
  { fix j
    { fix i
      have "f i + g j \<le> f i + g (max i j)"
        using `incseq g`[THEN incseqD] by (rule add_left_mono) auto
      also have "\<dots> \<le> f (max i j) + g (max i j)"
        using `incseq f`[THEN incseqD] by (rule add_right_mono) auto
      also have "\<dots> \<le> y" using * by auto
      finally have "f i + g j \<le> y" . }
    then have "SUPR UNIV f + g j \<le> y"
      using assms(4)[of j] by (intro SUP_ereal_le_addI) auto
    then have "g j + SUPR UNIV f \<le> y" by (simp add: ac_simps) }
  then have "SUPR UNIV g + SUPR UNIV f \<le> y"
    using f by (rule SUP_ereal_le_addI)
  then show "SUPR UNIV f + SUPR UNIV g \<le> y" by (simp add: ac_simps)
qed (auto intro!: add_mono SUP_upper)

lemma SUPR_ereal_add_pos:
  fixes f g :: "nat \<Rightarrow> ereal"
  assumes inc: "incseq f" "incseq g" and pos: "\<And>i. 0 \<le> f i" "\<And>i. 0 \<le> g i"
  shows "(SUP i. f i + g i) = SUPR UNIV f + SUPR UNIV g"
proof (intro SUPR_ereal_add inc)
  fix i show "f i \<noteq> -\<infinity>" "g i \<noteq> -\<infinity>" using pos[of i] by auto
qed

lemma SUPR_ereal_setsum:
  fixes f g :: "'a \<Rightarrow> nat \<Rightarrow> ereal"
  assumes "\<And>n. n \<in> A \<Longrightarrow> incseq (f n)" and pos: "\<And>n i. n \<in> A \<Longrightarrow> 0 \<le> f n i"
  shows "(SUP i. \<Sum>n\<in>A. f n i) = (\<Sum>n\<in>A. SUPR UNIV (f n))"
proof cases
  assume "finite A" then show ?thesis using assms
    by induct (auto simp: incseq_setsumI2 setsum_nonneg SUPR_ereal_add_pos)
qed simp

lemma SUPR_ereal_cmult:
  fixes f :: "nat \<Rightarrow> ereal" assumes "\<And>i. 0 \<le> f i" "0 \<le> c"
  shows "(SUP i. c * f i) = c * SUPR UNIV f"
proof (rule ereal_SUPI)
  fix i have "f i \<le> SUPR UNIV f" by (rule SUP_upper) auto
  then show "c * f i \<le> c * SUPR UNIV f"
    using `0 \<le> c` by (rule ereal_mult_left_mono)
next
  fix y assume *: "\<And>i. i \<in> UNIV \<Longrightarrow> c * f i \<le> y"
  show "c * SUPR UNIV f \<le> y"
  proof cases
    assume c: "0 < c \<and> c \<noteq> \<infinity>"
    with * have "SUPR UNIV f \<le> y / c"
      by (intro SUP_least) (auto simp: ereal_le_divide_pos)
    with c show ?thesis
      by (auto simp: ereal_le_divide_pos)
  next
    { assume "c = \<infinity>" have ?thesis
      proof cases
        assume "\<forall>i. f i = 0"
        moreover then have "range f = {0}" by auto
        ultimately show "c * SUPR UNIV f \<le> y" using *
          by (auto simp: SUP_def min_max.sup_absorb1)
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
  fixes f :: "'a \<Rightarrow> ereal"
  assumes "\<And>n::nat. \<exists>i\<in>A. ereal (real n) \<le> f i"
  shows "(SUP i:A. f i) = \<infinity>"
  unfolding SUP_def Sup_eq_top_iff[where 'a=ereal, unfolded top_ereal_def]
  apply simp
proof safe
  fix x :: ereal assume "x \<noteq> \<infinity>"
  show "\<exists>i\<in>A. x < f i"
  proof (cases x)
    case PInf with `x \<noteq> \<infinity>` show ?thesis by simp
  next
    case MInf with assms[of "0"] show ?thesis by force
  next
    case (real r)
    with less_PInf_Ex_of_nat[of x] obtain n :: nat where "x < ereal (real n)" by auto
    moreover from assms[of n] guess i ..
    ultimately show ?thesis
      by (auto intro!: bexI[of _ i])
  qed
qed

lemma Sup_countable_SUPR:
  assumes "A \<noteq> {}"
  shows "\<exists>f::nat \<Rightarrow> ereal. range f \<subseteq> A \<and> Sup A = SUPR UNIV f"
proof (cases "Sup A")
  case (real r)
  have "\<forall>n::nat. \<exists>x. x \<in> A \<and> Sup A < x + 1 / ereal (real n)"
  proof
    fix n ::nat have "\<exists>x\<in>A. Sup A - 1 / ereal (real n) < x"
      using assms real by (intro Sup_ereal_close) (auto simp: one_ereal_def)
    then guess x ..
    then show "\<exists>x. x \<in> A \<and> Sup A < x + 1 / ereal (real n)"
      by (auto intro!: exI[of _ x] simp: ereal_minus_less_iff)
  qed
  from choice[OF this] guess f .. note f = this
  have "SUPR UNIV f = Sup A"
  proof (rule ereal_SUPI)
    fix i show "f i \<le> Sup A" using f
      by (auto intro!: complete_lattice_class.Sup_upper)
  next
    fix y assume bound: "\<And>i. i \<in> UNIV \<Longrightarrow> f i \<le> y"
    show "Sup A \<le> y"
    proof (rule ereal_le_epsilon, intro allI impI)
      fix e :: ereal assume "0 < e"
      show "Sup A \<le> y + e"
      proof (cases e)
        case (real r)
        hence "0 < r" using `0 < e` by auto
        then obtain n ::nat where *: "1 / real n < r" "0 < n"
          using ex_inverse_of_nat_less by (auto simp: real_eq_of_nat inverse_eq_divide)
        have "Sup A \<le> f n + 1 / ereal (real n)" using f[THEN spec, of n]
          by auto
        also have "1 / ereal (real n) \<le> e" using real * by (auto simp: one_ereal_def )
        with bound have "f n + 1 / ereal (real n) \<le> y + e" by (rule add_mono) simp
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
      by (metis Infty_neq_0 PInf complete_lattice_class.Sup_least ereal_infty_less_eq2 linorder_linear)
    then obtain x where "x \<in> A" "0 \<le> x" by auto
    have "\<forall>n::nat. \<exists>f. f \<in> A \<and> x + ereal (real n) \<le> f"
    proof (rule ccontr)
      assume "\<not> ?thesis"
      then have "\<exists>n::nat. Sup A \<le> x + ereal (real n)"
        by (simp add: Sup_le_iff not_le less_imp_le Ball_def) (metis less_imp_le)
      then show False using `x \<in> A` `\<infinity> \<notin> A` PInf
        by(cases x) auto
    qed
    from choice[OF this] guess f .. note f = this
    have "SUPR UNIV f = \<infinity>"
    proof (rule SUP_PInfty)
      fix n :: nat show "\<exists>i\<in>UNIV. ereal (real n) \<le> f i"
        using f[THEN spec, of n] `0 \<le> x`
        by (cases rule: ereal2_cases[of "f n" x]) (auto intro!: exI[of _ n])
    qed
    then show ?thesis using f PInf by (auto intro!: exI[of _ f])
  qed
next
  case MInf
  with `A \<noteq> {}` have "A = {-\<infinity>}" by (auto simp: Sup_eq_MInfty)
  then show ?thesis using MInf by (auto intro!: exI[of _ "\<lambda>x. -\<infinity>"])
qed

lemma SUPR_countable_SUPR:
  "A \<noteq> {} \<Longrightarrow> \<exists>f::nat \<Rightarrow> ereal. range f \<subseteq> g`A \<and> SUPR A g = SUPR UNIV f"
  using Sup_countable_SUPR[of "g`A"] by (auto simp: SUP_def)

lemma Sup_ereal_cadd:
  fixes A :: "ereal set" assumes "A \<noteq> {}" and "a \<noteq> -\<infinity>"
  shows "Sup ((\<lambda>x. a + x) ` A) = a + Sup A"
proof (rule antisym)
  have *: "\<And>a::ereal. \<And>A. Sup ((\<lambda>x. a + x) ` A) \<le> a + Sup A"
    by (auto intro!: add_mono complete_lattice_class.Sup_least complete_lattice_class.Sup_upper)
  then show "Sup ((\<lambda>x. a + x) ` A) \<le> a + Sup A" .
  show "a + Sup A \<le> Sup ((\<lambda>x. a + x) ` A)"
  proof (cases a)
    case PInf with `A \<noteq> {}` show ?thesis by (auto simp: image_constant min_max.sup_absorb1)
  next
    case (real r)
    then have **: "op + (- a) ` op + a ` A = A"
      by (auto simp: image_iff ac_simps zero_ereal_def[symmetric])
    from *[of "-a" "(\<lambda>x. a + x) ` A"] real show ?thesis unfolding **
      by (cases rule: ereal2_cases[of "Sup A" "Sup (op + a ` A)"]) auto
  qed (insert `a \<noteq> -\<infinity>`, auto)
qed

lemma Sup_ereal_cminus:
  fixes A :: "ereal set" assumes "A \<noteq> {}" and "a \<noteq> -\<infinity>"
  shows "Sup ((\<lambda>x. a - x) ` A) = a - Inf A"
  using Sup_ereal_cadd[of "uminus ` A" a] assms
  by (simp add: comp_def image_image minus_ereal_def
                 ereal_Sup_uminus_image_eq)

lemma SUPR_ereal_cminus:
  fixes f :: "'i \<Rightarrow> ereal"
  fixes A assumes "A \<noteq> {}" and "a \<noteq> -\<infinity>"
  shows "(SUP x:A. a - f x) = a - (INF x:A. f x)"
  using Sup_ereal_cminus[of "f`A" a] assms
  unfolding SUP_def INF_def image_image by auto

lemma Inf_ereal_cminus:
  fixes A :: "ereal set" assumes "A \<noteq> {}" and "\<bar>a\<bar> \<noteq> \<infinity>"
  shows "Inf ((\<lambda>x. a - x) ` A) = a - Sup A"
proof -
  { fix x have "-a - -x = -(a - x)" using assms by (cases x) auto }
  moreover then have "(\<lambda>x. -a - x)`uminus`A = uminus ` (\<lambda>x. a - x) ` A"
    by (auto simp: image_image)
  ultimately show ?thesis
    using Sup_ereal_cminus[of "uminus ` A" "-a"] assms
    by (auto simp add: ereal_Sup_uminus_image_eq ereal_Inf_uminus_image_eq)
qed

lemma INFI_ereal_cminus:
  fixes a :: ereal assumes "A \<noteq> {}" and "\<bar>a\<bar> \<noteq> \<infinity>"
  shows "(INF x:A. a - f x) = a - (SUP x:A. f x)"
  using Inf_ereal_cminus[of "f`A" a] assms
  unfolding SUP_def INF_def image_image
  by auto

lemma uminus_ereal_add_uminus_uminus:
  fixes a b :: ereal shows "a \<noteq> \<infinity> \<Longrightarrow> b \<noteq> \<infinity> \<Longrightarrow> - (- a + - b) = a + b"
  by (cases rule: ereal2_cases[of a b]) auto

lemma INFI_ereal_add:
  fixes f :: "nat \<Rightarrow> ereal"
  assumes "decseq f" "decseq g" and fin: "\<And>i. f i \<noteq> \<infinity>" "\<And>i. g i \<noteq> \<infinity>"
  shows "(INF i. f i + g i) = INFI UNIV f + INFI UNIV g"
proof -
  have INF_less: "(INF i. f i) < \<infinity>" "(INF i. g i) < \<infinity>"
    using assms unfolding INF_less_iff by auto
  { fix i from fin[of i] have "- ((- f i) + (- g i)) = f i + g i"
      by (rule uminus_ereal_add_uminus_uminus) }
  then have "(INF i. f i + g i) = (INF i. - ((- f i) + (- g i)))"
    by simp
  also have "\<dots> = INFI UNIV f + INFI UNIV g"
    unfolding ereal_INFI_uminus
    using assms INF_less
    by (subst SUPR_ereal_add)
       (auto simp: ereal_SUPR_uminus intro!: uminus_ereal_add_uminus_uminus)
  finally show ?thesis .
qed

subsection "Limits on @{typ ereal}"

subsubsection "Topological space"

instantiation ereal :: topological_space
begin

definition "open A \<longleftrightarrow> open (ereal -` A)
       \<and> (\<infinity> \<in> A \<longrightarrow> (\<exists>x. {ereal x <..} \<subseteq> A))
       \<and> (-\<infinity> \<in> A \<longrightarrow> (\<exists>x. {..<ereal x} \<subseteq> A))"

lemma open_PInfty: "open A \<Longrightarrow> \<infinity> \<in> A \<Longrightarrow> (\<exists>x. {ereal x<..} \<subseteq> A)"
  unfolding open_ereal_def by auto

lemma open_MInfty: "open A \<Longrightarrow> -\<infinity> \<in> A \<Longrightarrow> (\<exists>x. {..<ereal x} \<subseteq> A)"
  unfolding open_ereal_def by auto

lemma open_PInfty2: assumes "open A" "\<infinity> \<in> A" obtains x where "{ereal x<..} \<subseteq> A"
  using open_PInfty[OF assms] by auto

lemma open_MInfty2: assumes "open A" "-\<infinity> \<in> A" obtains x where "{..<ereal x} \<subseteq> A"
  using open_MInfty[OF assms] by auto

lemma ereal_openE: assumes "open A" obtains x y where
  "open (ereal -` A)"
  "\<infinity> \<in> A \<Longrightarrow> {ereal x<..} \<subseteq> A"
  "-\<infinity> \<in> A \<Longrightarrow> {..<ereal y} \<subseteq> A"
  using assms open_ereal_def by auto

instance
proof
  let ?U = "UNIV::ereal set"
  show "open ?U" unfolding open_ereal_def
    by (auto intro!: exI[of _ 0])
next
  fix S T::"ereal set" assume "open S" and "open T"
  from `open S`[THEN ereal_openE] guess xS yS .
  moreover from `open T`[THEN ereal_openE] guess xT yT .
  ultimately have
    "open (ereal -` (S \<inter> T))"
    "\<infinity> \<in> S \<inter> T \<Longrightarrow> {ereal (max xS xT) <..} \<subseteq> S \<inter> T"
    "-\<infinity> \<in> S \<inter> T \<Longrightarrow> {..< ereal (min yS yT)} \<subseteq> S \<inter> T"
    by auto
  then show "open (S Int T)" unfolding open_ereal_def by blast
next
  fix K :: "ereal set set" assume "\<forall>S\<in>K. open S"
  then have *: "\<forall>S. \<exists>x y. S \<in> K \<longrightarrow> open (ereal -` S) \<and>
    (\<infinity> \<in> S \<longrightarrow> {ereal x <..} \<subseteq> S) \<and> (-\<infinity> \<in> S \<longrightarrow> {..< ereal y} \<subseteq> S)"
    by (auto simp: open_ereal_def)
  then show "open (Union K)" unfolding open_ereal_def
  proof (intro conjI impI)
    show "open (ereal -` \<Union>K)"
      using *[THEN choice] by (auto simp: vimage_Union)
  qed ((metis UnionE Union_upper subset_trans *)+)
qed
end

lemma open_ereal: "open S \<Longrightarrow> open (ereal ` S)"
  by (auto simp: inj_vimage_image_eq open_ereal_def)

lemma open_ereal_vimage: "open S \<Longrightarrow> open (ereal -` S)"
  unfolding open_ereal_def by auto

lemma open_ereal_lessThan[intro, simp]: "open {..< a :: ereal}"
proof -
  have "\<And>x. ereal -` {..<ereal x} = {..< x}"
    "ereal -` {..< \<infinity>} = UNIV" "ereal -` {..< -\<infinity>} = {}" by auto
  then show ?thesis by (cases a) (auto simp: open_ereal_def)
qed

lemma open_ereal_greaterThan[intro, simp]:
  "open {a :: ereal <..}"
proof -
  have "\<And>x. ereal -` {ereal x<..} = {x<..}"
    "ereal -` {\<infinity><..} = {}" "ereal -` {-\<infinity><..} = UNIV" by auto
  then show ?thesis by (cases a) (auto simp: open_ereal_def)
qed

lemma ereal_open_greaterThanLessThan[intro, simp]: "open {a::ereal <..< b}"
  unfolding greaterThanLessThan_def by auto

lemma closed_ereal_atLeast[simp, intro]: "closed {a :: ereal ..}"
proof -
  have "- {a ..} = {..< a}" by auto
  then show "closed {a ..}"
    unfolding closed_def using open_ereal_lessThan by auto
qed

lemma closed_ereal_atMost[simp, intro]: "closed {.. b :: ereal}"
proof -
  have "- {.. b} = {b <..}" by auto
  then show "closed {.. b}"
    unfolding closed_def using open_ereal_greaterThan by auto
qed

lemma closed_ereal_atLeastAtMost[simp, intro]:
  shows "closed {a :: ereal .. b}"
  unfolding atLeastAtMost_def by auto

lemma closed_ereal_singleton:
  "closed {a :: ereal}"
by (metis atLeastAtMost_singleton closed_ereal_atLeastAtMost)

lemma ereal_open_cont_interval:
  fixes S :: "ereal set"
  assumes "open S" "x \<in> S" "\<bar>x\<bar> \<noteq> \<infinity>"
  obtains e where "e>0" "{x-e <..< x+e} \<subseteq> S"
proof-
  from `open S` have "open (ereal -` S)" by (rule ereal_openE)
  then obtain e where "0 < e" and e: "\<And>y. dist y (real x) < e \<Longrightarrow> ereal y \<in> S"
    using assms unfolding open_dist by force
  show thesis
  proof (intro that subsetI)
    show "0 < ereal e" using `0 < e` by auto
    fix y assume "y \<in> {x - ereal e<..<x + ereal e}"
    with assms obtain t where "y = ereal t" "dist t (real x) < e"
      apply (cases y) by (auto simp: dist_real_def)
    then show "y \<in> S" using e[of t] by auto
  qed
qed

lemma ereal_open_cont_interval2:
  fixes S :: "ereal set"
  assumes "open S" "x \<in> S" and x: "\<bar>x\<bar> \<noteq> \<infinity>"
  obtains a b where "a < x" "x < b" "{a <..< b} \<subseteq> S"
proof-
  guess e using ereal_open_cont_interval[OF assms] .
  with that[of "x-e" "x+e"] ereal_between[OF x, of e]
  show thesis by auto
qed

instance ereal :: t2_space
proof
  fix x y :: ereal assume "x ~= y"
  let "?P x (y::ereal)" = "EX U V. open U & open V & x : U & y : V & U Int V = {}"

  { fix x y :: ereal assume "x < y"
    from ereal_dense[OF this] obtain z where z: "x < z" "z < y" by auto
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

lemma lim_ereal[simp]:
  "((\<lambda>n. ereal (f n)) ---> ereal x) net \<longleftrightarrow> (f ---> x) net" (is "?l = ?r")
proof (intro iffI topological_tendstoI)
  fix S assume "?l" "open S" "x \<in> S"
  then show "eventually (\<lambda>x. f x \<in> S) net"
    using `?l`[THEN topological_tendstoD, OF open_ereal, OF `open S`]
    by (simp add: inj_image_mem_iff)
next
  fix S assume "?r" "open S" "ereal x \<in> S"
  show "eventually (\<lambda>x. ereal (f x) \<in> S) net"
    using `?r`[THEN topological_tendstoD, OF open_ereal_vimage, OF `open S`]
    using `ereal x \<in> S` by auto
qed

lemma lim_real_of_ereal[simp]:
  assumes lim: "(f ---> ereal x) net"
  shows "((\<lambda>x. real (f x)) ---> x) net"
proof (intro topological_tendstoI)
  fix S assume "open S" "x \<in> S"
  then have S: "open S" "ereal x \<in> ereal ` S"
    by (simp_all add: inj_image_mem_iff)
  have "\<forall>x. f x \<in> ereal ` S \<longrightarrow> real (f x) \<in> S" by auto
  from this lim[THEN topological_tendstoD, OF open_ereal, OF S]
  show "eventually (\<lambda>x. real (f x) \<in> S) net"
    by (rule eventually_mono)
qed

lemma Lim_PInfty: "f ----> \<infinity> <-> (ALL B. EX N. ALL n>=N. f n >= ereal B)" (is "?l = ?r")
proof
  assume ?r
  show ?l
    apply(rule topological_tendstoI)
    unfolding eventually_sequentially
  proof-
    fix S :: "ereal set" assume "open S" "\<infinity> : S"
    from open_PInfty[OF this] guess B .. note B=this
    from `?r`[rule_format,of "B+1"] guess N .. note N=this
    show "EX N. ALL n>=N. f n : S" apply(rule_tac x=N in exI)
    proof safe case goal1
      have "ereal B < ereal (B + 1)" by auto
      also have "... <= f n" using goal1 N by auto
      finally show ?case using B by fastforce
    qed
  qed
next
  assume ?l
  show ?r
  proof fix B::real have "open {ereal B<..}" "\<infinity> : {ereal B<..}" by auto
    from topological_tendstoD[OF `?l` this,unfolded eventually_sequentially]
    guess N .. note N=this
    show "EX N. ALL n>=N. ereal B <= f n" apply(rule_tac x=N in exI) using N by auto
  qed
qed


lemma Lim_MInfty: "f ----> (-\<infinity>) <-> (ALL B. EX N. ALL n>=N. f n <= ereal B)" (is "?l = ?r")
proof
  assume ?r
  show ?l
    apply(rule topological_tendstoI)
    unfolding eventually_sequentially
  proof-
    fix S :: "ereal set"
    assume "open S" "(-\<infinity>) : S"
    from open_MInfty[OF this] guess B .. note B=this
    from `?r`[rule_format,of "B-(1::real)"] guess N .. note N=this
    show "EX N. ALL n>=N. f n : S" apply(rule_tac x=N in exI)
    proof safe case goal1
      have "ereal (B - 1) >= f n" using goal1 N by auto
      also have "... < ereal B" by auto
      finally show ?case using B by fastforce
    qed
  qed
next assume ?l show ?r
  proof fix B::real have "open {..<ereal B}" "(-\<infinity>) : {..<ereal B}" by auto
    from topological_tendstoD[OF `?l` this,unfolded eventually_sequentially]
    guess N .. note N=this
    show "EX N. ALL n>=N. ereal B >= f n" apply(rule_tac x=N in exI) using N by auto
  qed
qed


lemma Lim_bounded_PInfty: assumes lim:"f ----> l" and "!!n. f n <= ereal B" shows "l ~= \<infinity>"
proof(rule ccontr,unfold not_not) let ?B = "B + 1" assume as:"l=\<infinity>"
  from lim[unfolded this Lim_PInfty,rule_format,of "?B"]
  guess N .. note N=this[rule_format,OF le_refl]
  hence "ereal ?B <= ereal B" using assms(2)[of N] by(rule order_trans)
  hence "ereal ?B < ereal ?B" apply (rule le_less_trans) by auto
  thus False by auto
qed


lemma Lim_bounded_MInfty: assumes lim:"f ----> l" and "!!n. f n >= ereal B" shows "l ~= (-\<infinity>)"
proof(rule ccontr,unfold not_not) let ?B = "B - 1" assume as:"l=(-\<infinity>)"
  from lim[unfolded this Lim_MInfty,rule_format,of "?B"]
  guess N .. note N=this[rule_format,OF le_refl]
  hence "ereal B <= ereal ?B" using assms(2)[of N] order_trans[of "ereal B" "f N" "ereal(B - 1)"] by blast
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
assumes lim:"f ----> l" and "ALL n>=N. f n <= ereal B"
shows "l ~= \<infinity>"
proof-
  def g == "(%n. if n>=N then f n else ereal B)"
  hence "g ----> l" using tail_same_limit[of f l N g] lim by auto
  moreover have "!!n. g n <= ereal B" using g_def assms by auto
  ultimately show ?thesis using  Lim_bounded_PInfty by auto
qed

lemma Lim_bounded_ereal:
  assumes lim:"f ----> (l :: ereal)"
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
  { assume "EX B. C = ereal B"
    from this obtain B where B_def: "C=ereal B" by auto
    hence "~(l=\<infinity>)" using Lim_bounded_PInfty2 assms by auto
    from this obtain m where m_def: "ereal m=l" using `~(l=(-\<infinity>))` by (cases l) auto
    from this obtain N where N_def: "ALL n>=N. f n : {ereal(m - 1) <..< ereal(m+1)}"
       apply (subst tendsto_obtains_N[of f l "{ereal(m - 1) <..< ereal(m+1)}"]) using assms by auto
    { fix n assume "n>=N"
      hence "EX r. ereal r = f n" using N_def by (cases "f n") auto
    } from this obtain g where g_def: "ALL n>=N. ereal (g n) = f n" by metis
    hence "(%n. ereal (g n)) ----> l" using tail_same_limit[of f l N] assms by auto
    hence *: "(%n. g n) ----> m" using m_def by auto
    { fix n assume "n>=max N M"
      hence "ereal (g n) <= ereal B" using assms g_def B_def by auto
      hence "g n <= B" by auto
    } hence "EX N. ALL n>=N. g n <= B" by blast
    hence "m<=B" using * LIMSEQ_le_const2[of g m B] by auto
    hence ?thesis using m_def B_def by auto
  } ultimately have ?thesis by (cases C) auto
} ultimately show ?thesis by blast
qed

lemma real_of_ereal_mult[simp]:
  fixes a b :: ereal shows "real (a * b) = real a * real b"
  by (cases rule: ereal2_cases[of a b]) auto

lemma real_of_ereal_eq_0:
  fixes x :: ereal shows "real x = 0 \<longleftrightarrow> x = \<infinity> \<or> x = -\<infinity> \<or> x = 0"
  by (cases x) auto

lemma tendsto_ereal_realD:
  fixes f :: "'a \<Rightarrow> ereal"
  assumes "x \<noteq> 0" and tendsto: "((\<lambda>x. ereal (real (f x))) ---> x) net"
  shows "(f ---> x) net"
proof (intro topological_tendstoI)
  fix S assume S: "open S" "x \<in> S"
  with `x \<noteq> 0` have "open (S - {0})" "x \<in> S - {0}" by auto
  from tendsto[THEN topological_tendstoD, OF this]
  show "eventually (\<lambda>x. f x \<in> S) net"
    by (rule eventually_rev_mp) (auto simp: ereal_real)
qed

lemma tendsto_ereal_realI:
  fixes f :: "'a \<Rightarrow> ereal"
  assumes x: "\<bar>x\<bar> \<noteq> \<infinity>" and tendsto: "(f ---> x) net"
  shows "((\<lambda>x. ereal (real (f x))) ---> x) net"
proof (intro topological_tendstoI)
  fix S assume "open S" "x \<in> S"
  with x have "open (S - {\<infinity>, -\<infinity>})" "x \<in> S - {\<infinity>, -\<infinity>}" by auto
  from tendsto[THEN topological_tendstoD, OF this]
  show "eventually (\<lambda>x. ereal (real (f x)) \<in> S) net"
    by (elim eventually_elim1) (auto simp: ereal_real)
qed

lemma ereal_mult_cancel_left:
  fixes a b c :: ereal shows "a * b = a * c \<longleftrightarrow>
    ((\<bar>a\<bar> = \<infinity> \<and> 0 < b * c) \<or> a = 0 \<or> b = c)"
  by (cases rule: ereal3_cases[of a b c])
     (simp_all add: zero_less_mult_iff)

lemma ereal_inj_affinity:
  fixes m t :: ereal
  assumes "\<bar>m\<bar> \<noteq> \<infinity>" "m \<noteq> 0" "\<bar>t\<bar> \<noteq> \<infinity>"
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

lemma ereal_LimI_finite:
  fixes x :: ereal
  assumes "\<bar>x\<bar> \<noteq> \<infinity>"
  assumes "!!r. 0 < r ==> EX N. ALL n>=N. u n < x + r & x < u n + r"
  shows "u ----> x"
proof (rule topological_tendstoI, unfold eventually_sequentially)
  obtain rx where rx_def: "x=ereal rx" using assms by (cases x) auto
  fix S assume "open S" "x : S"
  then have "open (ereal -` S)" unfolding open_ereal_def by auto
  with `x \<in> S` obtain r where "0 < r" and dist: "!!y. dist y rx < r ==> ereal y \<in> S"
    unfolding open_real_def rx_def by auto
  then obtain n where
    upper: "!!N. n <= N ==> u N < x + ereal r" and
    lower: "!!N. n <= N ==> x < u N + ereal r" using assms(2)[of "ereal r"] by auto
  show "EX N. ALL n>=N. u n : S"
  proof (safe intro!: exI[of _ n])
    fix N assume "n <= N"
    from upper[OF this] lower[OF this] assms `0 < r`
    have "u N ~: {\<infinity>,(-\<infinity>)}" by auto
    from this obtain ra where ra_def: "(u N) = ereal ra" by (cases "u N") auto
    hence "rx < ra + r" and "ra < rx + r"
       using rx_def assms `0 < r` lower[OF `n <= N`] upper[OF `n <= N`] by auto
    hence "dist (real (u N)) rx < r"
      using rx_def ra_def
      by (auto simp: dist_real_def abs_diff_less_iff field_simps)
    from dist[OF this] show "u N : S" using `u N  ~: {\<infinity>, -\<infinity>}`
      by (auto simp: ereal_real split: split_if_asm)
  qed
qed

lemma ereal_LimI_finite_iff:
  fixes x :: ereal
  assumes "\<bar>x\<bar> \<noteq> \<infinity>"
  shows "u ----> x <-> (ALL r. 0 < r --> (EX N. ALL n>=N. u n < x + r & x < u n + r))"
  (is "?lhs <-> ?rhs")
proof
  assume lim: "u ----> x"
  { fix r assume "(r::ereal)>0"
    from this obtain N where N_def: "ALL n>=N. u n : {x - r <..< x + r}"
       apply (subst tendsto_obtains_N[of u x "{x - r <..< x + r}"])
       using lim ereal_between[of x r] assms `r>0` by auto
    hence "EX N. ALL n>=N. u n < x + r & x < u n + r"
      using ereal_minus_less[of r x] by (cases r) auto
  } then show "?rhs" by auto
next
  assume ?rhs then show "u ----> x"
    using ereal_LimI_finite[of x] assms by auto
qed


subsubsection {* @{text Liminf} and @{text Limsup} *}

definition
  "Liminf net f = (GREATEST l. \<forall>y<l. eventually (\<lambda>x. y < f x) net)"

definition
  "Limsup net f = (LEAST l. \<forall>y>l. eventually (\<lambda>x. f x < y) net)"

lemma Liminf_Sup:
  fixes f :: "'a => 'b::complete_linorder"
  shows "Liminf net f = Sup {l. \<forall>y<l. eventually (\<lambda>x. y < f x) net}"
  by (auto intro!: Greatest_equality complete_lattice_class.Sup_upper simp: less_Sup_iff Liminf_def)

lemma Limsup_Inf:
  fixes f :: "'a => 'b::complete_linorder"
  shows "Limsup net f = Inf {l. \<forall>y>l. eventually (\<lambda>x. f x < y) net}"
  by (auto intro!: Least_equality complete_lattice_class.Inf_lower simp: Inf_less_iff Limsup_def)

lemma ereal_SupI:
  fixes x :: ereal
  assumes "\<And>y. y \<in> A \<Longrightarrow> y \<le> x"
  assumes "\<And>y. (\<And>z. z \<in> A \<Longrightarrow> z \<le> y) \<Longrightarrow> x \<le> y"
  shows "Sup A = x"
  unfolding Sup_ereal_def
  using assms by (auto intro!: Least_equality)

lemma ereal_InfI:
  fixes x :: ereal
  assumes "\<And>i. i \<in> A \<Longrightarrow> x \<le> i"
  assumes "\<And>y. (\<And>i. i \<in> A \<Longrightarrow> y \<le> i) \<Longrightarrow> y \<le> x"
  shows "Inf A = x"
  unfolding Inf_ereal_def
  using assms by (auto intro!: Greatest_equality)

lemma Limsup_const:
  fixes c :: "'a::complete_linorder"
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
  fixes c :: "'a::complete_linorder"
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

definition (in order) mono_set:
  "mono_set S \<longleftrightarrow> (\<forall>x y. x \<le> y \<longrightarrow> x \<in> S \<longrightarrow> y \<in> S)"

lemma (in order) mono_greaterThan [intro, simp]: "mono_set {B<..}" unfolding mono_set by auto
lemma (in order) mono_atLeast [intro, simp]: "mono_set {B..}" unfolding mono_set by auto
lemma (in order) mono_UNIV [intro, simp]: "mono_set UNIV" unfolding mono_set by auto
lemma (in order) mono_empty [intro, simp]: "mono_set {}" unfolding mono_set by auto

lemma (in complete_linorder) mono_set_iff:
  fixes S :: "'a set"
  defines "a \<equiv> Inf S"
  shows "mono_set S \<longleftrightarrow> (S = {a <..} \<or> S = {a..})" (is "_ = ?c")
proof
  assume "mono_set S"
  then have mono: "\<And>x y. x \<le> y \<Longrightarrow> x \<in> S \<Longrightarrow> y \<in> S" by (auto simp: mono_set)
  show ?c
  proof cases
    assume "a \<in> S"
    show ?c
      using mono[OF _ `a \<in> S`]
      by (auto intro: Inf_lower simp: a_def)
  next
    assume "a \<notin> S"
    have "S = {a <..}"
    proof safe
      fix x assume "x \<in> S"
      then have "a \<le> x" unfolding a_def by (rule Inf_lower)
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
  fixes f :: "'a \<Rightarrow> ereal"
  assumes ntriv: "\<not> trivial_limit net"
  assumes lim: "(f ---> f0) net"
  shows "Liminf net f = f0"
  unfolding Liminf_Sup
proof (safe intro!: ereal_SupI)
  fix y assume *: "\<forall>y'<y. eventually (\<lambda>x. y' < f x) net"
  show "y \<le> f0"
  proof (rule ereal_le_ereal)
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

lemma ereal_Liminf_le_Limsup:
  fixes f :: "'a \<Rightarrow> ereal"
  assumes ntriv: "\<not> trivial_limit net"
  shows "Liminf net f \<le> Limsup net f"
  unfolding Limsup_Inf Liminf_Sup
proof (safe intro!: complete_lattice_class.Inf_greatest  complete_lattice_class.Sup_least)
  fix u v assume *: "\<forall>y<u. eventually (\<lambda>x. y < f x) net" "\<forall>y>v. eventually (\<lambda>x. f x < y) net"
  show "u \<le> v"
  proof (rule ccontr)
    assume "\<not> u \<le> v"
    then obtain t where "t < u" "v < t"
      using ereal_dense[of v u] by (auto simp: not_le)
    then have "eventually (\<lambda>x. t < f x \<and> f x < t) net"
      using * by (auto intro: eventually_conj)
    also have "(\<lambda>x. t < f x \<and> f x < t) = (\<lambda>x. False)" by (auto simp: fun_eq_iff)
    finally show False using ntriv by (auto simp: trivial_limit_def)
  qed
qed

lemma Liminf_mono:
  fixes f g :: "'a => ereal"
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
  fixes f g :: "'a \<Rightarrow> ereal"
  assumes "eventually (\<lambda>x. f x = g x) net"
  shows "Liminf net f = Liminf net g"
  by (intro antisym Liminf_mono eventually_mono[OF _ assms]) auto

lemma Liminf_mono_all:
  fixes f g :: "'a \<Rightarrow> ereal"
  assumes "\<And>x. f x \<le> g x"
  shows "Liminf net f \<le> Liminf net g"
  using assms by (intro Liminf_mono always_eventually) auto

lemma Limsup_mono:
  fixes f g :: "'a \<Rightarrow> ereal"
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
  fixes f g :: "'a \<Rightarrow> ereal"
  assumes "\<And>x. f x \<le> g x"
  shows "Limsup net f \<le> Limsup net g"
  using assms by (intro Limsup_mono always_eventually) auto

lemma Limsup_eq:
  fixes f g :: "'a \<Rightarrow> ereal"
  assumes "eventually (\<lambda>x. f x = g x) net"
  shows "Limsup net f = Limsup net g"
  by (intro antisym Limsup_mono eventually_mono[OF _ assms]) auto

abbreviation "liminf \<equiv> Liminf sequentially"

abbreviation "limsup \<equiv> Limsup sequentially"

lemma liminf_SUPR_INFI:
  fixes f :: "nat \<Rightarrow> ereal"
  shows "liminf f = (SUP n. INF m:{n..}. f m)"
  unfolding Liminf_Sup eventually_sequentially
proof (safe intro!: antisym complete_lattice_class.Sup_least)
  fix x assume *: "\<forall>y<x. \<exists>N. \<forall>n\<ge>N. y < f n" show "x \<le> (SUP n. INF m:{n..}. f m)"
  proof (rule ereal_le_ereal)
    fix y assume "y < x"
    with * obtain N where "\<And>n. N \<le> n \<Longrightarrow> y < f n" by auto
    then have "y \<le> (INF m:{N..}. f m)" by (force simp: le_INF_iff)
    also have "\<dots> \<le> (SUP n. INF m:{n..}. f m)" by (intro SUP_upper) auto
    finally show "y \<le> (SUP n. INF m:{n..}. f m)" .
  qed
next
  show "(SUP n. INF m:{n..}. f m) \<le> Sup {l. \<forall>y<l. \<exists>N. \<forall>n\<ge>N. y < f n}"
  proof (unfold SUP_def, safe intro!: Sup_mono bexI)
    fix y n assume "y < INFI {n..} f"
    from less_INF_D[OF this] show "\<exists>N. \<forall>n\<ge>N. y < f n" by (intro exI[of _ n]) auto
  qed (rule order_refl)
qed

lemma tail_same_limsup:
  fixes X Y :: "nat => ereal"
  assumes "\<And>n. N \<le> n \<Longrightarrow> X n = Y n"
  shows "limsup X = limsup Y"
  using Limsup_eq[of X Y sequentially] eventually_sequentially assms by auto

lemma tail_same_liminf:
  fixes X Y :: "nat => ereal"
  assumes "\<And>n. N \<le> n \<Longrightarrow> X n = Y n"
  shows "liminf X = liminf Y"
  using Liminf_eq[of X Y sequentially] eventually_sequentially assms by auto

lemma liminf_mono:
  fixes X Y :: "nat \<Rightarrow> ereal"
  assumes "\<And>n. N \<le> n \<Longrightarrow> X n <= Y n"
  shows "liminf X \<le> liminf Y"
  using Liminf_mono[of X Y sequentially] eventually_sequentially assms by auto

lemma limsup_mono:
  fixes X Y :: "nat => ereal"
  assumes "\<And>n. N \<le> n \<Longrightarrow> X n <= Y n"
  shows "limsup X \<le> limsup Y"
  using Limsup_mono[of X Y sequentially] eventually_sequentially assms by auto

lemma
  fixes X :: "nat \<Rightarrow> ereal"
  shows ereal_incseq_uminus[simp]: "incseq (\<lambda>i. - X i) = decseq X"
    and ereal_decseq_uminus[simp]: "decseq (\<lambda>i. - X i) = incseq X"
  unfolding incseq_def decseq_def by auto

lemma liminf_bounded:
  fixes X Y :: "nat \<Rightarrow> ereal"
  assumes "\<And>n. N \<le> n \<Longrightarrow> C \<le> X n"
  shows "C \<le> liminf X"
  using liminf_mono[of N "\<lambda>n. C" X] assms Liminf_const[of sequentially C] by simp

lemma limsup_bounded:
  fixes X Y :: "nat => ereal"
  assumes "\<And>n. N \<le> n \<Longrightarrow> X n <= C"
  shows "limsup X \<le> C"
  using limsup_mono[of N X "\<lambda>n. C"] assms Limsup_const[of sequentially C] by simp

lemma liminf_bounded_iff:
  fixes x :: "nat \<Rightarrow> ereal"
  shows "C \<le> liminf x \<longleftrightarrow> (\<forall>B<C. \<exists>N. \<forall>n\<ge>N. B < x n)" (is "?lhs <-> ?rhs")
proof safe
  fix B assume "B < C" "C \<le> liminf x"
  then have "B < liminf x" by auto
  then obtain N where "B < (INF m:{N..}. x m)"
    unfolding liminf_SUPR_INFI SUP_def less_Sup_iff by auto
  from less_INF_D[OF this] show "\<exists>N. \<forall>n\<ge>N. B < x n" by auto
next
  assume *: "\<forall>B<C. \<exists>N. \<forall>n\<ge>N. B < x n"
  { fix B assume "B<C"
    then obtain N where "\<forall>n\<ge>N. B < x n" using `?rhs` by auto
    hence "B \<le> (INF m:{N..}. x m)" by (intro INF_greatest) auto
    also have "... \<le> liminf x" unfolding liminf_SUPR_INFI by (intro SUP_upper) simp
    finally have "B \<le> liminf x" .
  } then show "?lhs" by (metis * leD liminf_bounded linorder_le_less_linear)
qed

lemma liminf_subseq_mono:
  fixes X :: "nat \<Rightarrow> ereal"
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

lemma ereal_real': assumes "\<bar>x\<bar> \<noteq> \<infinity>" shows "ereal (real x) = x"
  using assms by auto

lemma ereal_le_ereal_bounded:
  fixes x y z :: ereal
  assumes "z \<le> y"
  assumes *: "\<And>B. z < B \<Longrightarrow> B < x \<Longrightarrow> B \<le> y"
  shows "x \<le> y"
proof (rule ereal_le_ereal)
  fix B assume "B < x"
  show "B \<le> y"
  proof cases
    assume "z < B" from *[OF this `B < x`] show "B \<le> y" .
  next
    assume "\<not> z < B" with `z \<le> y` show "B \<le> y" by auto
  qed
qed

lemma fixes x y :: ereal
  shows Sup_atMost[simp]: "Sup {.. y} = y"
    and Sup_lessThan[simp]: "Sup {..< y} = y"
    and Sup_atLeastAtMost[simp]: "x \<le> y \<Longrightarrow> Sup { x .. y} = y"
    and Sup_greaterThanAtMost[simp]: "x < y \<Longrightarrow> Sup { x <.. y} = y"
    and Sup_atLeastLessThan[simp]: "x < y \<Longrightarrow> Sup { x ..< y} = y"
  by (auto simp: Sup_ereal_def intro!: Least_equality
           intro: ereal_le_ereal ereal_le_ereal_bounded[of x])

lemma Sup_greaterThanlessThan[simp]:
  fixes x y :: ereal assumes "x < y" shows "Sup { x <..< y} = y"
  unfolding Sup_ereal_def
proof (intro Least_equality ereal_le_ereal_bounded[of _ _ y])
  fix z assume z: "\<forall>u\<in>{x<..<y}. u \<le> z"
  from ereal_dense[OF `x < y`] guess w .. note w = this
  with z[THEN bspec, of w] show "x \<le> z" by auto
qed auto

lemma real_ereal_id: "real o ereal = id"
proof-
{ fix x have "(real o ereal) x = id x" by auto }
from this show ?thesis using ext by blast
qed

lemma open_image_ereal: "open(UNIV-{ \<infinity> , (-\<infinity> :: ereal)})"
by (metis range_ereal open_ereal open_UNIV)

lemma ereal_le_distrib:
  fixes a b c :: ereal shows "c * (a + b) \<le> c * a + c * b"
  by (cases rule: ereal3_cases[of a b c])
     (auto simp add: field_simps not_le mult_le_0_iff mult_less_0_iff)

lemma ereal_pos_distrib:
  fixes a b c :: ereal assumes "0 \<le> c" "c \<noteq> \<infinity>" shows "c * (a + b) = c * a + c * b"
  using assms by (cases rule: ereal3_cases[of a b c])
                 (auto simp add: field_simps not_le mult_le_0_iff mult_less_0_iff)

lemma ereal_pos_le_distrib:
fixes a b c :: ereal
assumes "c>=0"
shows "c * (a + b) <= c * a + c * b"
  using assms by (cases rule: ereal3_cases[of a b c])
                 (auto simp add: field_simps)

lemma ereal_max_mono:
  "[| (a::ereal) <= b; c <= d |] ==> max a c <= max b d"
  by (metis sup_ereal_def sup_mono)


lemma ereal_max_least:
  "[| (a::ereal) <= x; c <= x |] ==> max a c <= x"
  by (metis sup_ereal_def sup_least)

subsubsection {* Tests for code generator *}

(* A small list of simple arithmetic expressions *)

value [code] "- \<infinity> :: ereal"
value [code] "\<bar>-\<infinity>\<bar> :: ereal"
value [code] "4 + 5 / 4 - ereal 2 :: ereal"
value [code] "ereal 3 < \<infinity>"
value [code] "real (\<infinity>::ereal) = 0"

end
