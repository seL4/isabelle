 (* Title: Extended_Reals.thy
   Author: Johannes Hölzl, Robert Himmelmann, Armin Heller; TU München
   Author: Bogdan Grechuk; University of Edinburgh *)

header {* Extended real number line *}

theory Extended_Reals
  imports Topology_Euclidean_Space
begin

subsection {* Definition and basic properties *}

datatype extreal = extreal real | PInfty | MInfty

notation (xsymbols)
  PInfty  ("\<infinity>")

notation (HTML output)
  PInfty  ("\<infinity>")

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

lemma extreal_between:
  fixes x e :: extreal
  assumes "\<bar>x\<bar> \<noteq> \<infinity>" "0 < e"
  shows "x - e < x" "x < x + e"
using assms apply (cases x, cases e) apply auto
using assms by (cases x, cases e) auto

lemma extreal_distrib:
  fixes a b c :: extreal
  assumes "a \<noteq> \<infinity> \<or> b \<noteq> -\<infinity>" "a \<noteq> -\<infinity> \<or> b \<noteq> \<infinity>" "\<bar>c\<bar> \<noteq> \<infinity>"
  shows "(a + b) * c = a * c + b * c"
  using assms
  by (cases rule: extreal3_cases[of a b c]) (simp_all add: field_simps)

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

lemma extreal_mult_less_right:
  assumes "b * a < c * a" "0 < a" "a < \<infinity>"
  shows "b < c"
  using assms
  by (cases rule: extreal3_cases[of a b c])
     (auto split: split_if_asm simp: zero_less_mult_iff zero_le_mult_iff)

subsection "Complete lattice"

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

lemma (in complete_lattice) top_le:
  "top \<le> x \<Longrightarrow> x = top"
  by (rule antisym) auto

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

lemma infeal_le_Sup:
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

lemma infeal_Inf_le:
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

subsection "Limits on @{typ extreal}"

subsubsection "Topological space"

lemma
  shows extreal_max[simp]: "extreal (max x y) = max (extreal x) (extreal y)"
    and extreal_min[simp]: "extreal (min x y) = min (extreal x) (extreal y)"
  by (simp_all add: min_def max_def)

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
      using *[unfolded choice_iff] by (auto simp: vimage_Union)
  qed ((metis UnionE Union_upper subset_trans *)+)
qed
end

lemma open_extreal: "open S \<Longrightarrow> open (extreal ` S)"
  by (auto simp: inj_vimage_image_eq open_extreal_def)

lemma open_extreal_vimage: "open S \<Longrightarrow> open (extreal -` S)"
  unfolding open_extreal_def by auto

lemma continuous_on_extreal[intro, simp]: "continuous_on A extreal"
  unfolding continuous_on_topological open_extreal_def by auto

lemma continuous_at_extreal[intro, simp]: "continuous (at x) extreal"
  using continuous_on_eq_continuous_at[of UNIV] by auto

lemma continuous_within_extreal[intro, simp]: "x \<in> A \<Longrightarrow> continuous (at x within A) extreal"
  using continuous_on_eq_continuous_within[of A] by auto

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
  then obtain e where "0 < e" and e: "ball (real x) e \<subseteq> extreal -` S"
    using assms unfolding open_contains_ball by force
  show thesis
  proof (intro that subsetI)
    show "0 < extreal e" using `0 < e` by auto
    fix y assume "y \<in> {x - extreal e<..<x + extreal e}"
    with assms obtain t where "y = extreal t" "t \<in> ball (real x) e"
      by (cases y) (auto simp: ball_def dist_real_def)
    then show "y \<in> S" using e by auto
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

lemma extreal_uminus_eq_reorder: "- a = b \<longleftrightarrow> a = (-b::extreal)" by auto

lemma extreal_uminus_less_reorder: "- a < b \<longleftrightarrow> -b < (a::extreal)"
  by (subst (3) extreal_uminus_uminus[symmetric]) (simp only: extreal_minus_less_minus)

lemma extreal_uminus_le_reorder: "- a \<le> b \<longleftrightarrow> -b \<le> (a::extreal)"
  by (subst (3) extreal_uminus_uminus[symmetric]) (simp only: extreal_minus_le_minus)

lemmas extreal_uminus_reorder =
  extreal_uminus_eq_reorder extreal_uminus_less_reorder extreal_uminus_le_reorder

lemma extreal_open_uminus:
  fixes S :: "extreal set"
  assumes "open S"
  shows "open (uminus ` S)"
  unfolding open_extreal_def
proof (intro conjI impI)
  obtain x y where S: "open (extreal -` S)"
    "\<infinity> \<in> S \<Longrightarrow> {extreal x<..} \<subseteq> S" "-\<infinity> \<in> S \<Longrightarrow> {..< extreal y} \<subseteq> S"
    using `open S` unfolding open_extreal_def by auto
  have "extreal -` uminus ` S = uminus ` (extreal -` S)"
  proof safe
    fix x y assume "extreal x = - y" "y \<in> S"
    then show "x \<in> uminus ` extreal -` S" by (cases y) auto
  next
    fix x assume "extreal x \<in> S"
    then show "- x \<in> extreal -` uminus ` S"
      by (auto intro: image_eqI[of _ _ "extreal x"])
  qed
  then show "open (extreal -` uminus ` S)"
    using S by (auto intro: open_negations)
  { assume "\<infinity> \<in> uminus ` S"
    then have "-\<infinity> \<in> S" by (metis image_iff extreal_uminus_uminus)
    then have "uminus ` {..<extreal y} \<subseteq> uminus ` S" using S by (intro image_mono) auto
    then show "\<exists>x. {extreal x<..} \<subseteq> uminus ` S" using extreal_uminus_lessThan by auto }
  { assume "-\<infinity> \<in> uminus ` S"
    then have "\<infinity> : S" by (metis image_iff extreal_uminus_uminus)
    then have "uminus ` {extreal x<..} <= uminus ` S" using S by (intro image_mono) auto
    then show "\<exists>y. {..<extreal y} <= uminus ` S" using extreal_uminus_greaterThan by auto }
qed

lemma extreal_uminus_complement:
  fixes S :: "extreal set"
  shows "uminus ` (- S) = - uminus ` S"
  by (auto intro!: bij_image_Compl_eq surjI[of _ uminus] simp: bij_betw_def)

lemma extreal_closed_uminus:
  fixes S :: "extreal set"
  assumes "closed S"
  shows "closed (uminus ` S)"
using assms unfolding closed_def
using extreal_open_uminus[of "- S"] extreal_uminus_complement by auto

lemma not_open_extreal_singleton:
  "\<not> (open {a :: extreal})"
proof(rule ccontr)
  assume "\<not> \<not> open {a}" hence a: "open {a}" by auto
  show False
  proof (cases a)
    case MInf
    then obtain y where "{..<extreal y} <= {a}" using a open_MInfty2[of "{a}"] by auto
    hence "extreal(y - 1):{a}" apply (subst subsetD[of "{..<extreal y}"]) by auto
    then show False using `a=(-\<infinity>)` by auto
  next
    case PInf
    then obtain y where "{extreal y<..} <= {a}" using a open_PInfty2[of "{a}"] by auto
    hence "extreal(y+1):{a}" apply (subst subsetD[of "{extreal y<..}"]) by auto
    then show False using `a=\<infinity>` by auto
  next
    case (real r) then have fin: "\<bar>a\<bar> \<noteq> \<infinity>" by simp
    from extreal_open_cont_interval[OF a singletonI this] guess e . note e = this
    then obtain b where b_def: "a<b & b<a+e"
      using fin extreal_between extreal_dense[of a "a+e"] by auto
    then have "b: {a-e <..< a+e}" using fin extreal_between[of a e] e by auto
    then show False using b_def e by auto
  qed
qed

lemma extreal_closed_contains_Inf:
  fixes S :: "extreal set"
  assumes "closed S" "S ~= {}"
  shows "Inf S : S"
proof(rule ccontr)
  assume "Inf S \<notin> S" hence a: "open (-S)" "Inf S:(- S)" using assms by auto
  show False
  proof (cases "Inf S")
    case MInf hence "(-\<infinity>) : - S" using a by auto
    then obtain y where "{..<extreal y} <= (-S)" using a open_MInfty2[of "- S"] by auto
    hence "extreal y <= Inf S" by (metis Compl_anti_mono Compl_lessThan atLeast_iff
      complete_lattice_class.Inf_greatest double_complement set_rev_mp)
    then show False using MInf by auto
  next
    case PInf then have "S={\<infinity>}" by (metis Inf_eq_PInfty assms(2))
    then show False by (metis `Inf S ~: S` insert_code mem_def PInf)
  next
    case (real r) then have fin: "\<bar>Inf S\<bar> \<noteq> \<infinity>" by simp
    from extreal_open_cont_interval[OF a this] guess e . note e = this
    { fix x assume "x:S" hence "x>=Inf S" by (rule complete_lattice_class.Inf_lower)
      hence *: "x>Inf S-e" using e by (metis fin extreal_between(1) order_less_le_trans)
      { assume "x<Inf S+e" hence "x:{Inf S-e <..< Inf S+e}" using * by auto
        hence False using e `x:S` by auto
      } hence "x>=Inf S+e" by (metis linorder_le_less_linear)
    } hence "Inf S + e <= Inf S" by (metis le_Inf_iff)
    then show False using real e by (cases e) auto
  qed
qed

lemma extreal_closed_contains_Sup:
  fixes S :: "extreal set"
  assumes "closed S" "S ~= {}"
  shows "Sup S : S"
proof-
  have "closed (uminus ` S)" by (metis assms(1) extreal_closed_uminus)
  hence "Inf (uminus ` S) : uminus ` S" using assms extreal_closed_contains_Inf[of "uminus ` S"] by auto
  hence "- Sup S : uminus ` S" using extreal_Sup_uminus_image_eq[of "uminus ` S"] by (auto simp: image_image)
  thus ?thesis by (metis imageI extreal_uminus_uminus extreal_minus_minus_image)
qed

lemma extreal_open_closed_aux:
  fixes S :: "extreal set"
  assumes "open S" "closed S"
  assumes S: "(-\<infinity>) ~: S"
  shows "S = {}"
proof(rule ccontr)
  assume "S ~= {}"
  hence *: "(Inf S):S" by (metis assms(2) extreal_closed_contains_Inf)
  { assume "Inf S=(-\<infinity>)" hence False using * assms(3) by auto }
  moreover
  { assume "Inf S=\<infinity>" hence "S={\<infinity>}" by (metis Inf_eq_PInfty `S ~= {}`)
    hence False by (metis assms(1) not_open_extreal_singleton) }
  moreover
  { assume fin: "\<bar>Inf S\<bar> \<noteq> \<infinity>"
    from extreal_open_cont_interval[OF assms(1) * fin] guess e . note e = this
    then obtain b where b_def: "Inf S-e<b & b<Inf S"
      using fin extreal_between[of "Inf S" e] extreal_dense[of "Inf S-e"] by auto
    hence "b: {Inf S-e <..< Inf S+e}" using e fin extreal_between[of "Inf S" e] by auto
    hence "b:S" using e by auto
    hence False using b_def by (metis complete_lattice_class.Inf_lower leD)
  } ultimately show False by auto
qed


lemma extreal_open_closed:
  fixes S :: "extreal set"
  shows "(open S & closed S) <-> (S = {} | S = UNIV)"
proof-
{ assume lhs: "open S & closed S"
  { assume "(-\<infinity>) ~: S" hence "S={}" using lhs extreal_open_closed_aux by auto }
  moreover
  { assume "(-\<infinity>) : S" hence "(- S)={}" using lhs extreal_open_closed_aux[of "-S"] by auto }
  ultimately have "S = {} | S = UNIV" by auto
} thus ?thesis by auto
qed


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
       Lim_unique[OF trivial_limit_sequentially] tail_same_limit[of "\<lambda>n. -\<infinity>" "-\<infinity>" M f, OF tendsto_const] by auto
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

lemma extreal_open_affinity_pos:
  assumes "open S" and m: "m \<noteq> \<infinity>" "0 < m" and t: "\<bar>t\<bar> \<noteq> \<infinity>"
  shows "open ((\<lambda>x. m * x + t) ` S)"
proof -
  obtain r where r[simp]: "m = extreal r" using m by (cases m) auto
  obtain p where p[simp]: "t = extreal p" using t by auto
  have "r \<noteq> 0" "0 < r" and m': "m \<noteq> \<infinity>" "m \<noteq> -\<infinity>" "m \<noteq> 0" using m by auto
  from `open S`[THEN extreal_openE] guess l u . note T = this
  let ?f = "(\<lambda>x. m * x + t)"
  show ?thesis unfolding open_extreal_def
  proof (intro conjI impI exI subsetI)
    have "extreal -` ?f ` S = (\<lambda>x. r * x + p) ` (extreal -` S)"
    proof safe
      fix x y assume "extreal y = m * x + t" "x \<in> S"
      then show "y \<in> (\<lambda>x. r * x + p) ` extreal -` S"
        using `r \<noteq> 0` by (cases x) (auto intro!: image_eqI[of _ _ "real x"] split: split_if_asm)
    qed force
    then show "open (extreal -` ?f ` S)"
      using open_affinity[OF T(1) `r \<noteq> 0`] by (auto simp: ac_simps)
  next
    assume "\<infinity> \<in> ?f`S" with `0 < r` have "\<infinity> \<in> S" by auto
    fix x assume "x \<in> {extreal (r * l + p)<..}"
    then have [simp]: "extreal (r * l + p) < x" by auto
    show "x \<in> ?f`S"
    proof (rule image_eqI)
      show "x = m * ((x - t) / m) + t"
        using m t by (cases rule: extreal3_cases[of m x t]) auto
      have "extreal l < (x - t)/m"
        using m t by (simp add: extreal_less_divide_pos extreal_less_minus)
      then show "(x - t)/m \<in> S" using T(2)[OF `\<infinity> \<in> S`] by auto
    qed
  next
    assume "-\<infinity> \<in> ?f`S" with `0 < r` have "-\<infinity> \<in> S" by auto
    fix x assume "x \<in> {..<extreal (r * u + p)}"
    then have [simp]: "x < extreal (r * u + p)" by auto
    show "x \<in> ?f`S"
    proof (rule image_eqI)
      show "x = m * ((x - t) / m) + t"
        using m t by (cases rule: extreal3_cases[of m x t]) auto
      have "(x - t)/m < extreal u"
        using m t by (simp add: extreal_divide_less_pos extreal_minus_less)
      then show "(x - t)/m \<in> S" using T(3)[OF `-\<infinity> \<in> S`] by auto
    qed
  qed
qed

lemma extreal_open_affinity:
  assumes "open S" and m: "\<bar>m\<bar> \<noteq> \<infinity>" "m \<noteq> 0" and t: "\<bar>t\<bar> \<noteq> \<infinity>"
  shows "open ((\<lambda>x. m * x + t) ` S)"
proof cases
  assume "0 < m" then show ?thesis
    using extreal_open_affinity_pos[OF `open S` _ _ t, of m] m by auto
next
  assume "\<not> 0 < m" then
  have "0 < -m" using `m \<noteq> 0` by (cases m) auto
  then have m: "-m \<noteq> \<infinity>" "0 < -m" using `\<bar>m\<bar> \<noteq> \<infinity>`
    by (auto simp: extreal_uminus_eq_reorder)
  from extreal_open_affinity_pos[OF extreal_open_uminus[OF `open S`] m t]
  show ?thesis unfolding image_image by simp
qed

lemma extreal_divide_eq:
  "b \<noteq> 0 \<Longrightarrow> \<bar>b\<bar> \<noteq> \<infinity> \<Longrightarrow> a / b = c \<longleftrightarrow> a = b * c"
  by (cases rule: extreal3_cases[of a b c])
     (simp_all add: field_simps)

lemma extreal_inverse_not_MInfty[simp]: "inverse a \<noteq> -\<infinity>"
  by (cases a) auto

lemma extreal_lim_mult:
  fixes X :: "'a \<Rightarrow> extreal"
  assumes lim: "(X ---> L) net" and a: "\<bar>a\<bar> \<noteq> \<infinity>"
  shows "((\<lambda>i. a * X i) ---> a * L) net"
proof cases
  assume "a \<noteq> 0"
  show ?thesis
  proof (rule topological_tendstoI)
    fix S assume "open S" "a * L \<in> S"
    have "a * L / a = L"
      using `a \<noteq> 0` a by (cases rule: extreal2_cases[of a L]) auto
    then have L: "L \<in> ((\<lambda>x. x / a) ` S)"
      using `a * L \<in> S` by (force simp: image_iff)
    moreover have "open ((\<lambda>x. x / a) ` S)"
      using extreal_open_affinity[OF `open S`, of "inverse a" 0] `a \<noteq> 0` a
      by (auto simp: extreal_divide_eq extreal_inverse_eq_0 divide_extreal_def ac_simps)
    note * = lim[THEN topological_tendstoD, OF this L]
    { fix x from a `a \<noteq> 0` have "a * (x / a) = x"
        by (cases rule: extreal2_cases[of a x]) auto }
    note this[simp]
    show "eventually (\<lambda>x. a * X x \<in> S) net"
      by (rule eventually_mono[OF _ *]) auto
  qed
qed auto

lemma extreal_mult_m1[simp]: "x * extreal (-1) = -x"
  by (cases x) auto

lemma extreal_lim_uminus:
  fixes X :: "'a \<Rightarrow> extreal" shows "((\<lambda>i. - X i) ---> -L) net \<longleftrightarrow> (X ---> L) net"
  using extreal_lim_mult[of X L net "extreal (-1)"]
        extreal_lim_mult[of "(\<lambda>i. - X i)" "-L" net "extreal (-1)"]
  by (auto simp add: algebra_simps)

lemma Lim_bounded2_extreal:
  assumes lim:"f ----> (l :: extreal)"
  and ge: "ALL n>=N. f n >= C"
  shows "l>=C"
proof-
def g == "(%i. -(f i))"
{ fix n assume "n>=N" hence "g n <= -C" using assms extreal_minus_le_minus g_def by auto }
hence "ALL n>=N. g n <= -C" by auto
moreover have limg: "g ----> (-l)" using g_def extreal_lim_uminus lim by auto
ultimately have "-l <= -C" using Lim_bounded_extreal[of g "-l" _ "-C"] by auto
from this show ?thesis using extreal_minus_le_minus by auto
qed


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

lemma (in complete_lattice) not_less_bot[simp]: "\<not> (x < bot)"
proof
  assume "x < bot"
  with bot_least[of x] show False by (auto simp: le_less)
qed

lemma (in complete_lattice) atLeast_eq_UNIV_iff: "{x..} = UNIV \<longleftrightarrow> x = bot"
proof
  assume "{x..} = UNIV"
  show "x = bot"
  proof (rule ccontr)
    assume "x \<noteq> bot" then have "bot \<notin> {x..}" by (simp add: le_less)
    then show False using `{x..} = UNIV` by simp
  qed
qed auto


lemma extreal_open_atLeast: "open {x..} \<longleftrightarrow> x = -\<infinity>"
proof
  assume "x = -\<infinity>" then have "{x..} = UNIV" by auto
  then show "open {x..}" by auto
next
  assume "open {x..}"
  then have "open {x..} \<and> closed {x..}" by auto
  then have "{x..} = UNIV" unfolding extreal_open_closed by auto
  then show "x = -\<infinity>" by (simp add: bot_extreal_def atLeast_eq_UNIV_iff)
qed

lemma extreal_open_mono_set:
  fixes S :: "extreal set"
  defines "a \<equiv> Inf S"
  shows "(open S \<and> mono S) \<longleftrightarrow> (S = UNIV \<or> S = {a <..})"
  by (metis Inf_UNIV a_def atLeast_eq_UNIV_iff extreal_open_atLeast
            extreal_open_closed mono_set_iff open_extreal_greaterThan)

lemma extreal_closed_mono_set:
  fixes S :: "extreal set"
  shows "(closed S \<and> mono S) \<longleftrightarrow> (S = {} \<or> S = {Inf S ..})"
  by (metis Inf_UNIV atLeast_eq_UNIV_iff closed_extreal_atLeast
            extreal_open_closed mono_empty mono_set_iff open_extreal_greaterThan)

lemma extreal_Liminf_Sup_monoset:
  fixes f :: "'a => extreal"
  shows "Liminf net f = Sup {l. \<forall>S. open S \<longrightarrow> mono S \<longrightarrow> l \<in> S \<longrightarrow> eventually (\<lambda>x. f x \<in> S) net}"
  unfolding Liminf_Sup
proof (intro arg_cong[where f="\<lambda>P. Sup (Collect P)"] ext iffI allI impI)
  fix l S assume ev: "\<forall>y<l. eventually (\<lambda>x. y < f x) net" and "open S" "mono S" "l \<in> S"
  then have "S = UNIV \<or> S = {Inf S <..}"
    using extreal_open_mono_set[of S] by auto
  then show "eventually (\<lambda>x. f x \<in> S) net"
  proof
    assume S: "S = {Inf S<..}"
    then have "Inf S < l" using `l \<in> S` by auto
    then have "eventually (\<lambda>x. Inf S < f x) net" using ev by auto
    then show "eventually (\<lambda>x. f x \<in> S) net"  by (subst S) auto
  qed auto
next
  fix l y assume S: "\<forall>S. open S \<longrightarrow> mono S \<longrightarrow> l \<in> S \<longrightarrow> eventually  (\<lambda>x. f x \<in> S) net" "y < l"
  have "eventually  (\<lambda>x. f x \<in> {y <..}) net"
    using `y < l` by (intro S[rule_format]) auto
  then show "eventually (\<lambda>x. y < f x) net" by auto
qed

lemma extreal_Inf_uminus_image_eq: "Inf (uminus ` S) = - Sup (S::extreal set)"
  using extreal_Sup_uminus_image_eq[of "uminus ` S"] by (simp add: image_image)

lemma extreal_range_uminus[simp]: "range uminus = (UNIV::extreal set)"
proof safe
  fix x :: extreal show "x \<in> range uminus" by (intro image_eqI[of _ _ "-x"]) auto
qed auto

lemma extreal_Limsup_Inf_monoset:
  fixes f :: "'a => extreal"
  shows "Limsup net f = Inf {l. \<forall>S. open S \<longrightarrow> mono (uminus ` S) \<longrightarrow> l \<in> S \<longrightarrow> eventually (\<lambda>x. f x \<in> S) net}"
  unfolding Limsup_Inf
proof (intro arg_cong[where f="\<lambda>P. Inf (Collect P)"] ext iffI allI impI)
  fix l S assume ev: "\<forall>y>l. eventually (\<lambda>x. f x < y) net" and "open S" "mono (uminus`S)" "l \<in> S"
  then have "open (uminus`S) \<and> mono (uminus`S)" by (simp add: extreal_open_uminus)
  then have "S = UNIV \<or> S = {..< Sup S}"
    unfolding extreal_open_mono_set extreal_Inf_uminus_image_eq extreal_image_uminus_shift by simp
  then show "eventually (\<lambda>x. f x \<in> S) net"
  proof
    assume S: "S = {..< Sup S}"
    then have "l < Sup S" using `l \<in> S` by auto
    then have "eventually (\<lambda>x. f x < Sup S) net" using ev by auto
    then show "eventually (\<lambda>x. f x \<in> S) net"  by (subst S) auto
  qed auto
next
  fix l y assume S: "\<forall>S. open S \<longrightarrow> mono (uminus`S) \<longrightarrow> l \<in> S \<longrightarrow> eventually  (\<lambda>x. f x \<in> S) net" "l < y"
  have "eventually  (\<lambda>x. f x \<in> {..< y}) net"
    using `l < y` by (intro S[rule_format]) auto
  then show "eventually (\<lambda>x. f x < y) net" by auto
qed

lemma open_uminus_iff: "open (uminus ` S) \<longleftrightarrow> open (S::extreal set)"
  using extreal_open_uminus[of S] extreal_open_uminus[of "uminus`S"] by auto

lemma extreal_Limsup_uminus:
  fixes f :: "'a => extreal"
  shows "Limsup net (\<lambda>x. - (f x)) = -(Liminf net f)"
proof -
  { fix P l have "(\<exists>x. (l::extreal) = -x \<and> P x) \<longleftrightarrow> P (-l)" by (auto intro!: exI[of _ "-l"]) }
  note Ex_cancel = this
  { fix P :: "extreal set \<Rightarrow> bool" have "(\<forall>S. P S) \<longleftrightarrow> (\<forall>S. P (uminus`S))"
      apply auto by (erule_tac x="uminus`S" in allE) (auto simp: image_image) }
  note add_uminus_image = this
  { fix x S have "(x::extreal) \<in> uminus`S \<longleftrightarrow> -x\<in>S" by (auto intro!: image_eqI[of _ _ "-x"]) }
  note remove_uminus_image = this
  show ?thesis
    unfolding extreal_Limsup_Inf_monoset extreal_Liminf_Sup_monoset
    unfolding extreal_Inf_uminus_image_eq[symmetric] image_Collect Ex_cancel
    by (subst add_uminus_image) (simp add: open_uminus_iff remove_uminus_image)
qed

lemma extreal_Liminf_uminus:
  fixes f :: "'a => extreal"
  shows "Liminf net (\<lambda>x. - (f x)) = -(Limsup net f)"
  using extreal_Limsup_uminus[of _ "(\<lambda>x. - (f x))"] by auto

lemma extreal_Lim_uminus:
  fixes f :: "'a \<Rightarrow> extreal" shows "(f ---> f0) net \<longleftrightarrow> ((\<lambda>x. - f x) ---> - f0) net"
  using
    extreal_lim_mult[of f f0 net "- 1"]
    extreal_lim_mult[of "\<lambda>x. - (f x)" "-f0" net "- 1"]
  by (auto simp: extreal_uminus_reorder)

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

lemma lim_imp_Limsup:
  fixes f :: "'a => extreal"
  assumes "\<not> trivial_limit net"
  assumes lim: "(f ---> f0) net"
  shows "Limsup net f = f0"
  using extreal_Lim_uminus[of f f0] lim_imp_Liminf[of net "(%x. -(f x))" "-f0"]
     extreal_Liminf_uminus[of net f] assms by simp

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

lemma Liminf_PInfty:
  fixes f :: "'a \<Rightarrow> extreal"
  assumes "\<not> trivial_limit net"
  shows "(f ---> \<infinity>) net \<longleftrightarrow> Liminf net f = \<infinity>"
proof (intro lim_imp_Liminf iffI assms)
  assume rhs: "Liminf net f = \<infinity>"
  { fix S assume "open S & \<infinity> : S"
    then obtain m where "{extreal m<..} <= S" using open_PInfty2 by auto
    moreover have "eventually (\<lambda>x. f x \<in> {extreal m<..}) net"
      using rhs unfolding Liminf_Sup top_extreal_def[symmetric] Sup_eq_top_iff
      by (auto elim!: allE[where x="extreal m"] simp: top_extreal_def)
    ultimately have "eventually (%x. f x : S) net" apply (subst eventually_mono) by auto
  } then show "(f ---> \<infinity>) net" unfolding tendsto_def by auto
qed

lemma Limsup_MInfty:
  fixes f :: "'a \<Rightarrow> extreal"
  assumes "\<not> trivial_limit net"
  shows "(f ---> -\<infinity>) net \<longleftrightarrow> Limsup net f = -\<infinity>"
  using assms extreal_Lim_uminus[of f "-\<infinity>"] Liminf_PInfty[of _ "\<lambda>x. - (f x)"]
        extreal_Liminf_uminus[of _ f] by (auto simp: extreal_uminus_eq_reorder)

lemma extreal_Liminf_eq_Limsup:
  fixes f :: "'a \<Rightarrow> extreal"
  assumes ntriv: "\<not> trivial_limit net"
  assumes lim: "Liminf net f = f0" "Limsup net f = f0"
  shows "(f ---> f0) net"
proof (cases f0)
  case PInf then show ?thesis using Liminf_PInfty[OF ntriv] lim by auto
next
  case MInf then show ?thesis using Limsup_MInfty[OF ntriv] lim by auto
next
  case (real r)
  show "(f ---> f0) net"
  proof (rule topological_tendstoI)
    fix S assume "open S""f0 \<in> S"
    then obtain a b where "a < Liminf net f" "Limsup net f < b" "{a<..<b} \<subseteq> S"
      using extreal_open_cont_interval2[of S f0] real lim by auto
    then have "eventually (\<lambda>x. f x \<in> {a<..<b}) net"
      unfolding Liminf_Sup Limsup_Inf less_Sup_iff Inf_less_iff
      by (auto intro!: eventually_conj simp add: greaterThanLessThan_iff)
    with `{a<..<b} \<subseteq> S` show "eventually (%x. f x : S) net"
      by (rule_tac eventually_mono) auto
  qed
qed

lemma extreal_Liminf_eq_Limsup_iff:
  fixes f :: "'a \<Rightarrow> extreal"
  assumes "\<not> trivial_limit net"
  shows "(f ---> f0) net \<longleftrightarrow> Liminf net f = f0 \<and> Limsup net f = f0"
  by (metis assms extreal_Liminf_eq_Limsup lim_imp_Liminf lim_imp_Limsup)


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

lemma limsup_INFI_SUPR:
  fixes f :: "nat \<Rightarrow> extreal"
  shows "limsup f = (INF n. SUP m:{n..}. f m)"
  using extreal_Limsup_uminus[of sequentially "\<lambda>x. - f x"]
  by (simp add: liminf_SUPR_INFI extreal_INFI_uminus extreal_SUPR_uminus)

lemma liminf_PInfty:
  fixes X :: "nat => extreal"
  shows "X ----> \<infinity> <-> liminf X = \<infinity>"
by (metis Liminf_PInfty trivial_limit_sequentially)

lemma limsup_MInfty:
  fixes X :: "nat => extreal"
  shows "X ----> (-\<infinity>) <-> limsup X = (-\<infinity>)"
by (metis Limsup_MInfty trivial_limit_sequentially)

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

lemma liminf_bounded_open:
  fixes x :: "nat \<Rightarrow> extreal"
  shows "x0 \<le> liminf x \<longleftrightarrow> (\<forall>S. open S \<longrightarrow> mono S \<longrightarrow> x0 \<in> S \<longrightarrow> (\<exists>N. \<forall>n\<ge>N. x n \<in> S))" 
  (is "_ \<longleftrightarrow> ?P x0")
proof
  assume "?P x0" then show "x0 \<le> liminf x"
    unfolding extreal_Liminf_Sup_monoset eventually_sequentially
    by (intro complete_lattice_class.Sup_upper) auto
next
  assume "x0 \<le> liminf x"
  { fix S :: "extreal set" assume om: "open S & mono S & x0:S"
    { assume "S = UNIV" hence "EX N. (ALL n>=N. x n : S)" by auto }
    moreover
    { assume "~(S=UNIV)"
      then obtain B where B_def: "S = {B<..}" using om extreal_open_mono_set by auto
      hence "B<x0" using om by auto
      hence "EX N. ALL n>=N. x n : S" unfolding B_def using `x0 \<le> liminf x` liminf_bounded_iff by auto
    } ultimately have "EX N. (ALL n>=N. x n : S)" by auto
  } then show "?P x0" by auto
qed


lemma extreal_lim_mono:
  fixes X Y :: "nat => extreal"
  assumes "\<And>n. N \<le> n \<Longrightarrow> X n <= Y n"
  assumes "X ----> x" "Y ----> y"
  shows "x <= y"
  by (metis extreal_Liminf_eq_Limsup_iff[OF trivial_limit_sequentially] assms liminf_mono)

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

lemma limsup_subseq_mono:
  fixes X :: "nat \<Rightarrow> extreal"
  assumes "subseq r"
  shows "limsup (X \<circ> r) \<le> limsup X"
proof-
  have "(\<lambda>n. - X n) \<circ> r = (\<lambda>n. - (X \<circ> r) n)" by (simp add: fun_eq_iff)
  then have "- limsup X \<le> - limsup (X \<circ> r)"
     using liminf_subseq_mono[of r "(%n. - X n)"]
       extreal_Liminf_uminus[of sequentially X]
       extreal_Liminf_uminus[of sequentially "X o r"] assms by auto
  then show ?thesis by auto
qed

lemma bounded_abs:
  assumes "(a::real)<=x" "x<=b"
  shows "abs x <= max (abs a) (abs b)"
by (metis abs_less_iff assms leI le_max_iff_disj less_eq_real_def less_le_not_le less_minus_iff minus_minus)


lemma bounded_increasing_convergent2: fixes f::"nat => real"
  assumes "ALL n. f n <= B"  "ALL n m. n>=m --> f n >= f m"
  shows "EX l. (f ---> l) sequentially"
proof-
def N == "max (abs (f 0)) (abs B)"
{ fix n have "abs (f n) <= N" unfolding N_def apply (subst bounded_abs) using assms by auto }
hence "bounded {f n| n::nat. True}" unfolding bounded_real by auto
from this show ?thesis apply(rule Topology_Euclidean_Space.bounded_increasing_convergent)
   using assms by auto
qed

lemma extreal_real': assumes "\<bar>x\<bar> \<noteq> \<infinity>" shows "extreal (real x) = x"
  using assms by auto

lemma lim_extreal_increasing: assumes "\<And>n m. n >= m \<Longrightarrow> f n >= f m"
  obtains l where "f ----> (l::extreal)"
proof(cases "f = (\<lambda>x. - \<infinity>)")
  case True then show thesis using Lim_const[of "- \<infinity>" sequentially] by (intro that[of "-\<infinity>"]) auto
next
  case False
  from this obtain N where N_def: "f N > (-\<infinity>)" by (auto simp: fun_eq_iff)
  have "ALL n>=N. f n >= f N" using assms by auto
  hence minf: "ALL n>=N. f n > (-\<infinity>)" using N_def by auto
  def Y == "(%n. (if n>=N then f n else f N))"
  hence incy: "!!n m. n>=m ==> Y n >= Y m" using assms by auto
  from minf have minfy: "ALL n. Y n ~= (-\<infinity>)" using Y_def by auto
  show thesis
  proof(cases "EX B. ALL n. f n < extreal B")
    case False thus thesis apply- apply(rule that[of \<infinity>]) unfolding Lim_PInfty not_ex not_all
    apply safe apply(erule_tac x=B in allE,safe) apply(rule_tac x=x in exI,safe)
    apply(rule order_trans[OF _ assms[rule_format]]) by auto
  next case True then guess B ..
    hence "ALL n. Y n < extreal B" using Y_def by auto note B = this[rule_format]
    { fix n have "Y n < \<infinity>" using B[of n] apply (subst less_le_trans) by auto
      hence "Y n ~= \<infinity> & Y n ~= (-\<infinity>)" using minfy by auto
    } hence *: "ALL n. \<bar>Y n\<bar> \<noteq> \<infinity>" by auto
    { fix n have "real (Y n) < B" proof- case goal1 thus ?case
        using B[of n] apply-apply(subst(asm) extreal_real'[THEN sym]) defer defer
        unfolding extreal_less using * by auto
      qed
    }
    hence B': "ALL n. (real (Y n) <= B)" using less_imp_le by auto
    have "EX l. (%n. real (Y n)) ----> l"
      apply(rule bounded_increasing_convergent2)
    proof safe show "!!n. real (Y n) <= B" using B' by auto
      fix n m::nat assume "n<=m"
      hence "extreal (real (Y n)) <= extreal (real (Y m))"
        using incy[rule_format,of n m] apply(subst extreal_real)+
        using *[rule_format, of n] *[rule_format, of m] by auto
      thus "real (Y n) <= real (Y m)" by auto
    qed then guess l .. note l=this
    have "Y ----> extreal l" using l apply-apply(subst(asm) lim_extreal[THEN sym])
    unfolding extreal_real using * by auto
    thus thesis apply-apply(rule that[of "extreal l"])
       apply (subst tail_same_limit[of Y _ N]) using Y_def by auto
  qed
qed

lemma lim_extreal_decreasing: assumes "\<And>n m. n >= m \<Longrightarrow> f n <= f m"
  obtains l where "f ----> (l::extreal)"
proof -
  from lim_extreal_increasing[of "\<lambda>x. - f x"] assms
  obtain l where "(\<lambda>x. - f x) ----> l" by auto
  from extreal_lim_mult[OF this, of "- 1"] show thesis 
    by (intro that[of "-l"]) (simp add: extreal_uminus_eq_reorder)
qed

lemma compact_extreal:
  fixes X :: "nat \<Rightarrow> extreal"
  shows "\<exists>l r. subseq r \<and> (X \<circ> r) ----> l"
proof -
  obtain r where "subseq r" and mono: "monoseq (X \<circ> r)"
    using seq_monosub[of X] unfolding comp_def by auto
  then have "(\<forall>n m. m \<le> n \<longrightarrow> (X \<circ> r) m \<le> (X \<circ> r) n) \<or> (\<forall>n m. m \<le> n \<longrightarrow> (X \<circ> r) n \<le> (X \<circ> r) m)"
    by (auto simp add: monoseq_def)
  then obtain l where "(X\<circ>r) ----> l"
     using lim_extreal_increasing[of "X \<circ> r"] lim_extreal_decreasing[of "X \<circ> r"] by auto
  then show ?thesis using `subseq r` by auto
qed

lemma extreal_Sup_lim:
  assumes "\<And>n. b n \<in> s" "b ----> (a::extreal)"
  shows "a \<le> Sup s"
by (metis Lim_bounded_extreal assms complete_lattice_class.Sup_upper)

lemma extreal_Inf_lim:
  assumes "\<And>n. b n \<in> s" "b ----> (a::extreal)"
  shows "Inf s \<le> a"
by (metis Lim_bounded2_extreal assms complete_lattice_class.Inf_lower)

lemma incseq_le_extreal: assumes inc: "!!n m. n>=m ==> X n >= X m"
  and lim: "X ----> (L::extreal)" shows "X N <= L"
proof(cases "X N = (-\<infinity>)")
  case True thus ?thesis by auto
next
  case False
  have "ALL n>=N. X n >= X N" using inc by auto
  hence minf: "ALL n>=N. X n > (-\<infinity>)" using False by auto
  def Y == "(%n. (if n>=N then X n else X N))"
  hence incy: "!!n m. n>=m ==> Y n >= Y m" using inc by auto
  from minf have minfy: "ALL n. Y n ~= (-\<infinity>)" using Y_def by auto
  from lim have limy: "Y ----> L"
    apply (subst tail_same_limit[of X _ N]) using Y_def by auto
  show ?thesis
  proof (cases "\<bar>L\<bar> = \<infinity>")
    case False have "ALL n. Y n ~= \<infinity>"
    proof(rule ccontr,unfold not_all not_not,safe)
      case goal1 hence "ALL n>=x. Y n = \<infinity>" using incy[of x] by auto
      hence "Y ----> \<infinity>" unfolding tendsto_def eventually_sequentially
        apply safe apply(rule_tac x=x in exI) by auto
      note Lim_unique[OF trivial_limit_sequentially this limy]
      with False show False by auto
    qed
    with minfy have *: "\<And>n. \<bar>Y n\<bar> \<noteq> \<infinity>" by auto

    have **:"ALL m n. m <= n --> extreal (real (Y m)) <= extreal (real (Y n))"
      unfolding extreal_real using minfy * incy apply (cases "Y m", cases "Y n") by auto
    have "real (Y N) <= real L" apply-apply(rule incseq_le) defer
      apply(subst lim_extreal[THEN sym])
      unfolding extreal_real
      unfolding incseq_def using * ** limy False by auto
    hence "extreal (real (Y N)) <= extreal (real L)" by auto
    hence ***: "Y N <= L" unfolding extreal_real using * False by auto
    thus ?thesis using Y_def by auto
  next
    case True
    show ?thesis
    proof(cases "L=(-\<infinity>)")
      case True
      have "open {..<X N}" by auto
      moreover have "(-\<infinity>) : {..<X N}" using False by auto
      ultimately obtain N1 where "ALL n>=N1. X n : {..<X N}" using lim True
        unfolding tendsto_def eventually_sequentially by metis
      hence "X (max N N1) : {..<X N}" by auto
      with inc[of N "max N N1"] show ?thesis by auto
    next
      case False thus ?thesis using True by auto qed
  qed
qed

lemma decseq_ge_extreal: assumes dec: "!!n m. n>=m ==> X n <= X m"
  and lim: "X ----> (L::extreal)" shows "X N >= L"
proof-
def Y == "(%i. -(X i))"
hence inc: "!!n m. n>=m ==> Y n >= Y m" using dec extreal_minus_le_minus by auto
moreover have limy: "Y ----> (-L)" using Y_def extreal_lim_uminus lim by auto
ultimately have "Y N <= -L" using incseq_le_extreal[of Y "-L"] by auto
from this show ?thesis using Y_def extreal_minus_le_minus by auto
qed


lemma real_interm:
 assumes "(a::real)<b"
 shows "a + (b-a)/2 < b"
by (metis Bit0_def assms comm_semiring_1_class.normalizing_semiring_rules(24) diff_minus_eq_add number_of_is_id one_is_num_one pth_2 real_average_minus_second real_gt_half_sum succ_def)


lemma SUP_Lim_extreal: assumes "!!n m. n>=m ==> f n >= f m" "f ----> l"
  shows "(SUP n. f n) = (l::extreal)" unfolding SUPR_def Sup_extreal_def
proof (safe intro!: Least_equality)
  fix n::nat show "f n <= l" apply(rule incseq_le_extreal)
    using assms by auto
next fix y assume y:"ALL x:range f. x <= y" show "l <= y"
  proof-
    { assume yinf: "\<bar>y\<bar> \<noteq> \<infinity>"
      { assume as:"y < l"
        hence linf: "\<bar>l\<bar> \<noteq> \<infinity>"
          using Lim_bounded_PInfty[OF assms(2), of "real y"] y yinf by auto
        have [simp]: "extreal (1 / 2) = 1 / 2" by (auto simp: divide_extreal_def)
        have yl:"real y < real l" using as
          apply(subst(asm) extreal_real'[THEN sym,OF yinf])
          apply(subst(asm) extreal_real'[THEN sym,OF linf]) by auto
        hence "y + (l - y) * 1 / 2 < l" apply-
          apply(subst extreal_real'[THEN sym,OF yinf])
          apply(subst(2) extreal_real'[THEN sym,OF yinf])
          apply(subst extreal_real'[THEN sym,OF linf])
          apply(subst(2) extreal_real'[THEN sym,OF linf])
          using real_interm by auto
        hence *:"l : {y + (l - y) / 2<..}" by auto
        have "open {y + (l-y)/2 <..}" by auto
        note topological_tendstoD[OF assms(2) this *]
        from this[unfolded eventually_sequentially] guess N .. note this[rule_format, of N]
        hence "y + (l - y)  / 2 < y" using y[rule_format,of "f N"] by auto
        hence "extreal (real y) + (extreal (real l) - extreal (real y)) / 2 < extreal (real y)"
          unfolding extreal_real using yinf linf by auto
        hence False using yl by auto
      } hence ?thesis using not_le by auto
    }
    moreover
    { assume "y=(-\<infinity>)" hence "f = (\<lambda>_. -\<infinity>)" using y by (auto simp: fun_eq_iff)
      hence "l=(-\<infinity>)" using `f ----> l` using tendsto_const[of "-\<infinity>"]
         Lim_unique[OF trivial_limit_sequentially] by auto
      hence ?thesis by auto
    }
    moreover have "y=\<infinity> --> l <= y" by auto
    ultimately show ?thesis by blast
  qed
qed

lemma INF_Lim_extreal: assumes "!!n m. n>=m ==> f n <= f m" "f ----> l"
  shows "(INF n. f n) = (l::extreal)"
proof-
def Y == "(%i. -(f i))"
hence inc: "!!n m. n>=m ==> Y n >= Y m" using assms extreal_minus_le_minus by auto
moreover have limy: "Y ----> (-l)" using Y_def extreal_lim_uminus assms by auto
ultimately have "(SUP n. Y n) = -l" using SUP_Lim_extreal[of Y "-l"] by auto
hence "- (INF n. f n) = - l" using Y_def extreal_SUPR_uminus[of "UNIV" f] by auto
from this show ?thesis by simp
qed


lemma incseq_mono: "mono f <-> incseq f"
  unfolding mono_def incseq_def by auto


lemma SUP_eq_LIMSEQ:
  assumes "mono f"
  shows "(SUP n. extreal (f n)) = extreal x <-> f ----> x"
proof
  assume x: "(SUP n. extreal (f n)) = extreal x"
  { fix n
    have "extreal (f n) <= extreal x" using x[symmetric] by (auto intro: le_SUPI)
    hence "f n <= x" using assms by simp }
  show "f ----> x"
  proof (rule LIMSEQ_I)
    fix r :: real assume "0 < r"
    show "EX no. ALL n>=no. norm (f n - x) < r"
    proof (rule ccontr)
      assume *: "~ ?thesis"
      { fix N
        from * obtain n where "N <= n" "r <= x - f n"
          using `!!n. f n <= x` by (auto simp: not_less)
        hence "f N <= f n" using `mono f` by (auto dest: monoD)
        hence "f N <= x - r" using `r <= x - f n` by auto
        hence "extreal (f N) <= extreal (x - r)" by auto }
      hence "(SUP n. extreal (f n)) <= extreal (x - r)"
        and "extreal (x - r) < extreal x" using `0 < r` by (auto intro: SUP_leI)
      hence "(SUP n. extreal (f n)) < extreal x" by (rule le_less_trans)
      thus False using x by auto
    qed
  qed
next
  assume "f ----> x"
  show "(SUP n. extreal (f n)) = extreal x"
  proof (rule extreal_SUPI)
    fix n
    from incseq_le[of f x] `mono f` `f ----> x`
    show "extreal (f n) <= extreal x" using assms incseq_mono by auto
  next
    fix y assume *: "!!n. n:UNIV ==> extreal (f n) <= y"
    show "extreal x <= y"
    proof-
    { assume "EX r. y = extreal r"
      from this obtain r where r_def: "y = extreal r" by auto
      with * have "EX N. ALL n>=N. f n <= r" using assms by fastsimp
      from LIMSEQ_le_const2[OF `f ----> x` this]
      have "extreal x <= y" using r_def by auto
    }
    moreover
    { assume "y=\<infinity> | y=(-\<infinity>)"
      hence ?thesis using * by auto
    } ultimately show ?thesis by (cases y) auto
    qed
  qed
qed


lemma Liminf_within:
  fixes f :: "'a::metric_space => extreal"
  shows "Liminf (at x within S) f = (SUP e:{0<..}. INF y:(S Int ball x e - {x}). f y)"
proof-
let ?l="(SUP e:{0<..}. INF y:(S Int ball x e - {x}). f y)"
{ fix T assume T_def: "open T & mono T & ?l:T"
  have "EX d>0. ALL y:S. 0 < dist y x & dist y x < d --> f y : T"
  proof-
  { assume "T=UNIV" hence ?thesis by (simp add: gt_ex) }
  moreover
  { assume "~(T=UNIV)"
    then obtain B where "T={B<..}" using T_def extreal_open_mono_set[of T] by auto
    hence "B<?l" using T_def by auto
    then obtain d where d_def: "0<d & B<(INF y:(S Int ball x d - {x}). f y)"
      unfolding less_SUP_iff by auto
    { fix y assume "y:S & 0 < dist y x & dist y x < d"
      hence "y:(S Int ball x d - {x})" unfolding ball_def by (auto simp add: dist_commute)
      hence "f y:T" using d_def INF_leI[of y "S Int ball x d - {x}" f] `T={B<..}` by auto
    } hence ?thesis apply(rule_tac x="d" in exI) using d_def by auto
  } ultimately show ?thesis by auto
  qed
}
moreover
{ fix z
  assume a: "ALL T. open T --> mono T --> z : T -->
     (EX d>0. ALL y:S. 0 < dist y x & dist y x < d --> f y : T)"
  { fix B assume "B<z"
    then obtain d where d_def: "d>0 & (ALL y:S. 0 < dist y x & dist y x < d --> B < f y)"
       using a[rule_format, of "{B<..}"] mono_greaterThan by auto
    { fix y assume "y:(S Int ball x d - {x})"
      hence "y:S & 0 < dist y x & dist y x < d" unfolding ball_def apply (simp add: dist_commute)
         by (metis dist_eq_0_iff real_less_def zero_le_dist)
      hence "B <= f y" using d_def by auto
    } hence "B <= INFI (S Int ball x d - {x}) f" apply (subst le_INFI) by auto
    also have "...<=?l" apply (subst le_SUPI) using d_def by auto
    finally have "B<=?l" by auto
  } hence "z <= ?l" using extreal_le_extreal[of z "?l"] by auto
}
ultimately show ?thesis unfolding extreal_Liminf_Sup_monoset eventually_within
   apply (subst extreal_SupI[of _ "(SUP e:{0<..}. INFI (S Int ball x e - {x}) f)"]) by auto
qed

lemma Limsup_within:
  fixes f :: "'a::metric_space => extreal"
  shows "Limsup (at x within S) f = (INF e:{0<..}. SUP y:(S Int ball x e - {x}). f y)"
proof-
let ?l="(INF e:{0<..}. SUP y:(S Int ball x e - {x}). f y)"
{ fix T assume T_def: "open T & mono (uminus ` T) & ?l:T"
  have "EX d>0. ALL y:S. 0 < dist y x & dist y x < d --> f y : T"
  proof-
  { assume "T=UNIV" hence ?thesis by (simp add: gt_ex) }
  moreover
  { assume "~(T=UNIV)" hence "~(uminus ` T = UNIV)"
       by (metis Int_UNIV_right Int_absorb1 image_mono extreal_minus_minus_image subset_UNIV)
    hence "uminus ` T = {Inf (uminus ` T)<..}" using T_def extreal_open_mono_set[of "uminus ` T"]
       extreal_open_uminus[of T] by auto
    then obtain B where "T={..<B}"
      unfolding extreal_Inf_uminus_image_eq extreal_uminus_lessThan[symmetric]
      unfolding inj_image_eq_iff[OF extreal_inj_on_uminus] by simp
    hence "?l<B" using T_def by auto
    then obtain d where d_def: "0<d & (SUP y:(S Int ball x d - {x}). f y)<B"
      unfolding INF_less_iff by auto
    { fix y assume "y:S & 0 < dist y x & dist y x < d"
      hence "y:(S Int ball x d - {x})" unfolding ball_def by (auto simp add: dist_commute)
      hence "f y:T" using d_def le_SUPI[of y "S Int ball x d - {x}" f] `T={..<B}` by auto
    } hence ?thesis apply(rule_tac x="d" in exI) using d_def by auto
  } ultimately show ?thesis by auto
  qed
}
moreover
{ fix z
  assume a: "ALL T. open T --> mono (uminus ` T) --> z : T -->
     (EX d>0. ALL y:S. 0 < dist y x & dist y x < d --> f y : T)"
  { fix B assume "z<B"
    then obtain d where d_def: "d>0 & (ALL y:S. 0 < dist y x & dist y x < d --> f y<B)"
       using a[rule_format, of "{..<B}"] by auto
    { fix y assume "y:(S Int ball x d - {x})"
      hence "y:S & 0 < dist y x & dist y x < d" unfolding ball_def apply (simp add: dist_commute)
         by (metis dist_eq_0_iff real_less_def zero_le_dist)
      hence "f y <= B" using d_def by auto
    } hence "SUPR (S Int ball x d - {x}) f <= B" apply (subst SUP_leI) by auto
    moreover have "?l<=SUPR (S Int ball x d - {x}) f" apply (subst INF_leI) using d_def by auto
    ultimately have "?l<=B" by auto
  } hence "?l <= z" using extreal_ge_extreal[of z "?l"] by auto
}
ultimately show ?thesis unfolding extreal_Limsup_Inf_monoset eventually_within
   apply (subst extreal_InfI) by auto
qed


lemma Liminf_within_UNIV:
  fixes f :: "'a::metric_space => extreal"
  shows "Liminf (at x) f = Liminf (at x within UNIV) f"
by (metis within_UNIV)


lemma Liminf_at:
  fixes f :: "'a::metric_space => extreal"
  shows "Liminf (at x) f = (SUP e:{0<..}. INF y:(ball x e - {x}). f y)"
using Liminf_within[of x UNIV f] Liminf_within_UNIV[of x f] by auto


lemma Limsup_within_UNIV:
  fixes f :: "'a::metric_space => extreal"
  shows "Limsup (at x) f = Limsup (at x within UNIV) f"
by (metis within_UNIV)


lemma Limsup_at:
  fixes f :: "'a::metric_space => extreal"
  shows "Limsup (at x) f = (INF e:{0<..}. SUP y:(ball x e - {x}). f y)"
using Limsup_within[of x UNIV f] Limsup_within_UNIV[of x f] by auto

lemma Lim_within_constant:
  fixes f :: "'a::metric_space => 'b::topological_space"
  assumes "ALL y:S. f y = C"
  shows "(f ---> C) (at x within S)"
unfolding tendsto_def eventually_within
by (metis assms(1) linorder_le_less_linear n_not_Suc_n real_of_nat_le_zero_cancel_iff)

lemma Liminf_within_constant:
  fixes f :: "'a::metric_space => extreal"
  assumes "ALL y:S. f y = C"
  assumes "~trivial_limit (at x within S)"
  shows "Liminf (at x within S) f = C"
by (metis Lim_within_constant assms lim_imp_Liminf)

lemma Limsup_within_constant:
  fixes f :: "'a::metric_space => extreal"
  assumes "ALL y:S. f y = C"
  assumes "~trivial_limit (at x within S)"
  shows "Limsup (at x within S) f = C"
by (metis Lim_within_constant assms lim_imp_Limsup)

lemma islimpt_punctured:
"x islimpt S = x islimpt (S-{x})"
unfolding islimpt_def by blast


lemma islimpt_in_closure:
"(x islimpt S) = (x:closure(S-{x}))"
unfolding closure_def using islimpt_punctured by blast


lemma not_trivial_limit_within:
  "~trivial_limit (at x within S) = (x:closure(S-{x}))"
using islimpt_in_closure by (metis trivial_limit_within)


lemma not_trivial_limit_within_ball:
  "(~trivial_limit (at x within S)) = (ALL e>0. S Int ball x e - {x} ~= {})"
  (is "?lhs = ?rhs")
proof-
{ assume "?lhs"
  { fix e :: real assume "e>0"
    then obtain y where "y:(S-{x}) & dist y x < e"
       using `?lhs` not_trivial_limit_within[of x S] closure_approachable[of x "S - {x}"] by auto
    hence "y : (S Int ball x e - {x})" unfolding ball_def by (simp add: dist_commute)
    hence "S Int ball x e - {x} ~= {}" by blast
  } hence "?rhs" by auto
}
moreover
{ assume "?rhs"
  { fix e :: real assume "e>0"
    then obtain y where "y : (S Int ball x e - {x})" using `?rhs` by blast
    hence "y:(S-{x}) & dist y x < e" unfolding ball_def by (simp add: dist_commute)
    hence "EX y:(S-{x}). dist y x < e" by auto
  } hence "?lhs" using not_trivial_limit_within[of x S] closure_approachable[of x "S - {x}"] by auto
} ultimately show ?thesis by auto
qed

subsubsection {* Continuity *}

lemma continuous_imp_tendsto:
  assumes "continuous (at x0) f"
  assumes "x ----> x0"
  shows "(f o x) ----> (f x0)"
proof-
{ fix S assume "open S & (f x0):S"
  from this obtain T where T_def: "open T & x0 : T & (ALL x:T. f x : S)"
     using assms continuous_at_open by metis
  hence "(EX N. ALL n>=N. x n : T)" using assms tendsto_explicit T_def by auto
  hence "(EX N. ALL n>=N. f(x n) : S)" using T_def by auto
} from this show ?thesis using tendsto_explicit[of "f o x" "f x0"] by auto
qed


lemma continuous_at_sequentially2:
fixes f :: "'a::metric_space => 'b:: topological_space"
shows "continuous (at x0) f <-> (ALL x. (x ----> x0) --> (f o x) ----> (f x0))"
proof-
{ assume "~(continuous (at x0) f)"
  from this obtain T where T_def:
     "open T & f x0 : T & (ALL S. (open S & x0 : S) --> (EX x':S. f x' ~: T))"
     using continuous_at_open[of x0 f] by metis
  def X == "{x'. f x' ~: T}" hence "x0 islimpt X" unfolding islimpt_def using T_def by auto
  from this obtain x where x_def: "(ALL n. x n : X) & x ----> x0"
     using islimpt_sequential[of x0 X] by auto
  hence "~(f o x) ----> (f x0)" unfolding tendsto_explicit using X_def T_def by auto
  hence "EX x. x ----> x0 & (~(f o x) ----> (f x0))" using x_def by auto
}
from this show ?thesis using continuous_imp_tendsto by auto
qed

lemma continuous_at_of_extreal:
  fixes x0 :: extreal
  assumes "\<bar>x0\<bar> \<noteq> \<infinity>"
  shows "continuous (at x0) real"
proof-
{ fix T assume T_def: "open T & real x0 : T"
  def S == "extreal ` T"
  hence "extreal (real x0) : S" using T_def by auto
  hence "x0 : S" using assms extreal_real by auto
  moreover have "open S" using open_extreal S_def T_def by auto
  moreover have "ALL y:S. real y : T" using S_def T_def by auto
  ultimately have "EX S. x0 : S & open S & (ALL y:S. real y : T)" by auto
} from this show ?thesis unfolding continuous_at_open by blast
qed


lemma real_extreal_id: "real o extreal = id"
proof-
{ fix x have "(real o extreal) x = id x" by auto }
from this show ?thesis using ext by blast
qed


lemma continuous_at_iff_extreal:
fixes f :: "'a::t2_space => real"
shows "continuous (at x0) f <-> continuous (at x0) (extreal o f)"
proof-
{ assume "continuous (at x0) f" hence "continuous (at x0) (extreal o f)"
     using continuous_at_extreal continuous_at_compose[of x0 f extreal] by auto
}
moreover
{ assume "continuous (at x0) (extreal o f)"
  hence "continuous (at x0) (real o (extreal o f))"
     using continuous_at_of_extreal by (intro continuous_at_compose[of x0 "extreal o f"]) auto
  moreover have "real o (extreal o f) = f" using real_extreal_id by (simp add: o_assoc)
  ultimately have "continuous (at x0) f" by auto
} ultimately show ?thesis by auto
qed


lemma continuous_on_iff_extreal:
fixes f :: "'a::t2_space => real"
fixes A assumes "open A"
shows "continuous_on A f <-> continuous_on A (extreal o f)"
   using continuous_at_iff_extreal assms by (auto simp add: continuous_on_eq_continuous_at)


lemma open_image_extreal: "open(UNIV-{\<infinity>,(-\<infinity>)})"
by (metis range_extreal open_extreal open_UNIV)

lemma continuous_on_real: "continuous_on (UNIV-{\<infinity>,(-\<infinity>)}) real"
   using continuous_at_of_extreal continuous_on_eq_continuous_at open_image_extreal by auto


lemma continuous_on_iff_real:
  fixes f :: "'a::t2_space => extreal"
  assumes "\<And>x. x \<in> A \<Longrightarrow> \<bar>f x\<bar> \<noteq> \<infinity>"
  shows "continuous_on A f \<longleftrightarrow> continuous_on A (real \<circ> f)"
proof-
  have "f ` A <= UNIV-{\<infinity>,(-\<infinity>)}" using assms by force
  hence *: "continuous_on (f ` A) real"
     using continuous_on_real by (simp add: continuous_on_subset)
have **: "continuous_on ((real o f) ` A) extreal"
   using continuous_on_extreal continuous_on_subset[of "UNIV" "extreal" "(real o f) ` A"] by blast
{ assume "continuous_on A f" hence "continuous_on A (real o f)"
  apply (subst continuous_on_compose) using * by auto
}
moreover
{ assume "continuous_on A (real o f)"
  hence "continuous_on A (extreal o (real o f))"
     apply (subst continuous_on_compose) using ** by auto
  hence "continuous_on A f"
     apply (subst continuous_on_eq[of A "extreal o (real o f)" f])
     using assms extreal_real by auto
}
ultimately show ?thesis by auto
qed


lemma continuous_at_const:
  fixes f :: "'a::t2_space => extreal"
  assumes "ALL x. (f x = C)"
  shows "ALL x. continuous (at x) f"
unfolding continuous_at_open using assms t1_space by auto


lemma closure_contains_Inf:
  fixes S :: "real set"
  assumes "S ~= {}" "EX B. ALL x:S. B<=x"
  shows "Inf S : closure S"
proof-
have *: "ALL x:S. Inf S <= x" using Inf_lower_EX[of _ S] assms by metis
{ fix e assume "e>(0 :: real)"
  from this obtain x where x_def: "x:S & x < Inf S + e" using Inf_close `S ~= {}` by auto
  moreover hence "x > Inf S - e" using * by auto
  ultimately have "abs (x - Inf S) < e" by (simp add: abs_diff_less_iff)
  hence "EX x:S. abs (x - Inf S) < e" using x_def by auto
} from this show ?thesis apply (subst closure_approachable) unfolding dist_norm by auto
qed


lemma closed_contains_Inf:
  fixes S :: "real set"
  assumes "S ~= {}" "EX B. ALL x:S. B<=x"
  assumes "closed S"
  shows "Inf S : S"
by (metis closure_contains_Inf closure_closed assms)


lemma mono_closed_real:
  fixes S :: "real set"
  assumes mono: "ALL y z. y:S & y<=z --> z:S"
  assumes "closed S"
  shows "S = {} | S = UNIV | (EX a. S = {a ..})"
proof-
{ assume "S ~= {}"
  { assume ex: "EX B. ALL x:S. B<=x"
    hence *: "ALL x:S. Inf S <= x" using Inf_lower_EX[of _ S] ex by metis
    hence "Inf S : S" apply (subst closed_contains_Inf) using ex `S ~= {}` `closed S` by auto
    hence "ALL x. (Inf S <= x <-> x:S)" using mono[rule_format, of "Inf S"] * by auto
    hence "S = {Inf S ..}" by auto
    hence "EX a. S = {a ..}" by auto
  }
  moreover
  { assume "~(EX B. ALL x:S. B<=x)"
    hence nex: "ALL B. EX x:S. x<B" by (simp add: not_le)
    { fix y obtain x where "x:S & x < y" using nex by auto
      hence "y:S" using mono[rule_format, of x y] by auto
    } hence "S = UNIV" by auto
  } ultimately have "S = UNIV | (EX a. S = {a ..})" by blast
} from this show ?thesis by blast
qed


lemma mono_closed_extreal:
  fixes S :: "real set"
  assumes mono: "ALL y z. y:S & y<=z --> z:S"
  assumes "closed S"
  shows "EX a. S = {x. a <= extreal x}"
proof-
{ assume "S = {}" hence ?thesis apply(rule_tac x=PInfty in exI) by auto }
moreover
{ assume "S = UNIV" hence ?thesis apply(rule_tac x="-\<infinity>" in exI) by auto }
moreover
{ assume "EX a. S = {a ..}"
  from this obtain a where "S={a ..}" by auto
  hence ?thesis apply(rule_tac x="extreal a" in exI) by auto
} ultimately show ?thesis using mono_closed_real[of S] assms by auto
qed

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

subsection {* Sums *}

lemma setsum_extreal[simp]:
  "(\<Sum>x\<in>A. extreal (f x)) = extreal (\<Sum>x\<in>A. f x)"
proof cases
  assume "finite A" then show ?thesis by induct auto
qed simp

lemma setsum_Pinfty: "(\<Sum>x\<in>P. f x) = \<infinity> \<longleftrightarrow> (finite P \<and> (\<exists>i\<in>P. f i = \<infinity>))"
proof safe
  assume *: "setsum f P = \<infinity>"
  show "finite P"
  proof (rule ccontr) assume "infinite P" with * show False by auto qed
  show "\<exists>i\<in>P. f i = \<infinity>"
  proof (rule ccontr)
    assume "\<not> ?thesis" then have "\<And>i. i \<in> P \<Longrightarrow> f i \<noteq> \<infinity>" by auto
    from `finite P` this have "setsum f P \<noteq> \<infinity>"
      by induct auto
    with * show False by auto
  qed
next
  fix i assume "finite P" "i \<in> P" "f i = \<infinity>"
  thus "setsum f P = \<infinity>"
  proof induct
    case (insert x A)
    show ?case using insert by (cases "x = i") auto
  qed simp
qed

lemma setsum_of_pextreal:
  assumes "\<And>x. x \<in> S \<Longrightarrow> \<bar>f x\<bar> \<noteq> \<infinity>"
  shows "(\<Sum>x\<in>S. real (f x)) = real (setsum f S)"
proof -
  have "\<forall>x\<in>S. \<exists>r. f x = extreal r"
  proof
    fix x assume "x \<in> S"
    from assms[OF this] show "\<exists>r. f x = extreal r" by (cases "f x") auto
  qed
  from bchoice[OF this] guess r ..
  then show ?thesis by simp
qed

lemma setsum_0:
  fixes f :: "'a \<Rightarrow> pextreal" assumes "finite A"
  shows "(\<Sum>x\<in>A. f x) = 0 \<longleftrightarrow> (\<forall>i\<in>A. f i = 0)"
  using assms by induct auto

end
