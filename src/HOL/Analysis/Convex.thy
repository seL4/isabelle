(* Title:      HOL/Analysis/Convex.thy
   Author:     L C Paulson, University of Cambridge
   Author:     Robert Himmelmann, TU Muenchen
   Author:     Bogdan Grechuk, University of Edinburgh
   Author:     Armin Heller, TU Muenchen
   Author:     Johannes Hoelzl, TU Muenchen
*)

section \<open>Convex Sets and Functions\<close>

theory Convex
imports
  Affine  "HOL-Library.Set_Algebras"  "HOL-Library.FuncSet"
begin

subsection \<open>Convex Sets\<close>

definition\<^marker>\<open>tag important\<close> convex :: "'a::real_vector set \<Rightarrow> bool"
  where "convex s \<longleftrightarrow> (\<forall>x\<in>s. \<forall>y\<in>s. \<forall>u\<ge>0. \<forall>v\<ge>0. u + v = 1 \<longrightarrow> u *\<^sub>R x + v *\<^sub>R y \<in> s)"

lemma convexI:
  assumes "\<And>x y u v. x \<in> s \<Longrightarrow> y \<in> s \<Longrightarrow> 0 \<le> u \<Longrightarrow> 0 \<le> v \<Longrightarrow> u + v = 1 \<Longrightarrow> u *\<^sub>R x + v *\<^sub>R y \<in> s"
  shows "convex s"
  by (simp add: assms convex_def)

lemma convexD:
  assumes "convex s" and "x \<in> s" and "y \<in> s" and "0 \<le> u" and "0 \<le> v" and "u + v = 1"
  shows "u *\<^sub>R x + v *\<^sub>R y \<in> s"
  using assms unfolding convex_def by fast

lemma convex_alt: "convex s \<longleftrightarrow> (\<forall>x\<in>s. \<forall>y\<in>s. \<forall>u. 0 \<le> u \<and> u \<le> 1 \<longrightarrow> ((1 - u) *\<^sub>R x + u *\<^sub>R y) \<in> s)"
  (is "_ \<longleftrightarrow> ?alt")
  by (smt (verit) convexD convexI)

lemma convexD_alt:
  assumes "convex s" "a \<in> s" "b \<in> s" "0 \<le> u" "u \<le> 1"
  shows "((1 - u) *\<^sub>R a + u *\<^sub>R b) \<in> s"
  using assms unfolding convex_alt by auto

lemma mem_convex_alt:
  assumes "convex S" "x \<in> S" "y \<in> S" "u \<ge> 0" "v \<ge> 0" "u + v > 0"
  shows "((u/(u+v)) *\<^sub>R x + (v/(u+v)) *\<^sub>R y) \<in> S"
  using assms
  by (simp add: convex_def zero_le_divide_iff add_divide_distrib [symmetric])

lemma convex_empty[intro,simp]: "convex {}"
  unfolding convex_def by simp

lemma convex_singleton[intro,simp]: "convex {a}"
  unfolding convex_def by (auto simp: scaleR_left_distrib[symmetric])

lemma convex_UNIV[intro,simp]: "convex UNIV"
  unfolding convex_def by auto

lemma convex_Inter: "(\<And>s. s\<in>f \<Longrightarrow> convex s) \<Longrightarrow> convex(\<Inter>f)"
  unfolding convex_def by auto

lemma convex_Int: "convex s \<Longrightarrow> convex t \<Longrightarrow> convex (s \<inter> t)"
  unfolding convex_def by auto

lemma convex_INT: "(\<And>i. i \<in> A \<Longrightarrow> convex (B i)) \<Longrightarrow> convex (\<Inter>i\<in>A. B i)"
  unfolding convex_def by auto

lemma convex_Times: "convex s \<Longrightarrow> convex t \<Longrightarrow> convex (s \<times> t)"
  unfolding convex_def by auto

lemma convex_halfspace_le: "convex {x. inner a x \<le> b}"
  unfolding convex_def
  by (auto simp: inner_add intro!: convex_bound_le)

lemma convex_halfspace_ge: "convex {x. inner a x \<ge> b}"
proof -
  have *: "{x. inner a x \<ge> b} = {x. inner (-a) x \<le> -b}"
    by auto
  show ?thesis
    unfolding * using convex_halfspace_le[of "-a" "-b"] by auto
qed

lemma convex_halfspace_abs_le: "convex {x. \<bar>inner a x\<bar> \<le> b}"
proof -
  have *: "{x. \<bar>inner a x\<bar> \<le> b} = {x. inner a x \<le> b} \<inter> {x. -b \<le> inner a x}"
    by auto
  show ?thesis
    unfolding * by (simp add: convex_Int convex_halfspace_ge convex_halfspace_le)
qed

lemma convex_hyperplane: "convex {x. inner a x = b}"
proof -
  have *: "{x. inner a x = b} = {x. inner a x \<le> b} \<inter> {x. inner a x \<ge> b}"
    by auto
  show ?thesis using convex_halfspace_le convex_halfspace_ge
    by (auto intro!: convex_Int simp: *)
qed

lemma convex_halfspace_lt: "convex {x. inner a x < b}"
  unfolding convex_def
  by (auto simp: convex_bound_lt inner_add)

lemma convex_halfspace_gt: "convex {x. inner a x > b}"
  using convex_halfspace_lt[of "-a" "-b"] by auto

lemma convex_halfspace_Re_ge: "convex {x. Re x \<ge> b}"
  using convex_halfspace_ge[of b "1::complex"] by simp

lemma convex_halfspace_Re_le: "convex {x. Re x \<le> b}"
  using convex_halfspace_le[of "1::complex" b] by simp

lemma convex_halfspace_Im_ge: "convex {x. Im x \<ge> b}"
  using convex_halfspace_ge[of b \<i>] by simp

lemma convex_halfspace_Im_le: "convex {x. Im x \<le> b}"
  using convex_halfspace_le[of \<i> b] by simp

lemma convex_halfspace_Re_gt: "convex {x. Re x > b}"
  using convex_halfspace_gt[of b "1::complex"] by simp

lemma convex_halfspace_Re_lt: "convex {x. Re x < b}"
  using convex_halfspace_lt[of "1::complex" b] by simp

lemma convex_halfspace_Im_gt: "convex {x. Im x > b}"
  using convex_halfspace_gt[of b \<i>] by simp

lemma convex_halfspace_Im_lt: "convex {x. Im x < b}"
  using convex_halfspace_lt[of \<i> b] by simp

lemma convex_real_interval [iff]:
  fixes a b :: "real"
  shows "convex {a..}" and "convex {..b}"
    and "convex {a<..}" and "convex {..<b}"
    and "convex {a..b}" and "convex {a<..b}"
    and "convex {a..<b}" and "convex {a<..<b}"
proof -
  have "{a..} = {x. a \<le> inner 1 x}"
    by auto
  then show 1: "convex {a..}"
    by (simp only: convex_halfspace_ge)
  have "{..b} = {x. inner 1 x \<le> b}"
    by auto
  then show 2: "convex {..b}"
    by (simp only: convex_halfspace_le)
  have "{a<..} = {x. a < inner 1 x}"
    by auto
  then show 3: "convex {a<..}"
    by (simp only: convex_halfspace_gt)
  have "{..<b} = {x. inner 1 x < b}"
    by auto
  then show 4: "convex {..<b}"
    by (simp only: convex_halfspace_lt)
  have "{a..b} = {a..} \<inter> {..b}"
    by auto
  then show "convex {a..b}"
    by (simp only: convex_Int 1 2)
  have "{a<..b} = {a<..} \<inter> {..b}"
    by auto
  then show "convex {a<..b}"
    by (simp only: convex_Int 3 2)
  have "{a..<b} = {a..} \<inter> {..<b}"
    by auto
  then show "convex {a..<b}"
    by (simp only: convex_Int 1 4)
  have "{a<..<b} = {a<..} \<inter> {..<b}"
    by auto
  then show "convex {a<..<b}"
    by (simp only: convex_Int 3 4)
qed

lemma convex_Reals: "convex \<real>"
  by (simp add: convex_def scaleR_conv_of_real)


subsection\<^marker>\<open>tag unimportant\<close> \<open>Explicit expressions for convexity in terms of arbitrary sums\<close>

lemma convex_sum:
  fixes C :: "'a::real_vector set"
  assumes "finite S"
    and "convex C"
    and a: "(\<Sum> i \<in> S. a i) = 1" "\<And>i. i \<in> S \<Longrightarrow> a i \<ge> 0"
    and C: "\<And>i. i \<in> S \<Longrightarrow> y i \<in> C"
  shows "(\<Sum> j \<in> S. a j *\<^sub>R y j) \<in> C"
  using \<open>finite S\<close> a C
proof (induction arbitrary: a set: finite)
  case empty
  then show ?case by simp
next
  case (insert i S) 
  then have "0 \<le> sum a S"
    by (simp add: sum_nonneg)
  have "a i *\<^sub>R y i + (\<Sum>j\<in>S. a j *\<^sub>R y j) \<in> C"
  proof (cases "sum a S = 0")
    case True with insert show ?thesis
      by (simp add: sum_nonneg_eq_0_iff)
  next
    case False
    with \<open>0 \<le> sum a S\<close> have "0 < sum a S"
      by simp
    then have "(\<Sum>j\<in>S. (a j / sum a S) *\<^sub>R y j) \<in> C"
      using insert
      by (simp add: insert.IH flip: sum_divide_distrib)
    with \<open>convex C\<close> insert \<open>0 \<le> sum a S\<close> 
    have "a i *\<^sub>R y i + sum a S *\<^sub>R (\<Sum>j\<in>S. (a j / sum a S) *\<^sub>R y j) \<in> C"
      by (simp add: convex_def)
    then show ?thesis
      by (simp add: scaleR_sum_right False)
  qed
  then show ?case using \<open>finite S\<close> and \<open>i \<notin> S\<close>
    by simp
qed

lemma convex:
  "convex S \<longleftrightarrow> 
    (\<forall>(k::nat) u x. (\<forall>i. 1\<le>i \<and> i\<le>k \<longrightarrow> 0 \<le> u i \<and> x i \<in>S) \<and> (sum u {1..k} = 1)
      \<longrightarrow> sum (\<lambda>i. u i *\<^sub>R x i) {1..k} \<in> S)"  
  (is "?lhs = ?rhs")
proof
  show "?lhs \<Longrightarrow> ?rhs"
    by (metis (full_types) atLeastAtMost_iff convex_sum finite_atLeastAtMost)
  assume *: "\<forall>k u x. (\<forall> i :: nat. 1 \<le> i \<and> i \<le> k \<longrightarrow> 0 \<le> u i \<and> x i \<in> S) \<and> sum u {1..k} = 1
    \<longrightarrow> (\<Sum>i = 1..k. u i *\<^sub>R (x i :: 'a)) \<in> S"
  {
    fix \<mu> :: real
    fix x y :: 'a
    assume xy: "x \<in> S" "y \<in> S"
    assume mu: "\<mu> \<ge> 0" "\<mu> \<le> 1"
    let ?u = "\<lambda>i. if (i :: nat) = 1 then \<mu> else 1 - \<mu>"
    let ?x = "\<lambda>i. if (i :: nat) = 1 then x else y"
    have "{1 :: nat .. 2} \<inter> - {x. x = 1} = {2}"
      by auto
    then have S: "(\<Sum>j \<in> {1..2}. ?u j *\<^sub>R ?x j) \<in> S"
      using sum.If_cases[of "{(1 :: nat) .. 2}" "\<lambda>x. x = 1" "\<lambda>x. \<mu>" "\<lambda>x. 1 - \<mu>"]
      using mu xy "*" by auto
    have grarr: "(\<Sum>j \<in> {Suc (Suc 0)..2}. ?u j *\<^sub>R ?x j) = (1 - \<mu>) *\<^sub>R y"
      using sum.atLeast_Suc_atMost[of "Suc (Suc 0)" 2 "\<lambda> j. (1 - \<mu>) *\<^sub>R y"] by auto
    with sum.atLeast_Suc_atMost
    have "(\<Sum>j \<in> {1..2}. ?u j *\<^sub>R ?x j) = \<mu> *\<^sub>R x + (1 - \<mu>) *\<^sub>R y"
      by (smt (verit, best) Suc_1 Suc_eq_plus1 add_0 le_add1)
    then have "(1 - \<mu>) *\<^sub>R y + \<mu> *\<^sub>R x \<in> S"
      using S by (auto simp: add.commute)
  }
  then show "convex S"
    unfolding convex_alt by auto
qed


lemma convex_explicit:
  fixes S :: "'a::real_vector set"
  shows "convex S \<longleftrightarrow>
    (\<forall>t u. finite t \<and> t \<subseteq> S \<and> (\<forall>x\<in>t. 0 \<le> u x) \<and> sum u t = 1 \<longrightarrow> sum (\<lambda>x. u x *\<^sub>R x) t \<in> S)"
proof safe
  fix t
  fix u :: "'a \<Rightarrow> real"
  assume "convex S"
    and "finite t"
    and "t \<subseteq> S" "\<forall>x\<in>t. 0 \<le> u x" "sum u t = 1"
  then show "(\<Sum>x\<in>t. u x *\<^sub>R x) \<in> S"
    by (simp add: convex_sum subsetD)
next
  assume *: "\<forall>t. \<forall> u. finite t \<and> t \<subseteq> S \<and> (\<forall>x\<in>t. 0 \<le> u x) \<and>
    sum u t = 1 \<longrightarrow> (\<Sum>x\<in>t. u x *\<^sub>R x) \<in> S"
  show "convex S"
    unfolding convex_alt
  proof safe
    fix x y
    fix \<mu> :: real
    assume **: "x \<in> S" "y \<in> S" "0 \<le> \<mu>" "\<mu> \<le> 1"
    show "(1 - \<mu>) *\<^sub>R x + \<mu> *\<^sub>R y \<in> S"
    proof (cases "x = y")
      case False
      then show ?thesis
        using *[rule_format, of "{x, y}" "\<lambda> z. if z = x then 1 - \<mu> else \<mu>"] **
        by auto
    next
      case True
      then show ?thesis
        using *[rule_format, of "{x, y}" "\<lambda> z. 1"] **
        by (auto simp: field_simps real_vector.scale_left_diff_distrib)
    qed
  qed
qed

lemma convex_finite:
  assumes "finite S"
  shows "convex S \<longleftrightarrow> (\<forall>u. (\<forall>x\<in>S. 0 \<le> u x) \<and> sum u S = 1 \<longrightarrow> sum (\<lambda>x. u x *\<^sub>R x) S \<in> S)"
       (is "?lhs = ?rhs")
proof 
  { have if_distrib_arg: "\<And>P f g x. (if P then f else g) x = (if P then f x else g x)"
      by simp
    fix T :: "'a set" and u :: "'a \<Rightarrow> real"
    assume sum: "\<forall>u. (\<forall>x\<in>S. 0 \<le> u x) \<and> sum u S = 1 \<longrightarrow> (\<Sum>x\<in>S. u x *\<^sub>R x) \<in> S"
    assume *: "\<forall>x\<in>T. 0 \<le> u x" "sum u T = 1"
    assume "T \<subseteq> S"
    then have "S \<inter> T = T" by auto
    with sum[THEN spec[where x="\<lambda>x. if x\<in>T then u x else 0"]] *
    have "(\<Sum>x\<in>T. u x *\<^sub>R x) \<in> S"
      by (auto simp: assms sum.If_cases if_distrib if_distrib_arg) }
  moreover assume ?rhs
  ultimately show ?lhs
    unfolding convex_explicit by auto
qed (auto simp: convex_explicit assms)

subsection \<open>Convex Functions on a Set\<close>

definition\<^marker>\<open>tag important\<close> convex_on :: "'a::real_vector set \<Rightarrow> ('a \<Rightarrow> real) \<Rightarrow> bool"
  where "convex_on S f \<longleftrightarrow> convex S \<and>
    (\<forall>x\<in>S. \<forall>y\<in>S. \<forall>u\<ge>0. \<forall>v\<ge>0. u + v = 1 \<longrightarrow> f (u *\<^sub>R x + v *\<^sub>R y) \<le> u * f x + v * f y)"

definition\<^marker>\<open>tag important\<close> concave_on :: "'a::real_vector set \<Rightarrow> ('a \<Rightarrow> real) \<Rightarrow> bool"
  where "concave_on S f \<equiv> convex_on S (\<lambda>x. - f x)"

lemma convex_on_iff_concave: "convex_on S f = concave_on S (\<lambda>x. - f x)"
  by (simp add: concave_on_def)

lemma concave_on_iff:
  "concave_on S f \<longleftrightarrow> convex S \<and>
    (\<forall>x\<in>S. \<forall>y\<in>S. \<forall>u\<ge>0. \<forall>v\<ge>0. u + v = 1 \<longrightarrow> f (u *\<^sub>R x + v *\<^sub>R y) \<ge> u * f x + v * f y)"
  by (auto simp: concave_on_def convex_on_def algebra_simps)

lemma concave_onD:
  assumes "concave_on A f"
  shows "\<And>t x y. t \<ge> 0 \<Longrightarrow> t \<le> 1 \<Longrightarrow> x \<in> A \<Longrightarrow> y \<in> A \<Longrightarrow>
    f ((1 - t) *\<^sub>R x + t *\<^sub>R y) \<ge> (1 - t) * f x + t * f y"
  using assms by (auto simp: concave_on_iff)

lemma convex_onI [intro?]:
  assumes "\<And>t x y. t > 0 \<Longrightarrow> t < 1 \<Longrightarrow> x \<in> A \<Longrightarrow> y \<in> A \<Longrightarrow>
    f ((1 - t) *\<^sub>R x + t *\<^sub>R y) \<le> (1 - t) * f x + t * f y"
    and "convex A"
  shows "convex_on A f"
  unfolding convex_on_def
  by (smt (verit, del_insts) assms mult_cancel_right1 mult_eq_0_iff scaleR_collapse scaleR_eq_0_iff)

lemma convex_onD:
  assumes "convex_on A f"
  shows "\<And>t x y. t \<ge> 0 \<Longrightarrow> t \<le> 1 \<Longrightarrow> x \<in> A \<Longrightarrow> y \<in> A \<Longrightarrow>
    f ((1 - t) *\<^sub>R x + t *\<^sub>R y) \<le> (1 - t) * f x + t * f y"
  using assms by (auto simp: convex_on_def)

lemma convex_on_linorderI [intro?]:
  fixes A :: "('a::{linorder,real_vector}) set"
  assumes "\<And>t x y. t > 0 \<Longrightarrow> t < 1 \<Longrightarrow> x \<in> A \<Longrightarrow> y \<in> A \<Longrightarrow> x < y \<Longrightarrow>
    f ((1 - t) *\<^sub>R x + t *\<^sub>R y) \<le> (1 - t) * f x + t * f y"
    and "convex A"
  shows "convex_on A f"
  by (smt (verit, best) add.commute assms convex_onI distrib_left linorder_cases mult.commute mult_cancel_left2 scaleR_collapse)

lemma concave_on_linorderI [intro?]:
  fixes A :: "('a::{linorder,real_vector}) set"
  assumes "\<And>t x y. t > 0 \<Longrightarrow> t < 1 \<Longrightarrow> x \<in> A \<Longrightarrow> y \<in> A \<Longrightarrow> x < y \<Longrightarrow>
    f ((1 - t) *\<^sub>R x + t *\<^sub>R y) \<ge> (1 - t) * f x + t * f y"
    and "convex A"
  shows "concave_on A f"
  by (smt (verit) assms concave_on_def convex_on_linorderI mult_minus_right)

lemma convex_on_imp_convex: "convex_on A f \<Longrightarrow> convex A"
  by (auto simp: convex_on_def)

lemma concave_on_imp_convex: "concave_on A f \<Longrightarrow> convex A"
  by (simp add: concave_on_def convex_on_imp_convex)

lemma convex_onD_Icc:
  assumes "convex_on {x..y} f" "x \<le> (y :: _ :: {real_vector,preorder})"
  shows "\<And>t. t \<ge> 0 \<Longrightarrow> t \<le> 1 \<Longrightarrow>
    f ((1 - t) *\<^sub>R x + t *\<^sub>R y) \<le> (1 - t) * f x + t * f y"
  using assms(2) by (intro convex_onD [OF assms(1)]) simp_all

lemma convex_on_subset: "\<lbrakk>convex_on T f; S \<subseteq> T; convex S\<rbrakk> \<Longrightarrow> convex_on S f"
  by (simp add: convex_on_def subset_iff)

lemma convex_on_add [intro]:
  assumes "convex_on S f"
    and "convex_on S g"
  shows "convex_on S (\<lambda>x. f x + g x)"
proof -
  {
    fix x y
    assume "x \<in> S" "y \<in> S"
    moreover
    fix u v :: real
    assume "0 \<le> u" "0 \<le> v" "u + v = 1"
    ultimately
    have "f (u *\<^sub>R x + v *\<^sub>R y) + g (u *\<^sub>R x + v *\<^sub>R y) \<le> (u * f x + v * f y) + (u * g x + v * g y)"
      using assms unfolding convex_on_def by (auto simp: add_mono)
    then have "f (u *\<^sub>R x + v *\<^sub>R y) + g (u *\<^sub>R x + v *\<^sub>R y) \<le> u * (f x + g x) + v * (f y + g y)"
      by (simp add: field_simps)
  }
  with assms show ?thesis
    unfolding convex_on_def by auto
qed

lemma convex_on_ident: "convex_on S (\<lambda>x. x) \<longleftrightarrow> convex S"
  by (simp add: convex_on_def)

lemma concave_on_ident: "concave_on S (\<lambda>x. x) \<longleftrightarrow> convex S"
  by (simp add: concave_on_iff)

lemma convex_on_const: "convex_on S (\<lambda>x. a) \<longleftrightarrow> convex S"
  by (simp add: convex_on_def flip: distrib_right)

lemma concave_on_const: "concave_on S (\<lambda>x. a) \<longleftrightarrow> convex S"
  by (simp add: concave_on_iff flip: distrib_right)

lemma convex_on_diff:
  assumes "convex_on S f" and "concave_on S g"
  shows "convex_on S (\<lambda>x. f x - g x)"
  using assms concave_on_def convex_on_add by fastforce

lemma concave_on_diff:
  assumes "concave_on S f"
    and "convex_on S g"
  shows "concave_on S (\<lambda>x. f x - g x)"
  using convex_on_diff assms concave_on_def by fastforce

lemma concave_on_add:
  assumes "concave_on S f"
    and "concave_on S g"
  shows "concave_on S (\<lambda>x. f x + g x)"
  using assms convex_on_iff_concave concave_on_diff concave_on_def by fastforce

lemma convex_on_mul:
  fixes S::"real set"
  assumes "convex_on S f" "convex_on S g"
  assumes "mono_on S f" "mono_on S g"
  assumes fty: "f \<in> S \<rightarrow> {0..}" and gty: "g \<in> S \<rightarrow> {0..}"
  shows "convex_on S (\<lambda>x. f x*g x)"
proof (intro convex_on_linorderI)
  show "convex S"
    using assms convex_on_imp_convex by auto
  fix t::real and x y
  assume t: "0 < t" "t < 1" and xy: "x \<in> S" "y \<in> S" "x<y"
  have *: "t*(1-t) * f x * g y + t*(1-t) * f y * g x \<le> t*(1-t) * f x * g x + t*(1-t) * f y * g y"
    using t \<open>mono_on S f\<close> \<open>mono_on S g\<close> xy
    by (smt (verit, ccfv_SIG) left_diff_distrib mono_onD mult_left_less_imp_less zero_le_mult_iff)
  have inS: "(1-t)*x + t*y \<in> S"
    using t xy \<open>convex S\<close> by (simp add: convex_alt)
  then have "f ((1-t)*x + t*y) * g ((1-t)*x + t*y) \<le> ((1-t) * f x + t * f y)*g ((1-t)*x + t*y)"
    using convex_onD [OF \<open>convex_on S f\<close>, of t x y] t xy fty gty
    by (intro mult_mono add_nonneg_nonneg) (auto simp: Pi_iff zero_le_mult_iff)
  also have "\<dots> \<le> ((1-t) * f x + t * f y) * ((1-t)*g x + t*g y)"
    using convex_onD [OF \<open>convex_on S g\<close>, of t x y] t xy fty gty inS
    by (intro mult_mono add_nonneg_nonneg) (auto simp: Pi_iff zero_le_mult_iff)
  also have "\<dots> \<le> (1-t) * (f x*g x) + t * (f y*g y)"
    using * by (simp add: algebra_simps)
  finally show "f ((1-t) *\<^sub>R x + t *\<^sub>R y) * g ((1-t) *\<^sub>R x + t *\<^sub>R y) \<le> (1-t)*(f x*g x) + t*(f y*g y)" 
    by simp
qed

lemma convex_on_cmul [intro]:
  fixes c :: real
  assumes "0 \<le> c"
    and "convex_on S f"
  shows "convex_on S (\<lambda>x. c * f x)"
proof -
  have *: "u * (c * fx) + v * (c * fy) = c * (u * fx + v * fy)"
    for u c fx v fy :: real
    by (simp add: field_simps)
  show ?thesis using assms(2) and mult_left_mono [OF _ assms(1)]
    unfolding convex_on_def and * by auto
qed

lemma convex_on_cdiv [intro]:
  fixes c :: real
  assumes "0 \<le> c" and "convex_on S f"
  shows "convex_on S (\<lambda>x. f x / c)"
  unfolding divide_inverse
  using convex_on_cmul [of "inverse c" S f] by (simp add: mult.commute assms)

lemma convex_lower:
  assumes "convex_on S f"
    and "x \<in> S"
    and "y \<in> S"
    and "0 \<le> u"
    and "0 \<le> v"
    and "u + v = 1"
  shows "f (u *\<^sub>R x + v *\<^sub>R y) \<le> max (f x) (f y)"
proof -
  let ?m = "max (f x) (f y)"
  have "u * f x + v * f y \<le> u * max (f x) (f y) + v * max (f x) (f y)"
    using assms(4,5) by (auto simp: mult_left_mono add_mono)
  also have "\<dots> = max (f x) (f y)"
    using assms(6) by (simp add: distrib_right [symmetric])
  finally show ?thesis
    using assms unfolding convex_on_def by fastforce
qed

lemma convex_on_dist [intro]:
  fixes S :: "'a::real_normed_vector set"
  assumes "convex S"
  shows "convex_on S (\<lambda>x. dist a x)"
unfolding convex_on_def dist_norm
proof (intro conjI strip)
  fix x y
  assume "x \<in> S" "y \<in> S"
  fix u v :: real
  assume "0 \<le> u"
  assume "0 \<le> v"
  assume "u + v = 1"
  have "a = u *\<^sub>R a + v *\<^sub>R a"
    by (metis \<open>u + v = 1\<close> scaleR_left.add scaleR_one)
  then have "a - (u *\<^sub>R x + v *\<^sub>R y) = (u *\<^sub>R (a - x)) + (v *\<^sub>R (a - y))"
    by (auto simp: algebra_simps)
  then show "norm (a - (u *\<^sub>R x + v *\<^sub>R y)) \<le> u * norm (a - x) + v * norm (a - y)"
    by (smt (verit, best) \<open>0 \<le> u\<close> \<open>0 \<le> v\<close> norm_scaleR norm_triangle_ineq)
qed (use assms in auto)

lemma concave_on_mul:
  fixes S::"real set"
  assumes f: "concave_on S f" and g: "concave_on S g"
  assumes "mono_on S f" "antimono_on S g"
  assumes fty: "f \<in> S \<rightarrow> {0..}" and gty: "g \<in> S \<rightarrow> {0..}"
  shows "concave_on S (\<lambda>x. f x * g x)"
proof (intro concave_on_linorderI)
  show "convex S"
    using concave_on_imp_convex f by blast
  fix t::real and x y
  assume t: "0 < t" "t < 1" and xy: "x \<in> S" "y \<in> S" "x<y"
  have inS: "(1-t)*x + t*y \<in> S"
    using t xy \<open>convex S\<close> by (simp add: convex_alt)
  have "f x * g y + f y * g x \<ge> f x * g x + f y * g y"
    using \<open>mono_on S f\<close> \<open>antimono_on S g\<close>
    unfolding monotone_on_def by (smt (verit, best) left_diff_distrib mult_left_mono xy)
  with t have *: "t*(1-t) * f x * g y + t*(1-t) * f y * g x \<ge> t*(1-t) * f x * g x + t*(1-t) * f y * g y"
    by (smt (verit, ccfv_SIG) distrib_left mult_left_mono diff_ge_0_iff_ge mult.assoc)
  have "(1 - t) * (f x * g x) + t * (f y * g y) \<le> ((1-t) * f x + t * f y) * ((1-t) * g x + t * g y)"
    using * by (simp add: algebra_simps)
  also have "\<dots> \<le> ((1-t) * f x + t * f y)*g ((1-t)*x + t*y)"
    using concave_onD [OF \<open>concave_on S g\<close>, of t x y] t xy fty gty inS
    by (intro mult_mono add_nonneg_nonneg) (auto simp: Pi_iff zero_le_mult_iff)
  also have "\<dots> \<le> f ((1-t)*x + t*y) * g ((1-t)*x + t*y)"
    using concave_onD [OF \<open>concave_on S f\<close>, of t x y] t xy fty gty inS
    by (intro mult_mono add_nonneg_nonneg) (auto simp: Pi_iff zero_le_mult_iff)
  finally show "(1 - t) * (f x * g x) + t * (f y * g y)
           \<le> f ((1 - t) *\<^sub>R x + t *\<^sub>R y) * g ((1 - t) *\<^sub>R x + t *\<^sub>R y)" 
    by simp
qed

lemma concave_on_cmul [intro]:
  fixes c :: real
  assumes "0 \<le> c" and "concave_on S f"
  shows "concave_on S (\<lambda>x. c * f x)"
  using assms convex_on_cmul [of c S "\<lambda>x. - f x"]
  by (auto simp: concave_on_def)

lemma concave_on_cdiv [intro]:
  fixes c :: real
  assumes "0 \<le> c" and "concave_on S f"
  shows "concave_on S (\<lambda>x. f x / c)"
  unfolding divide_inverse
  using concave_on_cmul [of "inverse c" S f] by (simp add: mult.commute assms)

subsection\<^marker>\<open>tag unimportant\<close> \<open>Arithmetic operations on sets preserve convexity\<close>

lemma convex_linear_image:
  assumes "linear f" and "convex S"
  shows "convex (f ` S)"
proof -
  interpret f: linear f by fact
  from \<open>convex S\<close> show "convex (f ` S)"
    by (simp add: convex_def f.scaleR [symmetric] f.add [symmetric])
qed

lemma convex_linear_vimage:
  assumes "linear f" and "convex S"
  shows "convex (f -` S)"
proof -
  interpret f: linear f by fact
  from \<open>convex S\<close> show "convex (f -` S)"
    by (simp add: convex_def f.add f.scaleR)
qed

lemma convex_scaling:
  assumes "convex S"
  shows "convex ((\<lambda>x. c *\<^sub>R x) ` S)"
  by (simp add: assms convex_linear_image)

lemma convex_scaled:
  assumes "convex S"
  shows "convex ((\<lambda>x. x *\<^sub>R c) ` S)"
  by (simp add: assms convex_linear_image)

lemma convex_negations:
  assumes "convex S"
  shows "convex ((\<lambda>x. - x) ` S)"
  by (simp add: assms convex_linear_image module_hom_uminus)

lemma convex_sums:
  assumes "convex S"
    and "convex T"
  shows "convex (\<Union>x\<in> S. \<Union>y \<in> T. {x + y})"
proof -
  have "linear (\<lambda>(x, y). x + y)"
    by (auto intro: linearI simp: scaleR_add_right)
  with assms have "convex ((\<lambda>(x, y). x + y) ` (S \<times> T))"
    by (intro convex_linear_image convex_Times)
  also have "((\<lambda>(x, y). x + y) ` (S \<times> T)) = (\<Union>x\<in> S. \<Union>y \<in> T. {x + y})"
    by auto
  finally show ?thesis .
qed

lemma convex_differences:
  assumes "convex S" "convex T"
  shows "convex (\<Union>x\<in> S. \<Union>y \<in> T. {x - y})"
proof -
  have "{x - y| x y. x \<in> S \<and> y \<in> T} = {x + y |x y. x \<in> S \<and> y \<in> uminus ` T}"
    by (auto simp: diff_conv_add_uminus simp del: add_uminus_conv_diff)
  then show ?thesis
    using convex_sums[OF assms(1) convex_negations[OF assms(2)]] by auto
qed

lemma convex_translation:
  "convex ((+) a ` S)" if "convex S"
proof -
  have "(\<Union> x\<in> {a}. \<Union>y \<in> S. {x + y}) = (+) a ` S"
    by auto
  then show ?thesis
    using convex_sums [OF convex_singleton [of a] that] by auto
qed

lemma convex_translation_subtract:
  "convex ((\<lambda>b. b - a) ` S)" if "convex S"
  using convex_translation [of S "- a"] that by (simp cong: image_cong_simp)

lemma convex_affinity:
  assumes "convex S"
  shows "convex ((\<lambda>x. a + c *\<^sub>R x) ` S)"
proof -
  have "(\<lambda>x. a + c *\<^sub>R x) ` S = (+) a ` (*\<^sub>R) c ` S"
    by auto
  then show ?thesis
    using convex_translation[OF convex_scaling[OF assms], of a c] by auto
qed

lemma convex_on_sum:
  fixes a :: "'a \<Rightarrow> real"
    and y :: "'a \<Rightarrow> 'b::real_vector"
    and f :: "'b \<Rightarrow> real"
  assumes "finite S" "S \<noteq> {}"
    and "convex_on C f"
    and "(\<Sum> i \<in> S. a i) = 1"
    and "\<And>i. i \<in> S \<Longrightarrow> a i \<ge> 0"
    and "\<And>i. i \<in> S \<Longrightarrow> y i \<in> C"
  shows "f (\<Sum> i \<in> S. a i *\<^sub>R y i) \<le> (\<Sum> i \<in> S. a i * f (y i))"
  using assms
proof (induct S arbitrary: a rule: finite_ne_induct)
  case (singleton i)
  then show ?case
    by auto
next
  case (insert i S)
  then have yai: "y i \<in> C" "a i \<ge> 0"
    by auto
  with insert have conv: "\<And>x y \<mu>. x \<in> C \<Longrightarrow> y \<in> C \<Longrightarrow> 0 \<le> \<mu> \<Longrightarrow> \<mu> \<le> 1 \<Longrightarrow>
      f (\<mu> *\<^sub>R x + (1 - \<mu>) *\<^sub>R y) \<le> \<mu> * f x + (1 - \<mu>) * f y"
    by (simp add: convex_on_def)
  show ?case
  proof (cases "a i = 1")
    case True
    with insert have "(\<Sum> j \<in> S. a j) = 0"
      by auto
    with insert show ?thesis
      by (simp add: sum_nonneg_eq_0_iff)
  next
    case False
    then have ai1: "a i < 1"
      using sum_nonneg_leq_bound[of "insert i S" a] insert by force
    then have i0: "1 - a i > 0"
      by auto
    let ?a = "\<lambda>j. a j / (1 - a i)"
    have a_nonneg: "?a j \<ge> 0" if "j \<in> S" for j
      using i0 insert that by fastforce
    have "(\<Sum> j \<in> insert i S. a j) = 1"
      using insert by auto
    then have "(\<Sum> j \<in> S. a j) = 1 - a i"
      using sum.insert insert by fastforce
    then have "(\<Sum> j \<in> S. a j) / (1 - a i) = 1"
      using i0 by auto
    then have a1: "(\<Sum> j \<in> S. ?a j) = 1"
      unfolding sum_divide_distrib by simp
    have "convex C"
      using \<open>convex_on C f\<close> by (simp add: convex_on_def)
    have asum: "(\<Sum> j \<in> S. ?a j *\<^sub>R y j) \<in> C"
      using insert convex_sum [OF \<open>finite S\<close> \<open>convex C\<close> a1 a_nonneg] by auto
    have asum_le: "f (\<Sum> j \<in> S. ?a j *\<^sub>R y j) \<le> (\<Sum> j \<in> S. ?a j * f (y j))"
      using a_nonneg a1 insert by blast
    have "f (\<Sum> j \<in> insert i S. a j *\<^sub>R y j) = f ((\<Sum> j \<in> S. a j *\<^sub>R y j) + a i *\<^sub>R y i)"
      by (simp add: add.commute insert.hyps)
    also have "\<dots> = f (((1 - a i) * inverse (1 - a i)) *\<^sub>R (\<Sum> j \<in> S. a j *\<^sub>R y j) + a i *\<^sub>R y i)"
      using i0 by auto
    also have "\<dots> = f ((1 - a i) *\<^sub>R (\<Sum> j \<in> S. (a j * inverse (1 - a i)) *\<^sub>R y j) + a i *\<^sub>R y i)"
      using scaleR_right.sum[of "inverse (1 - a i)" "\<lambda> j. a j *\<^sub>R y j" S, symmetric]
      by (auto simp: algebra_simps)
    also have "\<dots> = f ((1 - a i) *\<^sub>R (\<Sum> j \<in> S. ?a j *\<^sub>R y j) + a i *\<^sub>R y i)"
      by (auto simp: divide_inverse)
    also have "\<dots> \<le> (1 - a i) *\<^sub>R f ((\<Sum> j \<in> S. ?a j *\<^sub>R y j)) + a i * f (y i)"
      using ai1 by (smt (verit) asum conv real_scaleR_def yai)
    also have "\<dots> \<le> (1 - a i) * (\<Sum> j \<in> S. ?a j * f (y j)) + a i * f (y i)"
      using asum_le i0 by fastforce
    also have "\<dots> = (\<Sum> j \<in> S. a j * f (y j)) + a i * f (y i)"
      using i0 by (auto simp: sum_distrib_left)
    finally show ?thesis
      using insert by auto
  qed
qed

lemma concave_on_sum:
  fixes a :: "'a \<Rightarrow> real"
    and y :: "'a \<Rightarrow> 'b::real_vector"
    and f :: "'b \<Rightarrow> real"
  assumes "finite S" "S \<noteq> {}"
    and "concave_on C f" 
    and "(\<Sum>i \<in> S. a i) = 1"
    and "\<And>i. i \<in> S \<Longrightarrow> a i \<ge> 0"
    and "\<And>i. i \<in> S \<Longrightarrow> y i \<in> C"
  shows "f (\<Sum>i \<in> S. a i *\<^sub>R y i) \<ge> (\<Sum>i \<in> S. a i * f (y i))"
proof -
  have "(uminus \<circ> f) (\<Sum>i\<in>S. a i *\<^sub>R y i) \<le> (\<Sum>i\<in>S. a i * (uminus \<circ> f) (y i))"
  proof (intro convex_on_sum)
    show "convex_on C (uminus \<circ> f)"
      by (simp add: assms convex_on_iff_concave)
  qed (use assms in auto)
  then show ?thesis
    by (simp add: sum_negf o_def)
qed

lemma convex_on_alt:
  fixes C :: "'a::real_vector set"
  shows "convex_on C f \<longleftrightarrow> convex C \<and>
         (\<forall>x \<in> C. \<forall>y \<in> C. \<forall> \<mu> :: real. \<mu> \<ge> 0 \<and> \<mu> \<le> 1 \<longrightarrow>
          f (\<mu> *\<^sub>R x + (1 - \<mu>) *\<^sub>R y) \<le> \<mu> * f x + (1 - \<mu>) * f y)"
  by (smt (verit) convex_on_def)

lemma convex_on_slope_le:
  fixes f :: "real \<Rightarrow> real"
  assumes f: "convex_on I f"
    and I: "x \<in> I" "y \<in> I"
    and t: "x < t" "t < y"
  shows "(f x - f t) / (x - t) \<le> (f x - f y) / (x - y)"
    and "(f x - f y) / (x - y) \<le> (f t - f y) / (t - y)"
proof -
  define a where "a \<equiv> (t - y) / (x - y)"
  with t have "0 \<le> a" "0 \<le> 1 - a"
    by (auto simp: field_simps)
  with f \<open>x \<in> I\<close> \<open>y \<in> I\<close> have cvx: "f (a * x + (1 - a) * y) \<le> a * f x + (1 - a) * f y"
    by (auto simp: convex_on_def)
  have "a * x + (1 - a) * y = a * (x - y) + y"
    by (simp add: field_simps)
  also have "\<dots> = t"
    unfolding a_def using \<open>x < t\<close> \<open>t < y\<close> by simp
  finally have "f t \<le> a * f x + (1 - a) * f y"
    using cvx by simp
  also have "\<dots> = a * (f x - f y) + f y"
    by (simp add: field_simps)
  finally have "f t - f y \<le> a * (f x - f y)"
    by simp
  with t show "(f x - f t) / (x - t) \<le> (f x - f y) / (x - y)"
    by (simp add: le_divide_eq divide_le_eq field_simps a_def)
  with t show "(f x - f y) / (x - y) \<le> (f t - f y) / (t - y)"
    by (simp add: le_divide_eq divide_le_eq field_simps)
qed

lemma pos_convex_function:
  fixes f :: "real \<Rightarrow> real"
  assumes "convex C"
    and leq: "\<And>x y. x \<in> C \<Longrightarrow> y \<in> C \<Longrightarrow> f' x * (y - x) \<le> f y - f x"
  shows "convex_on C f"
  unfolding convex_on_alt
  using assms
proof safe
  fix x y \<mu> :: real
  let ?x = "\<mu> *\<^sub>R x + (1 - \<mu>) *\<^sub>R y"
  assume *: "convex C" "x \<in> C" "y \<in> C" "\<mu> \<ge> 0" "\<mu> \<le> 1"
  then have "1 - \<mu> \<ge> 0" by auto
  then have xpos: "?x \<in> C"
    using * unfolding convex_alt by fastforce
  have geq: "\<mu> * (f x - f ?x) + (1 - \<mu>) * (f y - f ?x) \<ge>
      \<mu> * f' ?x * (x - ?x) + (1 - \<mu>) * f' ?x * (y - ?x)"
    using add_mono [OF mult_left_mono [OF leq [OF xpos *(2)] \<open>\<mu> \<ge> 0\<close>]
        mult_left_mono [OF leq [OF xpos *(3)] \<open>1 - \<mu> \<ge> 0\<close>]]
    by auto
  then have "\<mu> * f x + (1 - \<mu>) * f y - f ?x \<ge> 0"
    by (auto simp: field_simps)
  then show "f (\<mu> *\<^sub>R x + (1 - \<mu>) *\<^sub>R y) \<le> \<mu> * f x + (1 - \<mu>) * f y"
    by auto
qed

lemma atMostAtLeast_subset_convex:
  fixes C :: "real set"
  assumes "convex C"
    and "x \<in> C" "y \<in> C" "x < y"
  shows "{x .. y} \<subseteq> C"
proof safe
  fix z assume z: "z \<in> {x .. y}"
  have less: "z \<in> C" if *: "x < z" "z < y"
  proof -
    let ?\<mu> = "(y - z) / (y - x)"
    have "0 \<le> ?\<mu>" "?\<mu> \<le> 1"
      using assms * by (auto simp: field_simps)
    then have comb: "?\<mu> * x + (1 - ?\<mu>) * y \<in> C"
      using assms iffD1[OF convex_alt, rule_format, of C y x ?\<mu>]
      by (simp add: algebra_simps)
    have "?\<mu> * x + (1 - ?\<mu>) * y = (y - z) * x / (y - x) + (1 - (y - z) / (y - x)) * y"
      by (auto simp: field_simps)
    also have "\<dots> = ((y - z) * x + (y - x - (y - z)) * y) / (y - x)"
      using assms by (simp only: add_divide_distrib) (auto simp: field_simps)
    also have "\<dots> = z"
      using assms by (auto simp: field_simps)
    finally show ?thesis
      using comb by auto
  qed
  show "z \<in> C"
    using z less assms by (auto simp: le_less)
qed

lemma f''_imp_f':
  fixes f :: "real \<Rightarrow> real"
  assumes "convex C"
    and f': "\<And>x. x \<in> C \<Longrightarrow> DERIV f x :> (f' x)"
    and f'': "\<And>x. x \<in> C \<Longrightarrow> DERIV f' x :> (f'' x)"
    and pos: "\<And>x. x \<in> C \<Longrightarrow> f'' x \<ge> 0"
    and x: "x \<in> C"
    and y: "y \<in> C"
  shows "f' x * (y - x) \<le> f y - f x"
  using assms
proof -
  have "f y - f x \<ge> f' x * (y - x)" "f' y * (x - y) \<le> f x - f y"
    if *: "x \<in> C" "y \<in> C" "y > x" for x y :: real
  proof -
    from * have ge: "y - x > 0" "y - x \<ge> 0" and le: "x - y < 0" "x - y \<le> 0"
      by auto
    then obtain z1 where z1: "z1 > x" "z1 < y" "f y - f x = (y - x) * f' z1"
      using subsetD[OF atMostAtLeast_subset_convex[OF \<open>convex C\<close> \<open>x \<in> C\<close> \<open>y \<in> C\<close> \<open>x < y\<close>],
          THEN f', THEN MVT2[OF \<open>x < y\<close>, rule_format, unfolded atLeastAtMost_iff[symmetric]]]
      by auto
    then have "z1 \<in> C"
      using atMostAtLeast_subset_convex \<open>convex C\<close> \<open>x \<in> C\<close> \<open>y \<in> C\<close> \<open>x < y\<close>
      by fastforce
    obtain z2 where z2: "z2 > x" "z2 < z1" "f' z1 - f' x = (z1 - x) * f'' z2"
      using subsetD[OF atMostAtLeast_subset_convex[OF \<open>convex C\<close> \<open>x \<in> C\<close> \<open>z1 \<in> C\<close> \<open>x < z1\<close>],
          THEN f'', THEN MVT2[OF \<open>x < z1\<close>, rule_format, unfolded atLeastAtMost_iff[symmetric]]] z1
      by auto
    obtain z3 where z3: "z3 > z1" "z3 < y" "f' y - f' z1 = (y - z1) * f'' z3"
      using subsetD[OF atMostAtLeast_subset_convex[OF \<open>convex C\<close> \<open>z1 \<in> C\<close> \<open>y \<in> C\<close> \<open>z1 < y\<close>],
          THEN f'', THEN MVT2[OF \<open>z1 < y\<close>, rule_format, unfolded atLeastAtMost_iff[symmetric]]] z1
      by auto
    from z1 have "f x - f y = (x - y) * f' z1"
      by (simp add: field_simps)
    then have cool': "f' y - (f x - f y) / (x - y) = (y - z1) * f'' z3"
      using le(1) z3(3) by auto
    have "z3 \<in> C"
      using z3 * atMostAtLeast_subset_convex \<open>convex C\<close> \<open>x \<in> C\<close> \<open>z1 \<in> C\<close> \<open>x < z1\<close>
      by fastforce
    then have B': "f'' z3 \<ge> 0"
      using assms by auto
    with cool' have "f' y - (f x - f y) / (x - y) \<ge> 0"
      using z1 by auto
    then have res: "f' y * (x - y) \<le> f x - f y"
      by (meson diff_ge_0_iff_ge le(1) neg_divide_le_eq)
    have cool: "(f y - f x) / (y - x) - f' x = (z1 - x) * f'' z2"
      using le(1) z1(3) z2(3) by auto
    have "z2 \<in> C"
      using z2 z1 * atMostAtLeast_subset_convex \<open>convex C\<close> \<open>z1 \<in> C\<close> \<open>y \<in> C\<close> \<open>z1 < y\<close>
      by fastforce
    with z1 assms have "(z1 - x) * f'' z2 \<ge> 0"
      by auto
    then show "f y - f x \<ge> f' x * (y - x)" "f' y * (x - y) \<le> f x - f y"
      using that(3) z1(3) res cool by auto
  qed
  then show ?thesis
    using x y by fastforce
qed

lemma f''_ge0_imp_convex:
  fixes f :: "real \<Rightarrow> real"
  assumes "convex C"
    and "\<And>x. x \<in> C \<Longrightarrow> DERIV f x :> (f' x)"
    and "\<And>x. x \<in> C \<Longrightarrow> DERIV f' x :> (f'' x)"
    and "\<And>x. x \<in> C \<Longrightarrow> f'' x \<ge> 0"
  shows "convex_on C f"
  by (metis assms f''_imp_f' pos_convex_function)

lemma f''_le0_imp_concave:
  fixes f :: "real \<Rightarrow> real"
  assumes "convex C"
    and "\<And>x. x \<in> C \<Longrightarrow> DERIV f x :> (f' x)"
    and "\<And>x. x \<in> C \<Longrightarrow> DERIV f' x :> (f'' x)"
    and "\<And>x. x \<in> C \<Longrightarrow> f'' x \<le> 0"
  shows "concave_on C f"
  unfolding concave_on_def
  by (rule assms f''_ge0_imp_convex derivative_eq_intros | simp)+

lemma convex_power_even:
  assumes "even n"
  shows "convex_on (UNIV::real set) (\<lambda>x. x^n)"
proof (intro f''_ge0_imp_convex)
  show "((\<lambda>x. x ^ n) has_real_derivative of_nat n * x^(n-1)) (at x)" for x
    by (rule derivative_eq_intros | simp)+
  show "((\<lambda>x. of_nat n * x^(n-1)) has_real_derivative of_nat n * of_nat (n-1) * x^(n-2)) (at x)" for x
    by (rule derivative_eq_intros | simp add: eval_nat_numeral)+
  show "\<And>x. 0 \<le> real n * real (n - 1) * x ^ (n - 2)"
    using assms by (auto simp: zero_le_mult_iff zero_le_even_power)
qed auto

lemma convex_power_odd:
  assumes "odd n"
  shows "convex_on {0::real..} (\<lambda>x. x^n)"
proof (intro f''_ge0_imp_convex)
  show "((\<lambda>x. x ^ n) has_real_derivative of_nat n * x^(n-1)) (at x)" for x
    by (rule derivative_eq_intros | simp)+
  show "((\<lambda>x. of_nat n * x^(n-1)) has_real_derivative of_nat n * of_nat (n-1) * x^(n-2)) (at x)" for x
    by (rule derivative_eq_intros | simp add: eval_nat_numeral)+
  show "\<And>x. x \<in> {0::real..} \<Longrightarrow> 0 \<le> real n * real (n - 1) * x ^ (n - 2)"
    using assms by (auto simp: zero_le_mult_iff zero_le_even_power)
qed auto

lemma convex_power2: "convex_on (UNIV::real set) power2"
  by (simp add: convex_power_even)

lemma log_concave:
  fixes b :: real
  assumes "b > 1"
  shows "concave_on {0<..} (\<lambda> x. log b x)"
  using assms
  by (intro f''_le0_imp_concave derivative_eq_intros | simp)+

lemma ln_concave: "concave_on {0<..} ln"
  unfolding log_ln by (simp add: log_concave)

lemma minus_log_convex:
  fixes b :: real
  assumes "b > 1"
  shows "convex_on {0 <..} (\<lambda> x. - log b x)"
  using assms concave_on_def log_concave by blast

lemma powr_convex: 
  assumes "p \<ge> 1" shows "convex_on {0<..} (\<lambda>x. x powr p)"
  using assms
  by (intro f''_ge0_imp_convex derivative_eq_intros | simp)+

lemma exp_convex: "convex_on UNIV exp"
  by (intro f''_ge0_imp_convex derivative_eq_intros | simp)+

text \<open>The AM-GM inequality: the arithmetic mean exceeds the geometric mean.\<close>
lemma arith_geom_mean:
  fixes x :: "'a \<Rightarrow> real"
  assumes "finite S" "S \<noteq> {}"
    and x: "\<And>i. i \<in> S \<Longrightarrow> x i \<ge> 0"
  shows "(\<Sum>i \<in> S. x i / card S) \<ge> (\<Prod>i \<in> S. x i) powr (1 / card S)"
proof (cases "\<exists>i\<in>S. x i = 0")
  case True
  then have "(\<Prod>i \<in> S. x i) = 0"
    by (simp add: \<open>finite S\<close>)
  moreover have "(\<Sum>i \<in> S. x i / card S) \<ge> 0"
    by (simp add: sum_nonneg x)
  ultimately show ?thesis
    by simp
next
  case False
  have "ln (\<Sum>i \<in> S. (1 / card S) *\<^sub>R x i) \<ge> (\<Sum>i \<in> S. (1 / card S) * ln (x i))"
  proof (intro concave_on_sum)
    show "concave_on {0<..} ln"
      by (simp add: ln_concave)
    show "\<And>i. i\<in>S \<Longrightarrow> x i \<in> {0<..}"
      using False x by fastforce
  qed (use assms False in auto)
  moreover have "(\<Sum>i \<in> S. (1 / card S) *\<^sub>R x i) > 0"
    using False assms by (simp add: card_gt_0_iff less_eq_real_def sum_pos)
  ultimately have "(\<Sum>i \<in> S. (1 / card S) *\<^sub>R x i) \<ge> exp (\<Sum>i \<in> S. (1 / card S) * ln (x i))"
    using ln_ge_iff by blast
  then have "(\<Sum>i \<in> S. x i / card S) \<ge> exp (\<Sum>i \<in> S. ln (x i) / card S)"
    by (simp add: divide_simps)
  then show ?thesis
    using assms False
    by (smt (verit, ccfv_SIG) divide_inverse exp_ln exp_powr_real exp_sum inverse_eq_divide prod.cong prod_powr_distrib) 
qed

subsection\<^marker>\<open>tag unimportant\<close> \<open>Convexity of real functions\<close>

lemma convex_on_realI:
  assumes "connected A"
    and "\<And>x. x \<in> A \<Longrightarrow> (f has_real_derivative f' x) (at x)"
    and "\<And>x y. x \<in> A \<Longrightarrow> y \<in> A \<Longrightarrow> x \<le> y \<Longrightarrow> f' x \<le> f' y"
  shows "convex_on A f"
proof (rule convex_on_linorderI)
  show "convex A"
    using \<open>connected A\<close> convex_real_interval interval_cases
    by (smt (verit, ccfv_SIG) connectedD_interval convex_UNIV convex_empty)
      \<comment> \<open>the equivalence of "connected" and "convex" for real intervals is proved later\<close>
next
  fix t x y :: real
  assume t: "t > 0" "t < 1"
  assume xy: "x \<in> A" "y \<in> A" "x < y"
  define z where "z = (1 - t) * x + t * y"
  with \<open>connected A\<close> and xy have ivl: "{x..y} \<subseteq> A"
    using connected_contains_Icc by blast

  from xy t have xz: "z > x"
    by (simp add: z_def algebra_simps)
  have "y - z = (1 - t) * (y - x)"
    by (simp add: z_def algebra_simps)
  also from xy t have "\<dots> > 0"
    by (intro mult_pos_pos) simp_all
  finally have yz: "z < y"
    by simp

  from assms xz yz ivl t have "\<exists>\<xi>. \<xi> > x \<and> \<xi> < z \<and> f z - f x = (z - x) * f' \<xi>"
    by (intro MVT2) (auto intro!: assms(2))
  then obtain \<xi> where \<xi>: "\<xi> > x" "\<xi> < z" "f' \<xi> = (f z - f x) / (z - x)"
    by auto
  from assms xz yz ivl t have "\<exists>\<eta>. \<eta> > z \<and> \<eta> < y \<and> f y - f z = (y - z) * f' \<eta>"
    by (intro MVT2) (auto intro!: assms(2))
  then obtain \<eta> where \<eta>: "\<eta> > z" "\<eta> < y" "f' \<eta> = (f y - f z) / (y - z)"
    by auto

  from \<eta>(3) have "(f y - f z) / (y - z) = f' \<eta>" ..
  also from \<xi> \<eta> ivl have "\<xi> \<in> A" "\<eta> \<in> A"
    by auto
  with \<xi> \<eta> have "f' \<eta> \<ge> f' \<xi>"
    by (intro assms(3)) auto
  also from \<xi>(3) have "f' \<xi> = (f z - f x) / (z - x)" .
  finally have "(f y - f z) * (z - x) \<ge> (f z - f x) * (y - z)"
    using xz yz by (simp add: field_simps)
  also have "z - x = t * (y - x)"
    by (simp add: z_def algebra_simps)
  also have "y - z = (1 - t) * (y - x)"
    by (simp add: z_def algebra_simps)
  finally have "(f y - f z) * t \<ge> (f z - f x) * (1 - t)"
    using xy by simp
  then show "(1 - t) * f x + t * f y \<ge> f ((1 - t) *\<^sub>R x + t *\<^sub>R y)"
    by (simp add: z_def algebra_simps)
qed

lemma convex_on_inverse:
  fixes A :: "real set"
  assumes "A \<subseteq> {0<..}" "convex A"
  shows "convex_on A inverse"
proof -
  have "convex_on {0::real<..} inverse"
  proof (intro convex_on_realI)
    fix u v :: real
    assume "u \<in> {0<..}" "v \<in> {0<..}" "u \<le> v"
    with assms show "-inverse (u^2) \<le> -inverse (v^2)"
      by simp
  next
    show "\<And>x. x \<in> {0<..} \<Longrightarrow> (inverse has_real_derivative - inverse (x\<^sup>2)) (at x)"
      by (rule derivative_eq_intros | simp add: power2_eq_square)+
  qed auto
  then show ?thesis
    using assms convex_on_subset by blast
qed

lemma convex_onD_Icc':
  assumes "convex_on {x..y} f" "c \<in> {x..y}"
  defines "d \<equiv> y - x"
  shows "f c \<le> (f y - f x) / d * (c - x) + f x"
proof (cases x y rule: linorder_cases)
  case less
  then have d: "d > 0"
    by (simp add: d_def)
  from assms(2) less have A: "0 \<le> (c - x) / d" "(c - x) / d \<le> 1"
    by (simp_all add: d_def field_split_simps)
  have "f c = f (x + (c - x) * 1)"
    by simp
  also from less have "1 = ((y - x) / d)"
    by (simp add: d_def)
  also from d have "x + (c - x) * \<dots> = (1 - (c - x) / d) *\<^sub>R x + ((c - x) / d) *\<^sub>R y"
    by (simp add: field_simps)
  also have "f \<dots> \<le> (1 - (c - x) / d) * f x + (c - x) / d * f y"
    using assms less by (intro convex_onD_Icc) simp_all
  also from d have "\<dots> = (f y - f x) / d * (c - x) + f x"
    by (simp add: field_simps)
  finally show ?thesis .
qed (use assms in auto)

lemma convex_onD_Icc'':
  assumes "convex_on {x..y} f" "c \<in> {x..y}"
  defines "d \<equiv> y - x"
  shows "f c \<le> (f x - f y) / d * (y - c) + f y"
proof (cases x y rule: linorder_cases)
  case less
  then have d: "d > 0"
    by (simp add: d_def)
  from assms(2) less have A: "0 \<le> (y - c) / d" "(y - c) / d \<le> 1"
    by (simp_all add: d_def field_split_simps)
  have "f c = f (y - (y - c) * 1)"
    by simp
  also from less have "1 = ((y - x) / d)"
    by (simp add: d_def)
  also from d have "y - (y - c) * \<dots> = (1 - (1 - (y - c) / d)) *\<^sub>R x + (1 - (y - c) / d) *\<^sub>R y"
    by (simp add: field_simps)
  also have "f \<dots> \<le> (1 - (1 - (y - c) / d)) * f x + (1 - (y - c) / d) * f y"
    using assms less by (intro convex_onD_Icc) (simp_all add: field_simps)
  also from d have "\<dots> = (f x - f y) / d * (y - c) + f y"
    by (simp add: field_simps)
  finally show ?thesis .
qed (use assms in auto)

lemma concave_onD_Icc:
  assumes "concave_on {x..y} f" "x \<le> (y :: _ :: {real_vector,preorder})"
  shows "\<And>t. t \<ge> 0 \<Longrightarrow> t \<le> 1 \<Longrightarrow>
    f ((1 - t) *\<^sub>R x + t *\<^sub>R y) \<ge> (1 - t) * f x + t * f y"
  using assms(2) by (intro concave_onD [OF assms(1)]) simp_all

lemma concave_onD_Icc':
  assumes "concave_on {x..y} f" "c \<in> {x..y}"
  defines "d \<equiv> y - x"
  shows "f c \<ge> (f y - f x) / d * (c - x) + f x"
proof -
  have "- f c \<le> (f x - f y) / d * (c - x) - f x"
    using assms convex_onD_Icc' [of x y "\<lambda>x. - f x" c]
    by (simp add: concave_on_def)
  then show ?thesis
    by (smt (verit, best) divide_minus_left mult_minus_left)
qed

lemma concave_onD_Icc'':
  assumes "concave_on {x..y} f" "c \<in> {x..y}"
  defines "d \<equiv> y - x"
  shows "f c \<ge> (f x - f y) / d * (y - c) + f y"
proof -
  have "- f c \<le> (f y - f x) / d * (y - c) - f y"
    using assms convex_onD_Icc'' [of x y "\<lambda>x. - f x" c]
    by (simp add: concave_on_def)
  then show ?thesis
    by (smt (verit, best) divide_minus_left mult_minus_left)
qed

lemma convex_on_le_max:
  fixes a::real
  assumes "convex_on {x..y} f" and a: "a \<in> {x..y}"
  shows "f a \<le> max (f x) (f y)"
proof -
  have *: "(f y - f x) * (a - x) \<le> (f y - f x) * (y - x)" if "f x \<le> f y"
    using a that by (intro mult_left_mono) auto
  have "f a \<le> (f y - f x) / (y - x) * (a - x) + f x" 
    using assms convex_onD_Icc' by blast
  also have "\<dots> \<le> max (f x) (f y)"
    using a *
    by (simp add: divide_le_0_iff mult_le_0_iff zero_le_mult_iff max_def add.commute mult.commute scaling_mono)
  finally show ?thesis .
qed

lemma concave_on_ge_min:
  fixes a::real
  assumes "concave_on {x..y} f" and a: "a \<in> {x..y}"
  shows "f a \<ge> min (f x) (f y)"
proof -
  have *: "(f y - f x) * (a - x) \<ge> (f y - f x) * (y - x)" if "f x \<ge> f y"
    using a that by (intro mult_left_mono_neg) auto
  have "min (f x) (f y) \<le> (f y - f x) / (y - x) * (a - x) + f x"
    using a * apply (simp add: zero_le_divide_iff mult_le_0_iff zero_le_mult_iff min_def)
    by (smt (verit, best) nonzero_eq_divide_eq pos_divide_le_eq)
  also have "\<dots> \<le> f a"
    using assms concave_onD_Icc' by blast
  finally show ?thesis .
qed

subsection \<open>Convexity of the generalised binomial\<close>

lemma mono_on_mul:
  fixes f::"'a::ord \<Rightarrow> 'b::ordered_semiring"
  assumes "mono_on S f" "mono_on S g"
  assumes fty: "f \<in> S \<rightarrow> {0..}" and gty: "g \<in> S \<rightarrow> {0..}"
  shows "mono_on S (\<lambda>x. f x * g x)"
  using assms by (auto simp: Pi_iff monotone_on_def intro!: mult_mono)

lemma mono_on_prod:
  fixes f::"'i \<Rightarrow> 'a::ord \<Rightarrow> 'b::linordered_idom"
  assumes "\<And>i. i \<in> I \<Longrightarrow> mono_on S (f i)" 
  assumes "\<And>i. i \<in> I \<Longrightarrow> f i \<in> S \<rightarrow> {0..}" 
  shows "mono_on S (\<lambda>x. prod (\<lambda>i. f i x) I)"
  using assms
  by (induction I rule: infinite_finite_induct)
     (auto simp: mono_on_const Pi_iff prod_nonneg mono_on_mul mono_onI)

lemma convex_gchoose_aux: "convex_on {k-1..} (\<lambda>a. prod (\<lambda>i. a - of_nat i) {0..<k})"
proof (induction k)
  case 0
  then show ?case 
    by (simp add: convex_on_def)
next
  case (Suc k)
  have "convex_on {real k..} (\<lambda>a. (\<Prod>i = 0..<k. a - real i) * (a - real k))"
  proof (intro convex_on_mul convex_on_diff)
    show "convex_on {real k..} (\<lambda>x. \<Prod>i = 0..<k. x - real i)"
      using Suc convex_on_subset by fastforce
    show "mono_on {real k..} (\<lambda>x. \<Prod>i = 0..<k. x - real i)"
      by (force simp: monotone_on_def intro!: prod_mono)
  next
    show "(\<lambda>x. \<Prod>i = 0..<k. x - real i) \<in> {real k..} \<rightarrow> {0..}"
      by (auto intro!: prod_nonneg)
  qed (auto simp: convex_on_ident concave_on_const mono_onI)
  then show ?case
    by simp
qed

lemma convex_gchoose: "convex_on {k-1..} (\<lambda>x. x gchoose k)"
  by (simp add: gbinomial_prod_rev convex_on_cdiv convex_gchoose_aux)

lemma gbinomial_mono:
  fixes k::nat and a::real
  assumes "of_nat k \<le> a" "a \<le> b" shows "a gchoose k \<le> b gchoose k"
  using assms
  by (force simp: gbinomial_prod_rev intro!: divide_right_mono prod_mono)

lemma gbinomial_is_prod: "(a gchoose k) = (\<Prod>i<k. (a - of_nat i) / (1 + of_nat i))"
  unfolding gbinomial_prod_rev
  by (induction k; simp add: divide_simps)

subsection \<open>Some inequalities: Applications of convexity\<close>

lemma Youngs_inequality_0:
  fixes a::real
  assumes "0 \<le> \<alpha>" "0 \<le> \<beta>" "\<alpha>+\<beta> = 1" "a>0" "b>0"
  shows "a powr \<alpha> * b powr \<beta> \<le> \<alpha>*a + \<beta>*b"
proof -
  have "\<alpha> * ln a + \<beta> * ln b \<le> ln (\<alpha> * a + \<beta> * b)"
    using assms ln_concave by (simp add: concave_on_iff)
  moreover have "0 < \<alpha> * a + \<beta> * b"
    using assms by (smt (verit) mult_pos_pos split_mult_pos_le)
  ultimately show ?thesis
    using assms by (simp add: powr_def mult_exp_exp flip: ln_ge_iff)
qed

lemma Youngs_inequality:
  fixes p::real
  assumes "p>1" "q>1" "1/p + 1/q = 1" "a\<ge>0" "b\<ge>0"
  shows "a * b \<le> a powr p / p + b powr q / q"
proof (cases "a=0 \<or> b=0")
  case False
  then show ?thesis 
  using Youngs_inequality_0 [of "1/p" "1/q" "a powr p" "b powr q"] assms
  by (simp add: powr_powr)
qed (use assms in auto)

lemma Cauchy_Schwarz_ineq_sum:
  fixes a :: "'a \<Rightarrow> 'b::linordered_field"
  shows "(\<Sum>i\<in>I. a i * b i)\<^sup>2 \<le> (\<Sum>i\<in>I. (a i)\<^sup>2) * (\<Sum>i\<in>I. (b i)\<^sup>2)"
proof (cases "(\<Sum>i\<in>I. (b i)\<^sup>2) > 0")
  case False
  then consider "\<And>i. i\<in>I \<Longrightarrow> b i = 0" | "infinite I"
    by (metis (mono_tags, lifting) sum_pos2 zero_le_power2 zero_less_power2)
  thus ?thesis
    by fastforce
next
  case True
  define r where "r \<equiv> (\<Sum>i\<in>I. a i * b i) / (\<Sum>i\<in>I. (b i)\<^sup>2)"
  have "0 \<le> (\<Sum>i\<in>I. (a i - r * b i)\<^sup>2)"
    by (simp add: sum_nonneg)
  also have "... = (\<Sum>i\<in>I. (a i)\<^sup>2) - 2 * r * (\<Sum>i\<in>I. a i * b i) + r\<^sup>2 * (\<Sum>i\<in>I. (b i)\<^sup>2)"
    by (simp add: algebra_simps power2_eq_square sum_distrib_left flip: sum.distrib)
  also have "\<dots> = (\<Sum>i\<in>I. (a i)\<^sup>2) - ((\<Sum>i\<in>I. a i * b i))\<^sup>2 / (\<Sum>i\<in>I. (b i)\<^sup>2)"
    by (simp add: r_def power2_eq_square)
  finally have "0 \<le> (\<Sum>i\<in>I. (a i)\<^sup>2) - ((\<Sum>i\<in>I. a i * b i))\<^sup>2 / (\<Sum>i\<in>I. (b i)\<^sup>2)" .
  hence "((\<Sum>i\<in>I. a i * b i))\<^sup>2 / (\<Sum>i\<in>I. (b i)\<^sup>2) \<le> (\<Sum>i\<in>I. (a i)\<^sup>2)"
    by (simp add: le_diff_eq)
  thus "((\<Sum>i\<in>I. a i * b i))\<^sup>2 \<le> (\<Sum>i\<in>I. (a i)\<^sup>2) * (\<Sum>i\<in>I. (b i)\<^sup>2)"
    by (simp add: pos_divide_le_eq True)
qed

lemma sum_squared_le_sum_of_squares:
  fixes f :: "'a \<Rightarrow> real"
  assumes "\<And>i. i\<in>I \<Longrightarrow> f i \<ge> 0" "finite I" "I \<noteq> {}"
  shows "(\<Sum>i\<in>I. f i)\<^sup>2 \<le> (\<Sum>y\<in>I. (f y)\<^sup>2) * card I"
proof (cases "finite I \<and> I \<noteq> {}")
  case True
  have "(\<Sum>i\<in>I. f i / real (card I))\<^sup>2 \<le> (\<Sum>i\<in>I. (f i)\<^sup>2 / real (card I))"
    using assms convex_on_sum [OF _ _ convex_power2, where a = "\<lambda>x. 1 / real(card I)" and S=I]
    by simp
  then show ?thesis
    using assms  
    by (simp add: divide_simps power2_eq_square split: if_split_asm flip: sum_divide_distrib)
qed auto

subsection \<open>Misc related lemmas\<close>

lemma convex_translation_eq [simp]:
  "convex ((+) a ` s) \<longleftrightarrow> convex s"
  by (metis convex_translation translation_galois)

lemma convex_translation_subtract_eq [simp]:
  "convex ((\<lambda>b. b - a) ` s) \<longleftrightarrow> convex s"
  using convex_translation_eq [of "- a"] by (simp cong: image_cong_simp)

lemma convex_linear_image_eq [simp]:
    fixes f :: "'a::real_vector \<Rightarrow> 'b::real_vector"
    shows "\<lbrakk>linear f; inj f\<rbrakk> \<Longrightarrow> convex (f ` s) \<longleftrightarrow> convex s"
    by (metis (no_types) convex_linear_image convex_linear_vimage inj_vimage_image_eq)

lemma vector_choose_size:
  assumes "0 \<le> c"
  obtains x :: "'a::{real_normed_vector, perfect_space}" where "norm x = c"
proof -
  obtain a::'a where "a \<noteq> 0"
    using UNIV_not_singleton UNIV_eq_I set_zero singletonI by fastforce
  then show ?thesis
    by (rule_tac x="scaleR (c / norm a) a" in that) (simp add: assms)
qed

lemma vector_choose_dist:
  assumes "0 \<le> c"
  obtains y :: "'a::{real_normed_vector, perfect_space}" where "dist x y = c"
by (metis add_diff_cancel_left' assms dist_commute dist_norm vector_choose_size)

lemma sum_delta'':
  fixes s::"'a::real_vector set"
  assumes "finite s"
  shows "(\<Sum>x\<in>s. (if y = x then f x else 0) *\<^sub>R x) = (if y\<in>s then (f y) *\<^sub>R y else 0)"
proof -
  have *: "\<And>x y. (if y = x then f x else (0::real)) *\<^sub>R x = (if x=y then (f x) *\<^sub>R x else 0)"
    by auto
  show ?thesis
    unfolding * using sum.delta[OF assms, of y "\<lambda>x. f x *\<^sub>R x"] by auto
qed


subsection \<open>Cones\<close>

definition\<^marker>\<open>tag important\<close> cone :: "'a::real_vector set \<Rightarrow> bool"
  where "cone s \<longleftrightarrow> (\<forall>x\<in>s. \<forall>c\<ge>0. c *\<^sub>R x \<in> s)"

lemma cone_empty[intro, simp]: "cone {}"
  unfolding cone_def by auto

lemma cone_univ[intro, simp]: "cone UNIV"
  unfolding cone_def by auto

lemma cone_Inter[intro]: "\<forall>s\<in>f. cone s \<Longrightarrow> cone (\<Inter>f)"
  unfolding cone_def by auto

lemma subspace_imp_cone: "subspace S \<Longrightarrow> cone S"
  by (simp add: cone_def subspace_scale)


subsubsection \<open>Conic hull\<close>

lemma cone_cone_hull: "cone (cone hull S)"
  unfolding hull_def by auto

lemma cone_hull_eq: "cone hull S = S \<longleftrightarrow> cone S"
  by (metis cone_cone_hull hull_same)

lemma mem_cone:
  assumes "cone S" "x \<in> S" "c \<ge> 0"
  shows "c *\<^sub>R x \<in> S"
  using assms cone_def[of S] by auto

lemma cone_contains_0:
  assumes "cone S"
  shows "S \<noteq> {} \<longleftrightarrow> 0 \<in> S"
  using assms mem_cone by fastforce

lemma cone_0: "cone {0}"
  unfolding cone_def by auto

lemma cone_Union[intro]: "(\<forall>s\<in>f. cone s) \<longrightarrow> cone (\<Union>f)"
  unfolding cone_def by blast

lemma cone_iff:
  assumes "S \<noteq> {}"
  shows "cone S \<longleftrightarrow> 0 \<in> S \<and> (\<forall>c. c > 0 \<longrightarrow> ((*\<^sub>R) c) ` S = S)"  (is "_ = ?rhs")
proof 
  assume "cone S"
  {
    fix c :: real
    assume "c > 0"
    have "x \<in> ((*\<^sub>R) c) ` S" if "x \<in> S" for x
        using \<open>cone S\<close> \<open>c>0\<close> mem_cone[of S x "1/c"] that
          exI[of "(\<lambda>t. t \<in> S \<and> x = c *\<^sub>R t)" "(1 / c) *\<^sub>R x"]
        by auto
    then have "((*\<^sub>R) c) ` S = S" 
        using \<open>0 < c\<close> \<open>cone S\<close> mem_cone by fastforce
  }
  then show "0 \<in> S \<and> (\<forall>c. c > 0 \<longrightarrow> ((*\<^sub>R) c) ` S = S)"
    using \<open>cone S\<close> cone_contains_0[of S] assms by auto
next
  show "?rhs \<Longrightarrow> cone S"
    by (metis Convex.cone_def imageI order_neq_le_trans scaleR_zero_left)
qed

lemma cone_hull_empty: "cone hull {} = {}"
  by (metis cone_empty cone_hull_eq)

lemma cone_hull_empty_iff: "S = {} \<longleftrightarrow> cone hull S = {}"
  by (metis cone_hull_empty hull_subset subset_empty)

lemma cone_hull_contains_0: "S \<noteq> {} \<longleftrightarrow> 0 \<in> cone hull S"
  by (metis cone_cone_hull cone_contains_0 cone_hull_empty_iff)

lemma mem_cone_hull:
  assumes "x \<in> S" "c \<ge> 0"
  shows "c *\<^sub>R x \<in> cone hull S"
  by (metis assms cone_cone_hull hull_inc mem_cone)

proposition cone_hull_expl: "cone hull S = {c *\<^sub>R x | c x. c \<ge> 0 \<and> x \<in> S}"
  (is "?lhs = ?rhs")
proof 
  have "?rhs \<in> Collect cone"
    using Convex.cone_def by fastforce
  moreover have "S \<subseteq> ?rhs"
    by (smt (verit) mem_Collect_eq scaleR_one subsetI)
  ultimately show "?lhs \<subseteq> ?rhs"
    using hull_minimal by blast
qed (use mem_cone_hull in auto)

lemma convex_cone:
  "convex S \<and> cone S \<longleftrightarrow> (\<forall>x\<in>S. \<forall>y\<in>S. (x + y) \<in> S) \<and> (\<forall>x\<in>S. \<forall>c\<ge>0. (c *\<^sub>R x) \<in> S)"
  (is "?lhs = ?rhs")
proof -
  {
    fix x y
    assume "x\<in>S" "y\<in>S" and ?lhs
    then have "2 *\<^sub>R x \<in>S" "2 *\<^sub>R y \<in> S" "convex S"
      unfolding cone_def by auto
    then have "x + y \<in> S"
      using convexD [OF \<open>convex S\<close>, of "2*\<^sub>R x" "2*\<^sub>R y"]
      by (smt (verit, ccfv_threshold) field_sum_of_halves scaleR_2 scaleR_half_double)
  }
  then show ?thesis
    unfolding convex_def cone_def by blast
qed


subsection\<^marker>\<open>tag unimportant\<close> \<open>Connectedness of convex sets\<close>

lemma convex_connected:
  fixes S :: "'a::real_normed_vector set"
  assumes "convex S"
  shows "connected S"
proof (rule connectedI)
  fix A B
  assume "open A" "open B" "A \<inter> B \<inter> S = {}" "S \<subseteq> A \<union> B"
  moreover
  assume "A \<inter> S \<noteq> {}" "B \<inter> S \<noteq> {}"
  then obtain a b where a: "a \<in> A" "a \<in> S" and b: "b \<in> B" "b \<in> S" by auto
  define f where [abs_def]: "f u = u *\<^sub>R a + (1 - u) *\<^sub>R b" for u
  then have "continuous_on {0 .. 1} f"
    by (auto intro!: continuous_intros)
  then have "connected (f ` {0 .. 1})"
    by (auto intro!: connected_continuous_image)
  note connectedD[OF this, of A B]
  moreover have "a \<in> A \<inter> f ` {0 .. 1}"
    using a by (auto intro!: image_eqI[of _ _ 1] simp: f_def)
  moreover have "b \<in> B \<inter> f ` {0 .. 1}"
    using b by (auto intro!: image_eqI[of _ _ 0] simp: f_def)
  moreover have "f ` {0 .. 1} \<subseteq> S"
    using \<open>convex S\<close> a b unfolding convex_def f_def by auto
  ultimately show False by auto
qed

corollary%unimportant connected_UNIV[intro]: "connected (UNIV :: 'a::real_normed_vector set)"
  by (simp add: convex_connected)

lemma convex_prod:
  assumes "\<And>i. i \<in> Basis \<Longrightarrow> convex {x. P i x}"
  shows "convex {x. \<forall>i\<in>Basis. P i (x\<bullet>i)}"
  using assms by (auto simp: inner_add_left convex_def)

lemma convex_positive_orthant: "convex {x::'a::euclidean_space. (\<forall>i\<in>Basis. 0 \<le> x\<bullet>i)}"
by (rule convex_prod) (simp flip: atLeast_def)

subsection \<open>Convex hull\<close>

lemma convex_convex_hull [iff]: "convex (convex hull s)"
  by (metis (mono_tags) convex_Inter hull_def mem_Collect_eq)

lemma convex_hull_subset:
    "s \<subseteq> convex hull t \<Longrightarrow> convex hull s \<subseteq> convex hull t"
  by (simp add: subset_hull)

lemma convex_hull_eq: "convex hull s = s \<longleftrightarrow> convex s"
  by (metis convex_convex_hull hull_same)

subsubsection\<^marker>\<open>tag unimportant\<close> \<open>Convex hull is "preserved" by a linear function\<close>

lemma convex_hull_linear_image:
  assumes f: "linear f"
  shows "f ` (convex hull S) = convex hull (f ` S)"
proof
  show "convex hull (f ` S) \<subseteq> f ` (convex hull S)"
    by (intro hull_minimal image_mono hull_subset convex_linear_image assms convex_convex_hull)
  show "f ` (convex hull S) \<subseteq> convex hull (f ` S)"
    by (meson convex_convex_hull convex_linear_vimage f hull_minimal hull_subset image_subset_iff_subset_vimage)
qed

lemma in_convex_hull_linear_image:
  assumes "linear f" "x \<in> convex hull S"
  shows "f x \<in> convex hull (f ` S)"
  using assms convex_hull_linear_image image_eqI by blast

lemma convex_hull_Times:
  "convex hull (S \<times> T) = (convex hull S) \<times> (convex hull T)"
proof
  show "convex hull (S \<times> T) \<subseteq> (convex hull S) \<times> (convex hull T)"
    by (intro hull_minimal Sigma_mono hull_subset convex_Times convex_convex_hull)
  have "(x, y) \<in> convex hull (S \<times> T)" if x: "x \<in> convex hull S" and y: "y \<in> convex hull T" for x y
  proof (rule hull_induct [OF x], rule hull_induct [OF y])
    fix x y assume "x \<in> S" and "y \<in> T"
    then show "(x, y) \<in> convex hull (S \<times> T)"
      by (simp add: hull_inc)
  next
    fix x let ?S = "((\<lambda>y. (0, y)) -` (\<lambda>p. (- x, 0) + p) ` (convex hull S \<times> T))"
    have "convex ?S"
      by (intro convex_linear_vimage convex_translation convex_convex_hull,
        simp add: linear_iff)
    also have "?S = {y. (x, y) \<in> convex hull (S \<times> T)}"
      by (auto simp: image_def Bex_def)
    finally show "convex {y. (x, y) \<in> convex hull (S \<times> T)}" .
  next
    show "convex {x. (x, y) \<in> convex hull S \<times> T}"
    proof -
      fix y let ?S = "((\<lambda>x. (x, 0)) -` (\<lambda>p. (0, - y) + p) ` (convex hull S \<times> T))"
      have "convex ?S"
      by (intro convex_linear_vimage convex_translation convex_convex_hull,
        simp add: linear_iff)
      also have "?S = {x. (x, y) \<in> convex hull (S \<times> T)}"
        by (auto simp: image_def Bex_def)
      finally show "convex {x. (x, y) \<in> convex hull (S \<times> T)}" .
    qed
  qed
  then show "(convex hull S) \<times> (convex hull T) \<subseteq> convex hull (S \<times> T)"
    unfolding subset_eq split_paired_Ball_Sigma by blast
qed


subsubsection\<^marker>\<open>tag unimportant\<close> \<open>Stepping theorems for convex hulls of finite sets\<close>

lemma convex_hull_empty[simp]: "convex hull {} = {}"
  by (simp add: hull_same)

lemma convex_hull_singleton[simp]: "convex hull {a} = {a}"
  by (simp add: hull_same)

lemma convex_hull_insert:
  fixes S :: "'a::real_vector set"
  assumes "S \<noteq> {}"
  shows "convex hull (insert a S) =
         {x. \<exists>u\<ge>0. \<exists>v\<ge>0. \<exists>b. (u + v = 1) \<and> b \<in> (convex hull S) \<and> (x = u *\<^sub>R a + v *\<^sub>R b)}"
  (is "_ = ?hull")
proof (intro equalityI hull_minimal subsetI)
  fix x
  assume "x \<in> insert a S"
  then show "x \<in> ?hull"
  unfolding insert_iff
  proof
    assume "x = a"
    then show ?thesis
      by (smt (verit, del_insts) add.right_neutral assms ex_in_conv hull_inc mem_Collect_eq scaleR_one scaleR_zero_left)
  next
    assume "x \<in> S"
    with hull_subset show ?thesis
      by force
  qed
next
  fix x
  assume "x \<in> ?hull"
  then obtain u v b where obt: "u\<ge>0" "v\<ge>0" "u + v = 1" "b \<in> convex hull S" "x = u *\<^sub>R a + v *\<^sub>R b"
    by auto
  have "a \<in> convex hull insert a S" "b \<in> convex hull insert a S"
    using hull_mono[of S "insert a S" convex] hull_mono[of "{a}" "insert a S" convex] and obt(4)
    by auto
  then show "x \<in> convex hull insert a S"
    unfolding obt(5) using obt(1-3)
    by (rule convexD [OF convex_convex_hull])
next
  show "convex ?hull"
  proof (rule convexI)
    fix x y u v
    assume as: "(0::real) \<le> u" "0 \<le> v" "u + v = 1" and x: "x \<in> ?hull" and y: "y \<in> ?hull"
    from x obtain u1 v1 b1 where
      obt1: "u1\<ge>0" "v1\<ge>0" "u1 + v1 = 1" "b1 \<in> convex hull S" and xeq: "x = u1 *\<^sub>R a + v1 *\<^sub>R b1"
      by auto
    from y obtain u2 v2 b2 where
      obt2: "u2\<ge>0" "v2\<ge>0" "u2 + v2 = 1" "b2 \<in> convex hull S" and yeq: "y = u2 *\<^sub>R a + v2 *\<^sub>R b2"
      by auto
    have *: "\<And>(x::'a) s1 s2. x - s1 *\<^sub>R x - s2 *\<^sub>R x = ((1::real) - (s1 + s2)) *\<^sub>R x"
      by (auto simp: algebra_simps)
    have "\<exists>b \<in> convex hull S. u *\<^sub>R x + v *\<^sub>R y =
      (u * u1) *\<^sub>R a + (v * u2) *\<^sub>R a + (b - (u * u1) *\<^sub>R b - (v * u2) *\<^sub>R b)"
    proof (cases "u * v1 + v * v2 = 0")
      case True
      have *: "\<And>(x::'a) s1 s2. x - s1 *\<^sub>R x - s2 *\<^sub>R x = ((1::real) - (s1 + s2)) *\<^sub>R x"
        by (auto simp: algebra_simps)
      have eq0: "u * v1 = 0" "v * v2 = 0"
        using True mult_nonneg_nonneg[OF \<open>u\<ge>0\<close> \<open>v1\<ge>0\<close>] mult_nonneg_nonneg[OF \<open>v\<ge>0\<close> \<open>v2\<ge>0\<close>]
        by arith+
      then have "u * u1 + v * u2 = 1"
        using as(3) obt1(3) obt2(3) by auto
      then show ?thesis
        using "*" eq0 as obt1(4) xeq yeq by auto
    next
      case False
      have "1 - (u * u1 + v * u2) = (u + v) - (u * u1 + v * u2)"
        by (simp add: as(3))
      also have "\<dots> = u * v1 + v * v2"
        by (smt (verit, ccfv_SIG) distrib_left mult_cancel_left1 obt1(3) obt2(3))
      finally have **:"1 - (u * u1 + v * u2) = u * v1 + v * v2" .
      let ?b = "((u * v1) / (u * v1 + v * v2)) *\<^sub>R b1 + ((v * v2) / (u * v1 + v * v2)) *\<^sub>R b2"
      have zeroes: "0 \<le> u * v1 + v * v2" "0 \<le> u * v1" "0 \<le> u * v1 + v * v2" "0 \<le> v * v2"
        using as obt1 obt2 by auto
      show ?thesis
      proof
        show "u *\<^sub>R x + v *\<^sub>R y = (u * u1) *\<^sub>R a + (v * u2) *\<^sub>R a + (?b - (u * u1) *\<^sub>R ?b - (v * u2) *\<^sub>R ?b)"
          unfolding xeq yeq * **
          using False by (auto simp: scaleR_left_distrib scaleR_right_distrib)
        show "?b \<in> convex hull S"
          using False mem_convex_alt obt1(4) obt2(4) zeroes(2) zeroes(4) by fastforce
      qed
    qed
    then obtain b where b: "b \<in> convex hull S" 
       "u *\<^sub>R x + v *\<^sub>R y = (u * u1) *\<^sub>R a + (v * u2) *\<^sub>R a + (b - (u * u1) *\<^sub>R b - (v * u2) *\<^sub>R b)" ..
    obtain u1: "u1 \<le> 1" and u2: "u2 \<le> 1"
      using obt1 obt2 by auto
    have "u1 * u + u2 * v \<le> max u1 u2 * u + max u1 u2 * v"
      by (smt (verit, ccfv_SIG) as mult_right_mono)
    also have "\<dots> \<le> 1"
      unfolding distrib_left[symmetric] and as(3) using u1 u2 by auto
    finally have le1: "u1 * u + u2 * v \<le> 1" .    
    show "u *\<^sub>R x + v *\<^sub>R y \<in> ?hull"
    proof (intro CollectI exI conjI)
      show "0 \<le> u * u1 + v * u2"
        by (simp add: as obt1(1) obt2(1))
      show "0 \<le> 1 - u * u1 - v * u2"
        by (simp add: le1 diff_diff_add mult.commute)
    qed (use b in \<open>auto simp: algebra_simps\<close>)
  qed
qed

lemma convex_hull_insert_alt:
   "convex hull (insert a S) =
     (if S = {} then {a}
      else {(1 - u) *\<^sub>R a + u *\<^sub>R x |x u. 0 \<le> u \<and> u \<le> 1 \<and> x \<in> convex hull S})"
  apply (simp add: convex_hull_insert)
  using diff_add_cancel diff_ge_0_iff_ge
  by (smt (verit, del_insts) Collect_cong) 

subsubsection\<^marker>\<open>tag unimportant\<close> \<open>Explicit expression for convex hull\<close>

proposition convex_hull_indexed:
  fixes S :: "'a::real_vector set"
  shows "convex hull S =
    {y. \<exists>k u x. (\<forall>i\<in>{1::nat .. k}. 0 \<le> u i \<and> x i \<in> S) \<and>
                (sum u {1..k} = 1) \<and> (\<Sum>i = 1..k. u i *\<^sub>R x i) = y}"
    (is "?xyz = ?hull")
proof (rule hull_unique [OF _ convexI])
  show "S \<subseteq> ?hull" 
    by (clarsimp, rule_tac x=1 in exI, rule_tac x="\<lambda>x. 1" in exI, auto)
next
  fix T
  assume "S \<subseteq> T" "convex T"
  then show "?hull \<subseteq> T"
    by (blast intro: convex_sum)
next
  fix x y u v
  assume uv: "0 \<le> u" "0 \<le> v" "u + v = (1::real)"
  assume xy: "x \<in> ?hull" "y \<in> ?hull"
  from xy obtain k1 u1 x1 where
    x [rule_format]: "\<forall>i\<in>{1::nat..k1}. 0\<le>u1 i \<and> x1 i \<in> S" 
                      "sum u1 {Suc 0..k1} = 1" "(\<Sum>i = Suc 0..k1. u1 i *\<^sub>R x1 i) = x"
    by auto
  from xy obtain k2 u2 x2 where
    y [rule_format]: "\<forall>i\<in>{1::nat..k2}. 0\<le>u2 i \<and> x2 i \<in> S" 
                     "sum u2 {Suc 0..k2} = 1" "(\<Sum>i = Suc 0..k2. u2 i *\<^sub>R x2 i) = y"
    by auto
  have *: "\<And>P (x::'a) y s t i. (if P i then s else t) *\<^sub>R (if P i then x else y) = (if P i then s *\<^sub>R x else t *\<^sub>R y)"
          "{1..k1 + k2} \<inter> {1..k1} = {1..k1}" "{1..k1 + k2} \<inter> - {1..k1} = (\<lambda>i. i + k1) ` {1..k2}"
    by auto
  have inj: "inj_on (\<lambda>i. i + k1) {1..k2}"
    unfolding inj_on_def by auto
  let ?uu = "\<lambda>i. if i \<in> {1..k1} then u * u1 i else v * u2 (i - k1)"
  let ?xx = "\<lambda>i. if i \<in> {1..k1} then x1 i else x2 (i - k1)"
  show "u *\<^sub>R x + v *\<^sub>R y \<in> ?hull"
  proof (intro CollectI exI conjI ballI)
    show "0 \<le> ?uu i" "?xx i \<in> S" if "i \<in> {1..k1+k2}" for i
      using that by (auto simp add: le_diff_conv uv(1) x(1) uv(2) y(1))
    show "(\<Sum>i = 1..k1 + k2. ?uu i) = 1"  "(\<Sum>i = 1..k1 + k2. ?uu i *\<^sub>R ?xx i) = u *\<^sub>R x + v *\<^sub>R y"
      unfolding * sum.If_cases[OF finite_atLeastAtMost[of 1 "k1 + k2"]]
        sum.reindex[OF inj] Collect_mem_eq o_def
      unfolding scaleR_scaleR[symmetric] scaleR_right.sum [symmetric] sum_distrib_left[symmetric]
      by (simp_all add: sum_distrib_left[symmetric]  x(2,3) y(2,3) uv(3))
  qed 
qed

lemma convex_hull_finite:
  fixes S :: "'a::real_vector set"
  assumes "finite S"
  shows "convex hull S = {y. \<exists>u. (\<forall>x\<in>S. 0 \<le> u x) \<and> sum u S = 1 \<and> sum (\<lambda>x. u x *\<^sub>R x) S = y}"
  (is "?HULL = _")
proof (rule hull_unique [OF _ convexI]; clarify)
  fix x
  assume "x \<in> S"
  then show "\<exists>u. (\<forall>x\<in>S. 0 \<le> u x) \<and> sum u S = 1 \<and> (\<Sum>x\<in>S. u x *\<^sub>R x) = x"
    by (rule_tac x="\<lambda>y. if x=y then 1 else 0" in exI) (auto simp: sum.delta'[OF assms] sum_delta''[OF assms])
next
  fix u v :: real
  assume uv: "0 \<le> u" "0 \<le> v" "u + v = 1"
  fix ux assume ux [rule_format]: "\<forall>x\<in>S. 0 \<le> ux x" "sum ux S = (1::real)"
  fix uy assume uy [rule_format]: "\<forall>x\<in>S. 0 \<le> uy x" "sum uy S = (1::real)"
  have "0 \<le> u * ux x + v * uy x" if "x\<in>S" for x
    by (simp add: that uv ux(1) uy(1))
  moreover
  have "(\<Sum>x\<in>S. u * ux x + v * uy x) = 1"
    unfolding sum.distrib and sum_distrib_left[symmetric] ux(2) uy(2)
    using uv(3) by auto
  moreover
  have "(\<Sum>x\<in>S. (u * ux x + v * uy x) *\<^sub>R x) = u *\<^sub>R (\<Sum>x\<in>S. ux x *\<^sub>R x) + v *\<^sub>R (\<Sum>x\<in>S. uy x *\<^sub>R x)"
    unfolding scaleR_left_distrib sum.distrib scaleR_scaleR[symmetric] scaleR_right.sum [symmetric]
    by auto
  ultimately
  show "\<exists>uc. (\<forall>x\<in>S. 0 \<le> uc x) \<and> sum uc S = 1 \<and>
             (\<Sum>x\<in>S. uc x *\<^sub>R x) = u *\<^sub>R (\<Sum>x\<in>S. ux x *\<^sub>R x) + v *\<^sub>R (\<Sum>x\<in>S. uy x *\<^sub>R x)"
    by (rule_tac x="\<lambda>x. u * ux x + v * uy x" in exI, auto)
qed (use assms in \<open>auto simp: convex_explicit\<close>)


subsubsection\<^marker>\<open>tag unimportant\<close> \<open>Another formulation\<close>

text "Formalized by Lars Schewe."

lemma convex_hull_explicit:
  fixes p :: "'a::real_vector set"
  shows "convex hull p =
    {y. \<exists>S u. finite S \<and> S \<subseteq> p \<and> (\<forall>x\<in>S. 0 \<le> u x) \<and> sum u S = 1 \<and> sum (\<lambda>v. u v *\<^sub>R v) S = y}"
  (is "?lhs = ?rhs")
proof (intro subset_antisym subsetI)
  fix x
  assume "x \<in> convex hull p"
  then obtain k u y where
    obt: "\<forall>i\<in>{1::nat..k}. 0 \<le> u i \<and> y i \<in> p" "sum u {1..k} = 1" "(\<Sum>i = 1..k. u i *\<^sub>R y i) = x"
    unfolding convex_hull_indexed by auto
  have fin: "finite {1..k}" by auto
  {
    fix j
    assume "j\<in>{1..k}"
    then have "y j \<in> p \<and> 0 \<le> sum u {i. Suc 0 \<le> i \<and> i \<le> k \<and> y i = y j}"
      by (metis (mono_tags, lifting) One_nat_def atLeastAtMost_iff mem_Collect_eq obt(1) sum_nonneg)
  }
  moreover have "(\<Sum>v\<in>y ` {1..k}. sum u {i \<in> {1..k}. y i = v}) = 1"
    unfolding sum.image_gen[OF fin, symmetric] using obt(2) by auto
  moreover have "(\<Sum>v\<in>y ` {1..k}. sum u {i \<in> {1..k}. y i = v} *\<^sub>R v) = x"
    using sum.image_gen[OF fin, of "\<lambda>i. u i *\<^sub>R y i" y, symmetric]
    unfolding scaleR_left.sum using obt(3) by auto
  ultimately
  have "\<exists>S u. finite S \<and> S \<subseteq> p \<and> (\<forall>x\<in>S. 0 \<le> u x) \<and> sum u S = 1 \<and> (\<Sum>v\<in>S. u v *\<^sub>R v) = x"
    by (smt (verit, ccfv_SIG) imageE mem_Collect_eq obt(1) subsetI sum.cong sum.infinite sum_nonneg)
  then show "x \<in> ?rhs" by auto
next
  fix y
  assume "y \<in> ?rhs"
  then obtain S u where
    S: "finite S" "S \<subseteq> p" "\<forall>x\<in>S. 0 \<le> u x" "sum u S = 1" "(\<Sum>v\<in>S. u v *\<^sub>R v) = y"
    by auto
  obtain f where f: "inj_on f {1..card S}" "f ` {1..card S} = S"
    using ex_bij_betw_nat_finite_1[OF S(1)] unfolding bij_betw_def by auto
  then have "0 \<le> u (f i)" "f i \<in> p" if "i \<in> {1..card S}" for i
    using S \<open>i \<in> {1..card S}\<close> by blast+
  moreover 
  {
    fix y
    assume "y\<in>S"
    then obtain i where "i\<in>{1..card S}" "f i = y"
      by (metis f(2) image_iff)
    then have "{x. Suc 0 \<le> x \<and> x \<le> card S \<and> f x = y} = {i}"
      using f(1) inj_onD by fastforce
    then have "(\<Sum>x\<in>{x \<in> {1..card S}. f x = y}. u (f x)) = u y"
      "(\<Sum>x\<in>{x \<in> {1..card S}. f x = y}. u (f x) *\<^sub>R f x) = u y *\<^sub>R y"
      by (simp_all add: sum_constant_scaleR \<open>f i = y\<close>)
  }
  then have "(\<Sum>x = 1..card S. u (f x)) = 1" "(\<Sum>i = 1..card S. u (f i) *\<^sub>R f i) = y"
    by (metis (mono_tags, lifting) S(4,5) f sum.reindex_cong)+
  ultimately
  show "y \<in> convex hull p"
    unfolding convex_hull_indexed
    by (smt (verit, del_insts) mem_Collect_eq sum.cong)
qed


subsubsection\<^marker>\<open>tag unimportant\<close> \<open>A stepping theorem for that expansion\<close>

lemma convex_hull_finite_step:
  fixes S :: "'a::real_vector set"
  assumes "finite S"
  shows
    "(\<exists>u. (\<forall>x\<in>insert a S. 0 \<le> u x) \<and> sum u (insert a S) = w \<and> sum (\<lambda>x. u x *\<^sub>R x) (insert a S) = y)
      \<longleftrightarrow> (\<exists>v\<ge>0. \<exists>u. (\<forall>x\<in>S. 0 \<le> u x) \<and> sum u S = w - v \<and> sum (\<lambda>x. u x *\<^sub>R x) S = y - v *\<^sub>R a)"
  (is "?lhs = ?rhs")
proof (cases "a \<in> S")
  case True
  then have *: "insert a S = S" by auto
  show ?thesis
  proof
    assume ?lhs
    then show ?rhs
      unfolding * by force
  next
    have fin: "finite (insert a S)" using assms by auto
    assume ?rhs
    then obtain v u where uv: "v\<ge>0" "\<forall>x\<in>S. 0 \<le> u x" "sum u S = w - v" "(\<Sum>x\<in>S. u x *\<^sub>R x) = y - v *\<^sub>R a"
      by auto
    then show ?lhs
      using uv True assms
      apply (rule_tac x = "\<lambda>x. (if a = x then v else 0) + u x" in exI)
      apply (auto simp: sum_clauses scaleR_left_distrib sum.distrib sum_delta''[OF fin])
      done
  qed
next
  case False
  show ?thesis
  proof
    assume ?lhs
    then obtain u where u: "\<forall>x\<in>insert a S. 0 \<le> u x" "sum u (insert a S) = w" "(\<Sum>x\<in>insert a S. u x *\<^sub>R x) = y"
      by auto
    then show ?rhs
      using u \<open>a\<notin>S\<close> by (rule_tac x="u a" in exI) (auto simp: sum_clauses assms)
  next
    assume ?rhs
    then obtain v u where uv: "v\<ge>0" "\<forall>x\<in>S. 0 \<le> u x" "sum u S = w - v" "(\<Sum>x\<in>S. u x *\<^sub>R x) = y - v *\<^sub>R a"
      by auto
    moreover
    have "(\<Sum>x\<in>S. if a = x then v else u x) = sum u S"  "(\<Sum>x\<in>S. (if a = x then v else u x) *\<^sub>R x) = (\<Sum>x\<in>S. u x *\<^sub>R x)"
      using False by (auto intro!: sum.cong)
    ultimately show ?lhs
      using False by (rule_tac x="\<lambda>x. if a = x then v else u x" in exI) (auto simp: sum_clauses(2)[OF assms])
  qed
qed


subsubsection\<^marker>\<open>tag unimportant\<close> \<open>Hence some special cases\<close>

lemma convex_hull_2: "convex hull {a,b} = {u *\<^sub>R a + v *\<^sub>R b | u v. 0 \<le> u \<and> 0 \<le> v \<and> u + v = 1}"
       (is "?lhs = ?rhs")
proof -
  have **: "finite {b}" by auto
  have "\<And>x v u. \<lbrakk>0 \<le> v; v \<le> 1; (1 - v) *\<^sub>R b = x - v *\<^sub>R a\<rbrakk>
                \<Longrightarrow> \<exists>u v. x = u *\<^sub>R a + v *\<^sub>R b \<and> 0 \<le> u \<and> 0 \<le> v \<and> u + v = 1"
    by (metis add.commute diff_add_cancel diff_ge_0_iff_ge)
  moreover
  have "\<And>u v. \<lbrakk>0 \<le> u; 0 \<le> v; u + v = 1\<rbrakk>
               \<Longrightarrow> \<exists>p\<ge>0. \<exists>q. 0 \<le> q b \<and> q b = 1 - p \<and> q b *\<^sub>R b = u *\<^sub>R a + v *\<^sub>R b - p *\<^sub>R a"
    apply (rule_tac x=u in exI, simp)
    apply (rule_tac x="\<lambda>x. v" in exI, simp)
    done
  ultimately show ?thesis
    using convex_hull_finite_step[OF **, of a 1]
    by (auto simp add: convex_hull_finite)
qed

lemma convex_hull_2_alt: "convex hull {a,b} = {a + u *\<^sub>R (b - a) | u.  0 \<le> u \<and> u \<le> 1}"
  unfolding convex_hull_2
proof (rule Collect_cong)
  have *: "\<And>x y ::real. x + y = 1 \<longleftrightarrow> x = 1 - y"
    by auto
  fix x
  show "(\<exists>v u. x = v *\<^sub>R a + u *\<^sub>R b \<and> 0 \<le> v \<and> 0 \<le> u \<and> v + u = 1) \<longleftrightarrow>
    (\<exists>u. x = a + u *\<^sub>R (b - a) \<and> 0 \<le> u \<and> u \<le> 1)"
    apply (simp add: *)
    by (rule ex_cong1) (auto simp: algebra_simps)
qed

lemma convex_hull_3:
  "convex hull {a,b,c} = { u *\<^sub>R a + v *\<^sub>R b + w *\<^sub>R c | u v w. 0 \<le> u \<and> 0 \<le> v \<and> 0 \<le> w \<and> u + v + w = 1}"
proof -
  have fin: "finite {a,b,c}" "finite {b,c}" "finite {c}"
    by auto
  have *: "\<And>x y z ::real. x + y + z = 1 \<longleftrightarrow> x = 1 - y - z"
    by (auto simp: field_simps)
  show ?thesis
    unfolding convex_hull_finite[OF fin(1)] and convex_hull_finite_step[OF fin(2)] and *
    unfolding convex_hull_finite_step[OF fin(3)]
    apply (rule Collect_cong, simp)
    apply auto
    apply (rule_tac x=va in exI)
    apply (rule_tac x="u c" in exI, simp)
    apply (rule_tac x="1 - v - w" in exI, simp)
    apply (rule_tac x=v in exI, simp)
    apply (rule_tac x="\<lambda>x. w" in exI, simp)
    done
qed

lemma convex_hull_3_alt:
  "convex hull {a,b,c} = {a + u *\<^sub>R (b - a) + v *\<^sub>R (c - a) | u v.  0 \<le> u \<and> 0 \<le> v \<and> u + v \<le> 1}"
proof -
  have *: "\<And>x y z ::real. x + y + z = 1 \<longleftrightarrow> x = 1 - y - z"
    by auto
  show ?thesis
    unfolding convex_hull_3
    apply (auto simp: *)
    apply (rule_tac x=v in exI)
    apply (rule_tac x=w in exI)
    apply (simp add: algebra_simps)
    apply (rule_tac x=u in exI)
    apply (rule_tac x=v in exI)
    apply (simp add: algebra_simps)
    done
qed


subsection\<^marker>\<open>tag unimportant\<close> \<open>Relations among closure notions and corresponding hulls\<close>

lemma affine_imp_convex: "affine s \<Longrightarrow> convex s"
  unfolding affine_def convex_def by auto

lemma convex_affine_hull [simp]: "convex (affine hull S)"
  by (simp add: affine_imp_convex)

lemma subspace_imp_convex: "subspace s \<Longrightarrow> convex s"
  using subspace_imp_affine affine_imp_convex by auto

lemma convex_hull_subset_span: "(convex hull s) \<subseteq> (span s)"
  by (metis hull_minimal span_superset subspace_imp_convex subspace_span)

lemma convex_hull_subset_affine_hull: "(convex hull s) \<subseteq> (affine hull s)"
  by (metis affine_affine_hull affine_imp_convex hull_minimal hull_subset)

lemma aff_dim_convex_hull:
  fixes S :: "'n::euclidean_space set"
  shows "aff_dim (convex hull S) = aff_dim S"
  by (smt (verit) aff_dim_affine_hull aff_dim_subset convex_hull_subset_affine_hull hull_subset)


subsection \<open>Caratheodory's theorem\<close>

lemma convex_hull_caratheodory_aff_dim:
  fixes p :: "('a::euclidean_space) set"
  shows "convex hull p =
    {y. \<exists>S u. finite S \<and> S \<subseteq> p \<and> card S \<le> aff_dim p + 1 \<and>
        (\<forall>x\<in>S. 0 \<le> u x) \<and> sum u S = 1 \<and> sum (\<lambda>v. u v *\<^sub>R v) S = y}"
  unfolding convex_hull_explicit set_eq_iff mem_Collect_eq
proof (intro allI iffI)
  fix y
  let ?P = "\<lambda>n. \<exists>S u. finite S \<and> card S = n \<and> S \<subseteq> p \<and> (\<forall>x\<in>S. 0 \<le> u x) \<and>
    sum u S = 1 \<and> (\<Sum>v\<in>S. u v *\<^sub>R v) = y"
  assume "\<exists>S u. finite S \<and> S \<subseteq> p \<and> (\<forall>x\<in>S. 0 \<le> u x) \<and> sum u S = 1 \<and> (\<Sum>v\<in>S. u v *\<^sub>R v) = y"
  then obtain N where "?P N" by auto
  then have "\<exists>n\<le>N. (\<forall>k<n. \<not> ?P k) \<and> ?P n"
    by (rule_tac ex_least_nat_le, auto)
  then obtain n where "?P n" and smallest: "\<forall>k<n. \<not> ?P k"
    by blast
  then obtain S u where S: "finite S" "card S = n" "S\<subseteq>p" 
    and u: "\<forall>x\<in>S. 0 \<le> u x" "sum u S = 1"  "(\<Sum>v\<in>S. u v *\<^sub>R v) = y" by auto

  have "card S \<le> aff_dim p + 1"
  proof (rule ccontr, simp only: not_le)
    assume "aff_dim p + 1 < card S"
    then have "affine_dependent S"
      by (smt (verit) independent_card_le_aff_dim S(3))
    then obtain w v where wv: "sum w S = 0" "v\<in>S" "w v \<noteq> 0" "(\<Sum>v\<in>S. w v *\<^sub>R v) = 0"
      using affine_dependent_explicit_finite[OF S(1)] by auto
    define i where "i = (\<lambda>v. (u v) / (- w v)) ` {v\<in>S. w v < 0}"
    define t where "t = Min i"
    have "\<exists>x\<in>S. w x < 0"
      by (smt (verit, best) S(1) sum_pos2 wv)
    then have "i \<noteq> {}" unfolding i_def by auto
    then have "t \<ge> 0"
      using Min_ge_iff[of i 0] and S(1) u[unfolded le_less]
      unfolding t_def i_def
      by (auto simp: divide_le_0_iff)
    have t: "\<forall>v\<in>S. u v + t * w v \<ge> 0"
    proof
      fix v
      assume "v \<in> S"
      then have v: "0 \<le> u v"
        using u(1) by blast
      show "0 \<le> u v + t * w v"
      proof (cases "w v < 0")
        case False
        thus ?thesis using v \<open>t\<ge>0\<close> by auto
      next
        case True
        then have "t \<le> u v / (- w v)"
          using \<open>v\<in>S\<close> S unfolding t_def i_def by (auto intro: Min_le)
        then show ?thesis
          unfolding real_0_le_add_iff
          using True neg_le_minus_divide_eq by auto
      qed
    qed
    obtain a where "a \<in> S" and "t = (\<lambda>v. (u v) / (- w v)) a" and "w a < 0"
      using Min_in[OF _ \<open>i\<noteq>{}\<close>] and S(1) unfolding i_def t_def by auto
    then have a: "a \<in> S" "u a + t * w a = 0" by auto
    have *: "\<And>f. sum f (S - {a}) = sum f S - ((f a)::'b::ab_group_add)"
      unfolding sum.remove[OF S(1) \<open>a\<in>S\<close>] by auto
    have "(\<Sum>v\<in>S. u v + t * w v) = 1"
      by (metis add.right_neutral mult_zero_right sum.distrib sum_distrib_left u(2) wv(1))
    moreover have "(\<Sum>v\<in>S. u v *\<^sub>R v + (t * w v) *\<^sub>R v) - (u a *\<^sub>R a + (t * w a) *\<^sub>R a) = y"
      unfolding sum.distrib u(3) scaleR_scaleR[symmetric] scaleR_right.sum [symmetric] wv(4)
      using a(2) [THEN eq_neg_iff_add_eq_0 [THEN iffD2]] by simp
    ultimately have "?P (n - 1)"
      apply (rule_tac x="(S - {a})" in exI)
      apply (rule_tac x="\<lambda>v. u v + t * w v" in exI)
      using S t a
      apply (auto simp: * scaleR_left_distrib)
      done
    then show False
      using smallest[THEN spec[where x="n - 1"]] by auto
  qed
  then show "\<exists>S u. finite S \<and> S \<subseteq> p \<and> card S \<le> aff_dim p + 1 \<and>
      (\<forall>x\<in>S. 0 \<le> u x) \<and> sum u S = 1 \<and> (\<Sum>v\<in>S. u v *\<^sub>R v) = y"
    using S u by auto
qed auto

lemma caratheodory_aff_dim:
  fixes p :: "('a::euclidean_space) set"
  shows "convex hull p = {x. \<exists>S. finite S \<and> S \<subseteq> p \<and> card S \<le> aff_dim p + 1 \<and> x \<in> convex hull S}"
        (is "?lhs = ?rhs")
proof
  have "\<And>x S u. \<lbrakk>finite S; S \<subseteq> p; int (card S) \<le> aff_dim p + 1; \<forall>x\<in>S. 0 \<le> u x; sum u S = 1\<rbrakk>
                \<Longrightarrow> (\<Sum>v\<in>S. u v *\<^sub>R v) \<in> convex hull S"
    by (metis (mono_tags, lifting) convex_convex_hull convex_explicit hull_subset)
  then show "?lhs \<subseteq> ?rhs"
    by (subst convex_hull_caratheodory_aff_dim, auto)
qed (use hull_mono in auto)

lemma convex_hull_caratheodory:
  fixes p :: "('a::euclidean_space) set"
  shows "convex hull p =
            {y. \<exists>S u. finite S \<and> S \<subseteq> p \<and> card S \<le> DIM('a) + 1 \<and>
              (\<forall>x\<in>S. 0 \<le> u x) \<and> sum u S = 1 \<and> sum (\<lambda>v. u v *\<^sub>R v) S = y}"
        (is "?lhs = ?rhs")
proof (intro set_eqI iffI)
  fix x
  assume "x \<in> ?lhs" then show "x \<in> ?rhs"
    unfolding convex_hull_caratheodory_aff_dim 
    using aff_dim_le_DIM [of p] by fastforce
qed (auto simp: convex_hull_explicit)

theorem caratheodory:
  "convex hull p =
    {x::'a::euclidean_space. \<exists>S. finite S \<and> S \<subseteq> p \<and> card S \<le> DIM('a) + 1 \<and> x \<in> convex hull S}"
proof safe
  fix x
  assume "x \<in> convex hull p"
  then obtain S u where "finite S" "S \<subseteq> p" "card S \<le> DIM('a) + 1"
    "\<forall>x\<in>S. 0 \<le> u x" "sum u S = 1" "(\<Sum>v\<in>S. u v *\<^sub>R v) = x"
    unfolding convex_hull_caratheodory by auto
  then show "\<exists>S. finite S \<and> S \<subseteq> p \<and> card S \<le> DIM('a) + 1 \<and> x \<in> convex hull S"
    using convex_hull_finite by fastforce
qed (use hull_mono in force)

subsection\<^marker>\<open>tag unimportant\<close>\<open>Some Properties of subset of standard basis\<close>

lemma affine_hull_substd_basis:
  assumes "d \<subseteq> Basis"
  shows "affine hull (insert 0 d) = {x::'a::euclidean_space. \<forall>i\<in>Basis. i \<notin> d \<longrightarrow> x\<bullet>i = 0}"
  (is "affine hull (insert 0 ?A) = ?B")
proof -
  have *: "\<And>A. (+) (0::'a) ` A = A" "\<And>A. (+) (- (0::'a)) ` A = A"
    by auto
  show ?thesis
    unfolding affine_hull_insert_span_gen span_substd_basis[OF assms,symmetric] * ..
qed

lemma affine_hull_convex_hull [simp]: "affine hull (convex hull S) = affine hull S"
  by (metis Int_absorb1 Int_absorb2 convex_hull_subset_affine_hull hull_hull hull_mono hull_subset)


subsection\<^marker>\<open>tag unimportant\<close> \<open>Moving and scaling convex hulls\<close>

lemma convex_hull_set_plus:
  "convex hull (S + T) = convex hull S + convex hull T"
  by (simp add: set_plus_image linear_iff scaleR_right_distrib convex_hull_Times 
        flip: convex_hull_linear_image)

lemma translation_eq_singleton_plus: "(\<lambda>x. a + x) ` T = {a} + T"
  unfolding set_plus_def by auto

lemma convex_hull_translation:
  "convex hull ((\<lambda>x. a + x) ` S) = (\<lambda>x. a + x) ` (convex hull S)"
  by (simp add: convex_hull_set_plus translation_eq_singleton_plus)

lemma convex_hull_scaling:
  "convex hull ((\<lambda>x. c *\<^sub>R x) ` S) = (\<lambda>x. c *\<^sub>R x) ` (convex hull S)"
  by (simp add: convex_hull_linear_image)

lemma convex_hull_affinity:
  "convex hull ((\<lambda>x. a + c *\<^sub>R x) ` S) = (\<lambda>x. a + c *\<^sub>R x) ` (convex hull S)"
  by (metis convex_hull_scaling convex_hull_translation image_image)


subsection\<^marker>\<open>tag unimportant\<close> \<open>Convexity of cone hulls\<close>

lemma convex_cone_hull:
  assumes "convex S"
  shows "convex (cone hull S)"
proof (rule convexI)
  fix x y
  assume xy: "x \<in> cone hull S" "y \<in> cone hull S"
  then have "S \<noteq> {}"
    using cone_hull_empty_iff[of S] by auto
  fix u v :: real
  assume uv: "u \<ge> 0" "v \<ge> 0" "u + v = 1"
  then have *: "u *\<^sub>R x \<in> cone hull S" "v *\<^sub>R y \<in> cone hull S"
    by (simp_all add: cone_cone_hull mem_cone uv xy)
  then obtain cx :: real and xx
      and cy :: real and yy  where x: "u *\<^sub>R x = cx *\<^sub>R xx" "cx \<ge> 0" "xx \<in> S" 
      and y: "v *\<^sub>R y = cy *\<^sub>R yy" "cy \<ge> 0" "yy \<in> S"
    using cone_hull_expl[of S] by auto

  have "u *\<^sub>R x + v *\<^sub>R y \<in> cone hull S" if "cx + cy \<le> 0"
    using "*"(1) nless_le that x(2) y by fastforce
  moreover
  have "u *\<^sub>R x + v *\<^sub>R y \<in> cone hull S" if "cx + cy > 0"
  proof -
    have "(cx / (cx + cy)) *\<^sub>R xx + (cy / (cx + cy)) *\<^sub>R yy \<in> S"
      using assms mem_convex_alt[of S xx yy cx cy] x y that by auto
    then have "cx *\<^sub>R xx + cy *\<^sub>R yy \<in> cone hull S"
      using mem_cone_hull[of "(cx/(cx+cy)) *\<^sub>R xx + (cy/(cx+cy)) *\<^sub>R yy" S "cx+cy"] \<open>cx+cy>0\<close>
      by (auto simp: scaleR_right_distrib)
    then show ?thesis
      using x y by auto
  qed
  moreover have "cx + cy \<le> 0 \<or> cx + cy > 0" by auto
  ultimately show "u *\<^sub>R x + v *\<^sub>R y \<in> cone hull S" by blast
qed

lemma cone_convex_hull:
  assumes "cone S"
  shows "cone (convex hull S)"
  by (metis (no_types, lifting) affine_hull_convex_hull affine_hull_eq_empty assms cone_iff convex_hull_scaling hull_inc)

section \<open>Conic sets and conic hull\<close>

definition conic :: "'a::real_vector set \<Rightarrow> bool"
  where "conic S \<equiv> \<forall>x c. x \<in> S \<longrightarrow> 0 \<le> c \<longrightarrow> (c *\<^sub>R x) \<in> S"

lemma conicD: "\<lbrakk>conic S; x \<in> S; 0 \<le> c\<rbrakk> \<Longrightarrow> (c *\<^sub>R x) \<in> S"
  by (meson conic_def)

lemma subspace_imp_conic: "subspace S \<Longrightarrow> conic S"
  by (simp add: conic_def subspace_def)

lemma conic_empty [simp]: "conic {}"
  using conic_def by blast

lemma conic_UNIV: "conic UNIV"
  by (simp add: conic_def)

lemma conic_Inter: "(\<And>S. S \<in> \<F> \<Longrightarrow> conic S) \<Longrightarrow> conic(\<Inter>\<F>)"
  by (simp add: conic_def)

lemma conic_linear_image:
   "\<lbrakk>conic S; linear f\<rbrakk> \<Longrightarrow> conic(f ` S)"
  by (smt (verit) conic_def image_iff linear.scaleR)

lemma conic_linear_image_eq:
   "\<lbrakk>linear f; inj f\<rbrakk> \<Longrightarrow> conic (f ` S) \<longleftrightarrow> conic S"
  by (smt (verit) conic_def conic_linear_image inj_image_mem_iff linear_cmul)

lemma conic_mul: "\<lbrakk>conic S; x \<in> S; 0 \<le> c\<rbrakk> \<Longrightarrow> (c *\<^sub>R x) \<in> S"
  using conic_def by blast

lemma conic_conic_hull: "conic(conic hull S)"
  by (metis (no_types, lifting) conic_Inter hull_def mem_Collect_eq)

lemma conic_hull_eq: "(conic hull S = S) \<longleftrightarrow> conic S"
  by (metis conic_conic_hull hull_same)

lemma conic_hull_UNIV [simp]: "conic hull UNIV = UNIV"
  by simp

lemma conic_negations: "conic S \<Longrightarrow> conic (image uminus S)"
  by (auto simp: conic_def image_iff)

lemma conic_span [iff]: "conic(span S)"
  by (simp add: subspace_imp_conic)

lemma conic_hull_explicit:
   "conic hull S = {c *\<^sub>R x| c x. 0 \<le> c \<and> x \<in> S}"
  proof (rule hull_unique)
    show "S \<subseteq> {c *\<^sub>R x |c x. 0 \<le> c \<and> x \<in> S}"
      by (metis (no_types) cone_hull_expl hull_subset)
  show "conic {c *\<^sub>R x |c x. 0 \<le> c \<and> x \<in> S}"
    using mult_nonneg_nonneg by (force simp: conic_def)
qed (auto simp: conic_def)

lemma conic_hull_as_image:
   "conic hull S = (\<lambda>z. fst z *\<^sub>R snd z) ` ({0..} \<times> S)"
  by (force simp: conic_hull_explicit)

lemma conic_hull_linear_image:
   "linear f \<Longrightarrow> conic hull f ` S = f ` (conic hull S)"
  by (force simp: conic_hull_explicit image_iff set_eq_iff linear_scale) 

lemma conic_hull_image_scale:
  assumes "\<And>x. x \<in> S \<Longrightarrow> 0 < c x"
  shows   "conic hull (\<lambda>x. c x *\<^sub>R x) ` S = conic hull S"
proof
  show "conic hull (\<lambda>x. c x *\<^sub>R x) ` S \<subseteq> conic hull S"
  proof (rule hull_minimal)
    show "(\<lambda>x. c x *\<^sub>R x) ` S \<subseteq> conic hull S"
      using assms conic_hull_explicit by fastforce
  qed (simp add: conic_conic_hull)
  show "conic hull S \<subseteq> conic hull (\<lambda>x. c x *\<^sub>R x) ` S"
  proof (rule hull_minimal)
    show "S \<subseteq> conic hull (\<lambda>x. c x *\<^sub>R x) ` S"
    proof clarsimp
      fix x
      assume "x \<in> S"
      then have "x = inverse(c x) *\<^sub>R c x *\<^sub>R x"
        using assms by fastforce
      then show "x \<in> conic hull (\<lambda>x. c x *\<^sub>R x) ` S"
        by (smt (verit, best) \<open>x \<in> S\<close> assms conic_conic_hull conic_mul hull_inc image_eqI inverse_nonpositive_iff_nonpositive)
    qed
  qed (simp add: conic_conic_hull)
qed

lemma convex_conic_hull:
  assumes "convex S"
  shows "convex (conic hull S)"
proof (clarsimp simp add: conic_hull_explicit convex_alt)
  fix c x d y and u :: real
  assume \<section>: "(0::real) \<le> c" "x \<in> S" "(0::real) \<le> d" "y \<in> S" "0 \<le> u" "u \<le> 1"
  show "\<exists>c'' x''. ((1 - u) * c) *\<^sub>R x + (u * d) *\<^sub>R y = c'' *\<^sub>R x'' \<and> 0 \<le> c'' \<and> x'' \<in> S"
  proof (cases "(1 - u) * c = 0")
    case True
    with \<open>0 \<le> d\<close> \<open>y \<in> S\<close>\<open>0 \<le> u\<close>  
    show ?thesis by force
  next
    case False
    define \<xi> where "\<xi> \<equiv> (1 - u) * c + u * d"
    have *: "c * u \<le> c"
      by (simp add: "\<section>" mult_left_le)
    have "\<xi> > 0"
      using False \<section> by (smt (verit, best) \<xi>_def split_mult_pos_le)
    then have **: "c + d * u = \<xi> + c * u"
      by (simp add: \<xi>_def mult.commute right_diff_distrib')
    show ?thesis
    proof (intro exI conjI)
      show "0 \<le> \<xi>"
        using \<open>0 < \<xi>\<close> by auto
      show "((1 - u) * c) *\<^sub>R x + (u * d) *\<^sub>R y = \<xi> *\<^sub>R (((1 - u) * c / \<xi>) *\<^sub>R x + (u * d / \<xi>) *\<^sub>R y)"
        using \<open>\<xi> > 0\<close> by (simp add: algebra_simps diff_divide_distrib)
      show "((1 - u) * c / \<xi>) *\<^sub>R x + (u * d / \<xi>) *\<^sub>R y \<in> S"
        using \<open>0 < \<xi>\<close> 
        by (intro convexD [OF assms]) (auto simp: \<section> field_split_simps * **)
    qed
  qed
qed

lemma conic_halfspace_le: "conic {x. a \<bullet> x \<le> 0}"
  by (auto simp: conic_def mult_le_0_iff)

lemma conic_halfspace_ge: "conic {x. a \<bullet> x \<ge> 0}"
  by (auto simp: conic_def mult_le_0_iff)

lemma conic_hull_empty [simp]: "conic hull {} = {}"
  by (simp add: conic_hull_eq)

lemma conic_contains_0: "conic S \<Longrightarrow> (0 \<in> S \<longleftrightarrow> S \<noteq> {})"
  by (simp add: Convex.cone_def cone_contains_0 conic_def)

lemma conic_hull_eq_empty: "conic hull S = {} \<longleftrightarrow> (S = {})"
  using conic_hull_explicit by fastforce

lemma conic_sums: "\<lbrakk>conic S; conic T\<rbrakk> \<Longrightarrow> conic (\<Union>x\<in> S. \<Union>y \<in> T. {x + y})"
  by (simp add: conic_def) (metis scaleR_right_distrib)

lemma conic_Times: "\<lbrakk>conic S; conic T\<rbrakk> \<Longrightarrow> conic(S \<times> T)"
  by (auto simp: conic_def)

lemma conic_Times_eq:
   "conic(S \<times> T) \<longleftrightarrow> S = {} \<or> T = {} \<or> conic S \<and> conic T" (is "?lhs = ?rhs")
proof
  show "?lhs \<Longrightarrow> ?rhs"
    by (force simp: conic_def)
  show "?rhs \<Longrightarrow> ?lhs"
    by (force simp: conic_Times)
qed

lemma conic_hull_0 [simp]: "conic hull {0} = {0}"
  by (simp add: conic_hull_eq subspace_imp_conic)

lemma conic_hull_contains_0 [simp]: "0 \<in> conic hull S \<longleftrightarrow> (S \<noteq> {})"
  by (simp add: conic_conic_hull conic_contains_0 conic_hull_eq_empty)

lemma conic_hull_eq_sing:
  "conic hull S = {x} \<longleftrightarrow> S = {0} \<and> x = 0"
proof
  show "conic hull S = {x} \<Longrightarrow> S = {0} \<and> x = 0"
    by (metis conic_conic_hull conic_contains_0 conic_def conic_hull_eq hull_inc insert_not_empty singleton_iff)
qed simp

lemma conic_hull_Int_affine_hull:
  assumes "T \<subseteq> S" "0 \<notin> affine hull S"
  shows "(conic hull T) \<inter> (affine hull S) = T"
proof -
  have TaffS: "T \<subseteq> affine hull S"
    using \<open>T \<subseteq> S\<close> hull_subset by fastforce
  moreover
  have "conic hull T \<inter> affine hull S \<subseteq> T"
  proof (clarsimp simp: conic_hull_explicit)
    fix c x
    assume "c *\<^sub>R x \<in> affine hull S"
      and "0 \<le> c"
      and "x \<in> T"
    show "c *\<^sub>R x \<in> T"
    proof (cases "c=1")
      case True
      then show ?thesis
        by (simp add: \<open>x \<in> T\<close>)
    next
      case False
      then have "x /\<^sub>R (1 - c) = x + (c * inverse (1 - c)) *\<^sub>R x"
        by (smt (verit, ccfv_SIG) diff_add_cancel mult.commute real_vector_affinity_eq scaleR_collapse scaleR_scaleR)
      then have "0 = inverse(1 - c) *\<^sub>R c *\<^sub>R x + (1 - inverse(1 - c)) *\<^sub>R x"
        by (simp add: algebra_simps)
      then have "0 \<in> affine hull S"
        by (smt (verit) \<open>c *\<^sub>R x \<in> affine hull S\<close> \<open>x \<in> T\<close> affine_affine_hull TaffS in_mono mem_affine)
      then show ?thesis
        using assms by auto        
    qed
  qed
  ultimately show ?thesis
    by (auto simp: hull_inc)
qed


section \<open>Convex cones and corresponding hulls\<close>

definition convex_cone :: "'a::real_vector set \<Rightarrow> bool"
  where "convex_cone \<equiv> \<lambda>S. S \<noteq> {} \<and> convex S \<and> conic S"

lemma convex_cone_iff:
   "convex_cone S \<longleftrightarrow>
        0 \<in> S \<and> (\<forall>x \<in> S. \<forall>y \<in> S. x + y \<in> S) \<and> (\<forall>x \<in> S. \<forall>c\<ge>0. c *\<^sub>R x \<in> S)"
    by (metis cone_def conic_contains_0 conic_def convex_cone convex_cone_def)

lemma convex_cone_add: "\<lbrakk>convex_cone S; x \<in> S; y \<in> S\<rbrakk> \<Longrightarrow> x+y \<in> S"
  by (simp add: convex_cone_iff)

lemma convex_cone_scaleR: "\<lbrakk>convex_cone S; 0 \<le> c; x \<in> S\<rbrakk> \<Longrightarrow> c *\<^sub>R x \<in> S"
  by (simp add: convex_cone_iff)

lemma convex_cone_nonempty: "convex_cone S \<Longrightarrow> S \<noteq> {}"
  by (simp add: convex_cone_def)

lemma convex_cone_linear_image:
   "convex_cone S \<and> linear f \<Longrightarrow> convex_cone(f ` S)"
  by (simp add: conic_linear_image convex_cone_def convex_linear_image)

lemma convex_cone_linear_image_eq:
   "\<lbrakk>linear f; inj f\<rbrakk> \<Longrightarrow> (convex_cone(f ` S) \<longleftrightarrow> convex_cone S)"
  by (simp add: conic_linear_image_eq convex_cone_def)

lemma convex_cone_halfspace_ge: "convex_cone {x. a \<bullet> x \<ge> 0}"
  by (simp add: convex_cone_iff inner_simps(2))

lemma convex_cone_halfspace_le: "convex_cone {x. a \<bullet> x \<le> 0}"
  by (simp add: convex_cone_iff inner_right_distrib mult_nonneg_nonpos)

lemma convex_cone_contains_0: "convex_cone S \<Longrightarrow> 0 \<in> S"
  using convex_cone_iff by blast

lemma convex_cone_Inter:
   "(\<And>S. S \<in> f \<Longrightarrow> convex_cone S) \<Longrightarrow> convex_cone(\<Inter> f)"
  by (simp add: convex_cone_iff)

lemma convex_cone_convex_cone_hull: "convex_cone(convex_cone hull S)"
  by (metis (no_types, lifting) convex_cone_Inter hull_def mem_Collect_eq)

lemma convex_convex_cone_hull: "convex(convex_cone hull S)"
  by (meson convex_cone_convex_cone_hull convex_cone_def)

lemma conic_convex_cone_hull: "conic(convex_cone hull S)"
  by (metis convex_cone_convex_cone_hull convex_cone_def)

lemma convex_cone_hull_nonempty: "convex_cone hull S \<noteq> {}"
  by (simp add: convex_cone_convex_cone_hull convex_cone_nonempty)

lemma convex_cone_hull_contains_0: "0 \<in> convex_cone hull S"
  by (simp add: convex_cone_contains_0 convex_cone_convex_cone_hull)

lemma convex_cone_hull_add:
   "\<lbrakk>x \<in> convex_cone hull S; y \<in> convex_cone hull S\<rbrakk> \<Longrightarrow> x + y \<in> convex_cone hull S"
  by (simp add: convex_cone_add convex_cone_convex_cone_hull)

lemma convex_cone_hull_mul:
   "\<lbrakk>x \<in> convex_cone hull S; 0 \<le> c\<rbrakk> \<Longrightarrow> (c *\<^sub>R x) \<in> convex_cone hull S"
  by (simp add: conic_convex_cone_hull conic_mul)

thm convex_sums
lemma convex_cone_sums:
   "\<lbrakk>convex_cone S; convex_cone T\<rbrakk> \<Longrightarrow> convex_cone (\<Union>x\<in> S. \<Union>y \<in> T. {x + y})"
  by (simp add: convex_cone_def conic_sums convex_sums)

lemma convex_cone_Times:
   "\<lbrakk>convex_cone S; convex_cone T\<rbrakk> \<Longrightarrow> convex_cone(S \<times> T)"
  by (simp add: conic_Times convex_Times convex_cone_def)

lemma convex_cone_Times_D1: "convex_cone (S \<times> T) \<Longrightarrow> convex_cone S"
  by (metis Times_empty conic_Times_eq convex_cone_def convex_convex_hull convex_hull_Times hull_same times_eq_iff)

lemma convex_cone_Times_eq:
   "convex_cone(S \<times> T) \<longleftrightarrow> convex_cone S \<and> convex_cone T" 
proof (cases "S={} \<or> T={}")
  case True
  then show ?thesis 
    by (auto dest: convex_cone_nonempty)
next
  case False
  then have "convex_cone (S \<times> T) \<Longrightarrow> convex_cone T"
    by (metis conic_Times_eq convex_cone_def convex_convex_hull convex_hull_Times hull_same times_eq_iff)
  then show ?thesis
    using convex_cone_Times convex_cone_Times_D1 by blast 
qed


lemma convex_cone_hull_Un:
  "convex_cone hull(S \<union> T) = (\<Union>x \<in> convex_cone hull S. \<Union>y \<in> convex_cone hull T. {x + y})"
  (is "?lhs = ?rhs")
proof
  show "?lhs \<subseteq> ?rhs"
  proof (rule hull_minimal)
    show "S \<union> T \<subseteq> (\<Union>x\<in>convex_cone hull S. \<Union>y\<in>convex_cone hull T. {x + y})"
      apply (clarsimp simp: subset_iff)
      by (metis add_0 convex_cone_hull_contains_0 group_cancel.rule0 hull_inc)
    show "convex_cone (\<Union>x\<in>convex_cone hull S. \<Union>y\<in>convex_cone hull T. {x + y})"
      by (simp add: convex_cone_convex_cone_hull convex_cone_sums)
  qed
next
  show "?rhs \<subseteq> ?lhs"
    by clarify (metis convex_cone_hull_add hull_mono le_sup_iff subsetD subsetI)
qed

lemma convex_cone_singleton [iff]: "convex_cone {0}"
  by (simp add: convex_cone_iff)

lemma convex_hull_subset_convex_cone_hull:
   "convex hull S \<subseteq> convex_cone hull S"
  by (simp add: convex_convex_cone_hull hull_minimal hull_subset)

lemma conic_hull_subset_convex_cone_hull:
   "conic hull S \<subseteq> convex_cone hull S"
  by (simp add: conic_convex_cone_hull hull_minimal hull_subset)

lemma subspace_imp_convex_cone: "subspace S \<Longrightarrow> convex_cone S"
  by (simp add: convex_cone_iff subspace_def)

lemma convex_cone_span: "convex_cone(span S)"
  by (simp add: subspace_imp_convex_cone)

lemma convex_cone_negations:
   "convex_cone S \<Longrightarrow> convex_cone (image uminus S)"
  by (simp add: convex_cone_linear_image module_hom_uminus)

lemma subspace_convex_cone_symmetric:
   "subspace S \<longleftrightarrow> convex_cone S \<and> (\<forall>x \<in> S. -x \<in> S)"
  by (smt (verit) convex_cone_iff scaleR_left.minus subspace_def subspace_neg)

lemma convex_cone_hull_separate_nonempty:
  assumes "S \<noteq> {}"
  shows "convex_cone hull S = conic hull (convex hull S)"   (is "?lhs = ?rhs")
proof
  show "?lhs \<subseteq> ?rhs"
    by (metis assms conic_conic_hull convex_cone_def convex_conic_hull convex_convex_hull hull_subset subset_empty subset_hull)
  show "?rhs \<subseteq> ?lhs"
    by (simp add: conic_convex_cone_hull convex_hull_subset_convex_cone_hull subset_hull)
qed

lemma convex_cone_hull_empty [simp]: "convex_cone hull {} = {0}"
  by (metis convex_cone_hull_contains_0 convex_cone_singleton hull_redundant hull_same)

lemma convex_cone_hull_separate:
   "convex_cone hull S = insert 0 (conic hull (convex hull S))"
proof(cases "S={}")
  case False
  then show ?thesis
    using convex_cone_hull_contains_0 convex_cone_hull_separate_nonempty by blast
qed auto

lemma convex_cone_hull_convex_hull_nonempty:
   "S \<noteq> {} \<Longrightarrow> convex_cone hull S = (\<Union>x \<in> convex hull S. \<Union>c\<in>{0..}. {c *\<^sub>R x})"
  by (force simp: convex_cone_hull_separate_nonempty conic_hull_as_image)

lemma convex_cone_hull_convex_hull:
   "convex_cone hull S = insert 0 (\<Union>x \<in> convex hull S. \<Union>c\<in>{0..}. {c *\<^sub>R x})"
  by (force simp: convex_cone_hull_separate conic_hull_as_image)

lemma convex_cone_hull_linear_image:
   "linear f \<Longrightarrow> convex_cone hull (f ` S) = image f (convex_cone hull S)"
  by (metis (no_types, lifting) conic_hull_linear_image convex_cone_hull_separate convex_hull_linear_image image_insert linear_0)

subsection \<open>Radon's theorem\<close>

text "Formalized by Lars Schewe."

lemma Radon_ex_lemma:
  assumes "finite c" "affine_dependent c"
  shows "\<exists>u. sum u c = 0 \<and> (\<exists>v\<in>c. u v \<noteq> 0) \<and> sum (\<lambda>v. u v *\<^sub>R v) c = 0"
  using affine_dependent_explicit_finite assms by blast

lemma Radon_s_lemma:
  assumes "finite S"
    and "sum f S = (0::real)"
  shows "sum f {x\<in>S. 0 < f x} = - sum f {x\<in>S. f x < 0}"
proof -
  have "\<And>x. (if f x < 0 then f x else 0) + (if 0 < f x then f x else 0) = f x"
    by auto
  then show ?thesis
    using assms by (simp add: sum.inter_filter flip: sum.distrib add_eq_0_iff)
qed

lemma Radon_v_lemma:
  assumes "finite S"
    and "sum f S = 0"
    and "\<forall>x. g x = (0::real) \<longrightarrow> f x = (0::'a::euclidean_space)"
  shows "(sum f {x\<in>S. 0 < g x}) = - sum f {x\<in>S. g x < 0}"
proof -
  have "\<And>x. (if 0 < g x then f x else 0) + (if g x < 0 then f x else 0) = f x"
    using assms by auto
  then show ?thesis
    using assms by (simp add: sum.inter_filter eq_neg_iff_add_eq_0 flip: sum.distrib add_eq_0_iff)
qed

lemma Radon_partition:
  assumes "finite C" "affine_dependent C"
  shows "\<exists>M P. M \<inter> P = {} \<and> M \<union> P = C \<and> (convex hull M) \<inter> (convex hull P) \<noteq> {}"
proof -
  obtain u v where uv: "sum u C = 0" "v\<in>C" "u v \<noteq> 0"  "(\<Sum>v\<in>C. u v *\<^sub>R v) = 0"
    using Radon_ex_lemma[OF assms] by auto
  have fin: "finite {x \<in> C. 0 < u x}" "finite {x \<in> C. 0 > u x}"
    using assms(1) by auto
  define z  where "z = inverse (sum u {x\<in>C. u x > 0}) *\<^sub>R sum (\<lambda>x. u x *\<^sub>R x) {x\<in>C. u x > 0}"
  have "sum u {x \<in> C. 0 < u x} \<noteq> 0"
  proof (cases "u v \<ge> 0")
    case False
    then have "u v < 0" by auto
    then show ?thesis
      by (smt (verit) assms(1) fin(1) mem_Collect_eq sum.neutral_const sum_mono_inv uv)
  next
    case True
    with fin uv show "sum u {x \<in> C. 0 < u x} \<noteq> 0"
      by (smt (verit) fin(1) mem_Collect_eq sum_nonneg_eq_0_iff uv)
  qed
  then have *: "sum u {x\<in>C. u x > 0} > 0"
    unfolding less_le by (metis (no_types, lifting) mem_Collect_eq sum_nonneg)
  moreover have "sum u ({x \<in> C. 0 < u x} \<union> {x \<in> C. u x < 0}) = sum u C"
    "(\<Sum>x\<in>{x \<in> C. 0 < u x} \<union> {x \<in> C. u x < 0}. u x *\<^sub>R x) = (\<Sum>x\<in>C. u x *\<^sub>R x)"
    using assms(1)
    by (rule_tac[!] sum.mono_neutral_left, auto)
  then have "sum u {x \<in> C. 0 < u x} = - sum u {x \<in> C. 0 > u x}"
    "(\<Sum>x\<in>{x \<in> C. 0 < u x}. u x *\<^sub>R x) = - (\<Sum>x\<in>{x \<in> C. 0 > u x}. u x *\<^sub>R x)"
    unfolding eq_neg_iff_add_eq_0
    using uv(1,4)
    by (auto simp: sum.union_inter_neutral[OF fin, symmetric])
  moreover have "\<forall>x\<in>{v \<in> C. u v < 0}. 0 \<le> inverse (sum u {x \<in> C. 0 < u x}) * - u x"
    using * by (fastforce intro: mult_nonneg_nonneg)
  ultimately have "z \<in> convex hull {v \<in> C. u v \<le> 0}"
    unfolding convex_hull_explicit mem_Collect_eq
    apply (rule_tac x="{v \<in> C. u v < 0}" in exI)
    apply (rule_tac x="\<lambda>y. inverse (sum u {x\<in>C. u x > 0}) * - u y" in exI)
    using assms(1) unfolding scaleR_scaleR[symmetric] scaleR_right.sum [symmetric] 
    by (auto simp: z_def sum_negf sum_distrib_left[symmetric])
  moreover have "\<forall>x\<in>{v \<in> C. 0 < u v}. 0 \<le> inverse (sum u {x \<in> C. 0 < u x}) * u x"
    using * by (fastforce intro: mult_nonneg_nonneg)
  then have "z \<in> convex hull {v \<in> C. u v > 0}"
    unfolding convex_hull_explicit mem_Collect_eq
    apply (rule_tac x="{v \<in> C. 0 < u v}" in exI)
    apply (rule_tac x="\<lambda>y. inverse (sum u {x\<in>C. u x > 0}) * u y" in exI)
    using assms(1)
    unfolding scaleR_scaleR[symmetric] scaleR_right.sum [symmetric]
    using * by (auto simp: z_def sum_negf sum_distrib_left[symmetric])
  ultimately show ?thesis
    apply (rule_tac x="{v\<in>C. u v \<le> 0}" in exI)
    apply (rule_tac x="{v\<in>C. u v > 0}" in exI, auto)
    done
qed

theorem Radon:
  assumes "affine_dependent c"
  obtains M P where "M \<subseteq> c" "P \<subseteq> c" "M \<inter> P = {}" "(convex hull M) \<inter> (convex hull P) \<noteq> {}"
  by (smt (verit) Radon_partition affine_dependent_explicit affine_dependent_explicit_finite assms le_sup_iff)


subsection \<open>Helly's theorem\<close>

lemma Helly_induct:
  fixes \<F> :: "'a::euclidean_space set set"
  assumes "card \<F> = n"
    and "n \<ge> DIM('a) + 1"
    and "\<forall>S\<in>\<F>. convex S" "\<forall>T\<subseteq>\<F>. card T = DIM('a) + 1 \<longrightarrow> \<Inter>T \<noteq> {}"
  shows "\<Inter>\<F> \<noteq> {}"
  using assms
proof (induction n arbitrary: \<F>)
  case 0
  then show ?case by auto
next
  case (Suc n)
  have "finite \<F>"
    using \<open>card \<F> = Suc n\<close> by (auto intro: card_ge_0_finite)
  show "\<Inter>\<F> \<noteq> {}"
  proof (cases "n = DIM('a)")
    case True
    then show ?thesis
      by (simp add: Suc.prems)
  next
    case False
    have "\<Inter>(\<F> - {S}) \<noteq> {}" if "S \<in> \<F>" for S
    proof (rule Suc.IH[rule_format])
      show "card (\<F> - {S}) = n"
        by (simp add: Suc.prems(1) \<open>finite \<F>\<close> that)
      show "DIM('a) + 1 \<le> n"
        using False Suc.prems(2) by linarith
      show "\<And>t. \<lbrakk>t \<subseteq> \<F> - {S}; card t = DIM('a) + 1\<rbrakk> \<Longrightarrow> \<Inter>t \<noteq> {}"
        by (simp add: Suc.prems(4) subset_Diff_insert)
    qed (use Suc in auto)
    then have "\<forall>S\<in>\<F>. \<exists>x. x \<in> \<Inter>(\<F> - {S})"
      by blast
    then obtain X where X: "\<And>S. S\<in>\<F> \<Longrightarrow> X S \<in> \<Inter>(\<F> - {S})"
      by metis
    show ?thesis
    proof (cases "inj_on X \<F>")
      case False
      then obtain S T where "S\<noteq>T" and st: "S\<in>\<F>" "T\<in>\<F>" "X S = X T"
        unfolding inj_on_def by auto
      then have *: "\<Inter>\<F> = \<Inter>(\<F> - {S}) \<inter> \<Inter>(\<F> - {T})" by auto
      show ?thesis
        by (metis "*" X disjoint_iff_not_equal st)
    next
      case True
      then obtain M P where mp: "M \<inter> P = {}" "M \<union> P = X ` \<F>" "convex hull M \<inter> convex hull P \<noteq> {}"
        using Radon_partition[of "X ` \<F>"] and affine_dependent_biggerset[of "X ` \<F>"]
        unfolding card_image[OF True] and \<open>card \<F> = Suc n\<close>
        using Suc(3) \<open>finite \<F>\<close> and False
        by auto
      have "M \<subseteq> X ` \<F>" "P \<subseteq> X ` \<F>"
        using mp(2) by auto
      then obtain \<G> \<H> where gh:"M = X ` \<G>" "P = X ` \<H>" "\<G> \<subseteq> \<F>" "\<H> \<subseteq> \<F>"
        unfolding subset_image_iff by auto
      then have "\<F> \<union> (\<G> \<union> \<H>) = \<F>" by auto
      then have \<F>: "\<F> = \<G> \<union> \<H>"
        using inj_on_Un_image_eq_iff[of X \<F> "\<G> \<union> \<H>"] and True
        unfolding mp(2)[unfolded image_Un[symmetric] gh]
        by auto
      have *: "\<G> \<inter> \<H> = {}"
        using gh local.mp(1) by blast
      have "convex hull (X ` \<H>) \<subseteq> \<Inter>\<G>" "convex hull (X ` \<G>) \<subseteq> \<Inter>\<H>"
        by (rule hull_minimal; use X * \<F> in \<open>auto simp: Suc.prems(3) convex_Inter\<close>)+
      then show ?thesis
        unfolding \<F> using mp(3)[unfolded gh] by blast
    qed
  qed 
qed

theorem Helly:
  fixes \<F> :: "'a::euclidean_space set set"
  assumes "card \<F> \<ge> DIM('a) + 1" "\<forall>s\<in>\<F>. convex s"
    and "\<And>t. \<lbrakk>t\<subseteq>\<F>; card t = DIM('a) + 1\<rbrakk> \<Longrightarrow> \<Inter>t \<noteq> {}"
  shows "\<Inter>\<F> \<noteq> {}"
  using Helly_induct assms by blast

subsection \<open>Epigraphs of convex functions\<close>

definition\<^marker>\<open>tag important\<close> "epigraph S (f :: _ \<Rightarrow> real) = {xy. fst xy \<in> S \<and> f (fst xy) \<le> snd xy}"

lemma mem_epigraph: "(x, y) \<in> epigraph S f \<longleftrightarrow> x \<in> S \<and> f x \<le> y"
  unfolding epigraph_def by auto

lemma convex_epigraph: "convex (epigraph S f) \<longleftrightarrow> convex_on S f"
proof safe
  assume L: "convex (epigraph S f)"
  then show "convex_on S f"
    by (fastforce simp: convex_def convex_on_def epigraph_def)
next
  assume "convex_on S f"
  then show "convex (epigraph S f)"
    unfolding convex_def convex_on_def epigraph_def
    apply safe
     apply (rule_tac [2] y="u * f a + v * f aa" in order_trans)
      apply (auto intro!:mult_left_mono add_mono)
    done
qed

lemma convex_epigraphI: "convex_on S f \<Longrightarrow> convex (epigraph S f)"
  unfolding convex_epigraph by auto

lemma convex_epigraph_convex: "convex_on S f \<longleftrightarrow> convex(epigraph S f)"
  by (simp add: convex_epigraph)


subsubsection\<^marker>\<open>tag unimportant\<close> \<open>Use this to derive general bound property of convex function\<close>

lemma convex_on:
  assumes "convex S"
  shows "convex_on S f \<longleftrightarrow>
    (\<forall>k u x. (\<forall>i\<in>{1..k::nat}. 0 \<le> u i \<and> x i \<in> S) \<and> sum u {1..k} = 1 \<longrightarrow>
      f (sum (\<lambda>i. u i *\<^sub>R x i) {1..k}) \<le> sum (\<lambda>i. u i * f(x i)) {1..k})"
  (is "?lhs = (\<forall>k u x. ?rhs k u x)")
proof
  assume ?lhs 
  then have \<section>: "convex {xy. fst xy \<in> S \<and> f (fst xy) \<le> snd xy}"
    by (metis assms convex_epigraph epigraph_def)
  show "\<forall>k u x. ?rhs k u x"
  proof (intro allI)
    fix k u x
    show "?rhs k u x"
      using \<section>
      unfolding  convex mem_Collect_eq fst_sum snd_sum 
      apply safe
      apply (drule_tac x=k in spec)
      apply (drule_tac x=u in spec)
      apply (drule_tac x="\<lambda>i. (x i, f (x i))" in spec)
      apply simp
      done
  qed
next
  assume "\<forall>k u x. ?rhs k u x"
  then show ?lhs
  unfolding convex_epigraph_convex convex epigraph_def Ball_def mem_Collect_eq fst_sum snd_sum
  using assms[unfolded convex] apply clarsimp
  apply (rule_tac y="\<Sum>i = 1..k. u i * f (fst (x i))" in order_trans)
  by (auto simp add: mult_left_mono intro: sum_mono)
qed


subsection\<^marker>\<open>tag unimportant\<close> \<open>A bound within a convex hull\<close>

lemma convex_on_convex_hull_bound:
  assumes "convex_on (convex hull S) f"
    and "\<forall>x\<in>S. f x \<le> b"
  shows "\<forall>x\<in> convex hull S. f x \<le> b"
proof
  fix x
  assume "x \<in> convex hull S"
  then obtain k u v where
    u: "\<forall>i\<in>{1..k::nat}. 0 \<le> u i \<and> v i \<in> S" "sum u {1..k} = 1" "(\<Sum>i = 1..k. u i *\<^sub>R v i) = x"
    unfolding convex_hull_indexed mem_Collect_eq by auto
  have "(\<Sum>i = 1..k. u i * f (v i)) \<le> b"
    using sum_mono[of "{1..k}" "\<lambda>i. u i * f (v i)" "\<lambda>i. u i * b"]
    unfolding sum_distrib_right[symmetric] u(2) mult_1
    using assms(2) mult_left_mono u(1) by blast
  then show "f x \<le> b"
    using assms(1)[unfolded convex_on[OF convex_convex_hull], rule_format, of k u v]
    using hull_inc u by fastforce
qed

lemma convex_set_plus:
  assumes "convex S" and "convex T" shows "convex (S + T)"
  by (metis assms convex_hull_eq convex_hull_set_plus)

lemma convex_set_sum:
  assumes "\<And>i. i \<in> A \<Longrightarrow> convex (B i)"
  shows "convex (\<Sum>i\<in>A. B i)"
  using assms
  by (induction A rule: infinite_finite_induct) (auto simp: convex_set_plus)

lemma finite_set_sum:
  assumes "\<forall>i\<in>A. finite (B i)" shows "finite (\<Sum>i\<in>A. B i)"
  using assms
  by (induction A rule: infinite_finite_induct) (auto simp: finite_set_plus)

lemma box_eq_set_sum_Basis:
  "{x. \<forall>i\<in>Basis. x\<bullet>i \<in> B i} = (\<Sum>i\<in>Basis. (\<lambda>x. x *\<^sub>R i) ` (B i))" (is "?lhs = ?rhs")
proof -
  have "\<And>x. \<forall>i\<in>Basis. x \<bullet> i \<in> B i \<Longrightarrow>
         \<exists>s. x = sum s Basis \<and> (\<forall>i\<in>Basis. s i \<in> (\<lambda>x. x *\<^sub>R i) ` B i)"
    by (metis (mono_tags, lifting) euclidean_representation image_iff)
  moreover
  have "sum f Basis \<bullet> i \<in> B i" if "i \<in> Basis" and f: "\<forall>i\<in>Basis. f i \<in> (\<lambda>x. x *\<^sub>R i) ` B i" for i f
  proof -
    have "(\<Sum>x\<in>Basis - {i}. f x \<bullet> i) = 0"
    proof (intro strip sum.neutral)
      show "f x \<bullet> i = 0" if "x \<in> Basis - {i}" for x
        using that f \<open>i \<in> Basis\<close> inner_Basis that by fastforce
    qed
    then have "(\<Sum>x\<in>Basis. f x \<bullet> i) = f i \<bullet> i"
      by (metis (no_types) \<open>i \<in> Basis\<close> add.right_neutral sum.remove [OF finite_Basis])
    then have "(\<Sum>x\<in>Basis. f x \<bullet> i) \<in> B i"
      using f that(1) by auto
    then show ?thesis
      by (simp add: inner_sum_left)
  qed
  ultimately show ?thesis
    by (subst set_sum_alt [OF finite_Basis]) auto
qed

lemma convex_hull_set_sum:
  "convex hull (\<Sum>i\<in>A. B i) = (\<Sum>i\<in>A. convex hull (B i))"
  by (induction A rule: infinite_finite_induct) (auto simp: convex_hull_set_plus)

end
