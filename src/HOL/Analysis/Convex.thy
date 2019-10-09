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
  Linear_Algebra
  "HOL-Library.Set_Algebras"
begin

subsection \<open>Convexity\<close>

definition\<^marker>\<open>tag important\<close> convex :: "'a::real_vector set \<Rightarrow> bool"
  where "convex s \<longleftrightarrow> (\<forall>x\<in>s. \<forall>y\<in>s. \<forall>u\<ge>0. \<forall>v\<ge>0. u + v = 1 \<longrightarrow> u *\<^sub>R x + v *\<^sub>R y \<in> s)"

lemma convexI:
  assumes "\<And>x y u v. x \<in> s \<Longrightarrow> y \<in> s \<Longrightarrow> 0 \<le> u \<Longrightarrow> 0 \<le> v \<Longrightarrow> u + v = 1 \<Longrightarrow> u *\<^sub>R x + v *\<^sub>R y \<in> s"
  shows "convex s"
  using assms unfolding convex_def by fast

lemma convexD:
  assumes "convex s" and "x \<in> s" and "y \<in> s" and "0 \<le> u" and "0 \<le> v" and "u + v = 1"
  shows "u *\<^sub>R x + v *\<^sub>R y \<in> s"
  using assms unfolding convex_def by fast

lemma convex_alt: "convex s \<longleftrightarrow> (\<forall>x\<in>s. \<forall>y\<in>s. \<forall>u. 0 \<le> u \<and> u \<le> 1 \<longrightarrow> ((1 - u) *\<^sub>R x + u *\<^sub>R y) \<in> s)"
  (is "_ \<longleftrightarrow> ?alt")
proof
  show "convex s" if alt: ?alt
  proof -
    {
      fix x y and u v :: real
      assume mem: "x \<in> s" "y \<in> s"
      assume "0 \<le> u" "0 \<le> v"
      moreover
      assume "u + v = 1"
      then have "u = 1 - v" by auto
      ultimately have "u *\<^sub>R x + v *\<^sub>R y \<in> s"
        using alt [rule_format, OF mem] by auto
    }
    then show ?thesis
      unfolding convex_def by auto
  qed
  show ?alt if "convex s"
    using that by (auto simp: convex_def)
qed

lemma convexD_alt:
  assumes "convex s" "a \<in> s" "b \<in> s" "0 \<le> u" "u \<le> 1"
  shows "((1 - u) *\<^sub>R a + u *\<^sub>R b) \<in> s"
  using assms unfolding convex_alt by auto

lemma mem_convex_alt:
  assumes "convex S" "x \<in> S" "y \<in> S" "u \<ge> 0" "v \<ge> 0" "u + v > 0"
  shows "((u/(u+v)) *\<^sub>R x + (v/(u+v)) *\<^sub>R y) \<in> S"
  apply (rule convexD)
  using assms
       apply (simp_all add: zero_le_divide_iff add_divide_distrib [symmetric])
  done

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
  assumes "finite s"
    and "convex C"
    and "(\<Sum> i \<in> s. a i) = 1"
  assumes "\<And>i. i \<in> s \<Longrightarrow> a i \<ge> 0"
    and "\<And>i. i \<in> s \<Longrightarrow> y i \<in> C"
  shows "(\<Sum> j \<in> s. a j *\<^sub>R y j) \<in> C"
  using assms(1,3,4,5)
proof (induct arbitrary: a set: finite)
  case empty
  then show ?case by simp
next
  case (insert i s) note IH = this(3)
  have "a i + sum a s = 1"
    and "0 \<le> a i"
    and "\<forall>j\<in>s. 0 \<le> a j"
    and "y i \<in> C"
    and "\<forall>j\<in>s. y j \<in> C"
    using insert.hyps(1,2) insert.prems by simp_all
  then have "0 \<le> sum a s"
    by (simp add: sum_nonneg)
  have "a i *\<^sub>R y i + (\<Sum>j\<in>s. a j *\<^sub>R y j) \<in> C"
  proof (cases "sum a s = 0")
    case True
    with \<open>a i + sum a s = 1\<close> have "a i = 1"
      by simp
    from sum_nonneg_0 [OF \<open>finite s\<close> _ True] \<open>\<forall>j\<in>s. 0 \<le> a j\<close> have "\<forall>j\<in>s. a j = 0"
      by simp
    show ?thesis using \<open>a i = 1\<close> and \<open>\<forall>j\<in>s. a j = 0\<close> and \<open>y i \<in> C\<close>
      by simp
  next
    case False
    with \<open>0 \<le> sum a s\<close> have "0 < sum a s"
      by simp
    then have "(\<Sum>j\<in>s. (a j / sum a s) *\<^sub>R y j) \<in> C"
      using \<open>\<forall>j\<in>s. 0 \<le> a j\<close> and \<open>\<forall>j\<in>s. y j \<in> C\<close>
      by (simp add: IH sum_divide_distrib [symmetric])
    from \<open>convex C\<close> and \<open>y i \<in> C\<close> and this and \<open>0 \<le> a i\<close>
      and \<open>0 \<le> sum a s\<close> and \<open>a i + sum a s = 1\<close>
    have "a i *\<^sub>R y i + sum a s *\<^sub>R (\<Sum>j\<in>s. (a j / sum a s) *\<^sub>R y j) \<in> C"
      by (rule convexD)
    then show ?thesis
      by (simp add: scaleR_sum_right False)
  qed
  then show ?case using \<open>finite s\<close> and \<open>i \<notin> s\<close>
    by simp
qed

lemma convex:
  "convex s \<longleftrightarrow> (\<forall>(k::nat) u x. (\<forall>i. 1\<le>i \<and> i\<le>k \<longrightarrow> 0 \<le> u i \<and> x i \<in>s) \<and> (sum u {1..k} = 1)
      \<longrightarrow> sum (\<lambda>i. u i *\<^sub>R x i) {1..k} \<in> s)"
proof safe
  fix k :: nat
  fix u :: "nat \<Rightarrow> real"
  fix x
  assume "convex s"
    "\<forall>i. 1 \<le> i \<and> i \<le> k \<longrightarrow> 0 \<le> u i \<and> x i \<in> s"
    "sum u {1..k} = 1"
  with convex_sum[of "{1 .. k}" s] show "(\<Sum>j\<in>{1 .. k}. u j *\<^sub>R x j) \<in> s"
    by auto
next
  assume *: "\<forall>k u x. (\<forall> i :: nat. 1 \<le> i \<and> i \<le> k \<longrightarrow> 0 \<le> u i \<and> x i \<in> s) \<and> sum u {1..k} = 1
    \<longrightarrow> (\<Sum>i = 1..k. u i *\<^sub>R (x i :: 'a)) \<in> s"
  {
    fix \<mu> :: real
    fix x y :: 'a
    assume xy: "x \<in> s" "y \<in> s"
    assume mu: "\<mu> \<ge> 0" "\<mu> \<le> 1"
    let ?u = "\<lambda>i. if (i :: nat) = 1 then \<mu> else 1 - \<mu>"
    let ?x = "\<lambda>i. if (i :: nat) = 1 then x else y"
    have "{1 :: nat .. 2} \<inter> - {x. x = 1} = {2}"
      by auto
    then have card: "card ({1 :: nat .. 2} \<inter> - {x. x = 1}) = 1"
      by simp
    then have "sum ?u {1 .. 2} = 1"
      using sum.If_cases[of "{(1 :: nat) .. 2}" "\<lambda> x. x = 1" "\<lambda> x. \<mu>" "\<lambda> x. 1 - \<mu>"]
      by auto
    with *[rule_format, of "2" ?u ?x] have s: "(\<Sum>j \<in> {1..2}. ?u j *\<^sub>R ?x j) \<in> s"
      using mu xy by auto
    have grarr: "(\<Sum>j \<in> {Suc (Suc 0)..2}. ?u j *\<^sub>R ?x j) = (1 - \<mu>) *\<^sub>R y"
      using sum.atLeast_Suc_atMost[of "Suc (Suc 0)" 2 "\<lambda> j. (1 - \<mu>) *\<^sub>R y"] by auto
    from sum.atLeast_Suc_atMost[of "Suc 0" 2 "\<lambda> j. ?u j *\<^sub>R ?x j", simplified this]
    have "(\<Sum>j \<in> {1..2}. ?u j *\<^sub>R ?x j) = \<mu> *\<^sub>R x + (1 - \<mu>) *\<^sub>R y"
      by auto
    then have "(1 - \<mu>) *\<^sub>R y + \<mu> *\<^sub>R x \<in> s"
      using s by (auto simp: add.commute)
  }
  then show "convex s"
    unfolding convex_alt by auto
qed


lemma convex_explicit:
  fixes s :: "'a::real_vector set"
  shows "convex s \<longleftrightarrow>
    (\<forall>t u. finite t \<and> t \<subseteq> s \<and> (\<forall>x\<in>t. 0 \<le> u x) \<and> sum u t = 1 \<longrightarrow> sum (\<lambda>x. u x *\<^sub>R x) t \<in> s)"
proof safe
  fix t
  fix u :: "'a \<Rightarrow> real"
  assume "convex s"
    and "finite t"
    and "t \<subseteq> s" "\<forall>x\<in>t. 0 \<le> u x" "sum u t = 1"
  then show "(\<Sum>x\<in>t. u x *\<^sub>R x) \<in> s"
    using convex_sum[of t s u "\<lambda> x. x"] by auto
next
  assume *: "\<forall>t. \<forall> u. finite t \<and> t \<subseteq> s \<and> (\<forall>x\<in>t. 0 \<le> u x) \<and>
    sum u t = 1 \<longrightarrow> (\<Sum>x\<in>t. u x *\<^sub>R x) \<in> s"
  show "convex s"
    unfolding convex_alt
  proof safe
    fix x y
    fix \<mu> :: real
    assume **: "x \<in> s" "y \<in> s" "0 \<le> \<mu>" "\<mu> \<le> 1"
    show "(1 - \<mu>) *\<^sub>R x + \<mu> *\<^sub>R y \<in> s"
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
  assumes "finite s"
  shows "convex s \<longleftrightarrow> (\<forall>u. (\<forall>x\<in>s. 0 \<le> u x) \<and> sum u s = 1 \<longrightarrow> sum (\<lambda>x. u x *\<^sub>R x) s \<in> s)"
  unfolding convex_explicit
  apply safe
  subgoal for u by (erule allE [where x=s], erule allE [where x=u]) auto
  subgoal for t u
  proof -
    have if_distrib_arg: "\<And>P f g x. (if P then f else g) x = (if P then f x else g x)"
      by simp
    assume sum: "\<forall>u. (\<forall>x\<in>s. 0 \<le> u x) \<and> sum u s = 1 \<longrightarrow> (\<Sum>x\<in>s. u x *\<^sub>R x) \<in> s"
    assume *: "\<forall>x\<in>t. 0 \<le> u x" "sum u t = 1"
    assume "t \<subseteq> s"
    then have "s \<inter> t = t" by auto
    with sum[THEN spec[where x="\<lambda>x. if x\<in>t then u x else 0"]] * show "(\<Sum>x\<in>t. u x *\<^sub>R x) \<in> s"
      by (auto simp: assms sum.If_cases if_distrib if_distrib_arg)
  qed
  done


subsection \<open>Functions that are convex on a set\<close>

definition\<^marker>\<open>tag important\<close> convex_on :: "'a::real_vector set \<Rightarrow> ('a \<Rightarrow> real) \<Rightarrow> bool"
  where "convex_on s f \<longleftrightarrow>
    (\<forall>x\<in>s. \<forall>y\<in>s. \<forall>u\<ge>0. \<forall>v\<ge>0. u + v = 1 \<longrightarrow> f (u *\<^sub>R x + v *\<^sub>R y) \<le> u * f x + v * f y)"

lemma convex_onI [intro?]:
  assumes "\<And>t x y. t > 0 \<Longrightarrow> t < 1 \<Longrightarrow> x \<in> A \<Longrightarrow> y \<in> A \<Longrightarrow>
    f ((1 - t) *\<^sub>R x + t *\<^sub>R y) \<le> (1 - t) * f x + t * f y"
  shows "convex_on A f"
  unfolding convex_on_def
proof clarify
  fix x y
  fix u v :: real
  assume A: "x \<in> A" "y \<in> A" "u \<ge> 0" "v \<ge> 0" "u + v = 1"
  from A(5) have [simp]: "v = 1 - u"
    by (simp add: algebra_simps)
  from A(1-4) show "f (u *\<^sub>R x + v *\<^sub>R y) \<le> u * f x + v * f y"
    using assms[of u y x]
    by (cases "u = 0 \<or> u = 1") (auto simp: algebra_simps)
qed

lemma convex_on_linorderI [intro?]:
  fixes A :: "('a::{linorder,real_vector}) set"
  assumes "\<And>t x y. t > 0 \<Longrightarrow> t < 1 \<Longrightarrow> x \<in> A \<Longrightarrow> y \<in> A \<Longrightarrow> x < y \<Longrightarrow>
    f ((1 - t) *\<^sub>R x + t *\<^sub>R y) \<le> (1 - t) * f x + t * f y"
  shows "convex_on A f"
proof
  fix x y
  fix t :: real
  assume A: "x \<in> A" "y \<in> A" "t > 0" "t < 1"
  with assms [of t x y] assms [of "1 - t" y x]
  show "f ((1 - t) *\<^sub>R x + t *\<^sub>R y) \<le> (1 - t) * f x + t * f y"
    by (cases x y rule: linorder_cases) (auto simp: algebra_simps)
qed

lemma convex_onD:
  assumes "convex_on A f"
  shows "\<And>t x y. t \<ge> 0 \<Longrightarrow> t \<le> 1 \<Longrightarrow> x \<in> A \<Longrightarrow> y \<in> A \<Longrightarrow>
    f ((1 - t) *\<^sub>R x + t *\<^sub>R y) \<le> (1 - t) * f x + t * f y"
  using assms by (auto simp: convex_on_def)

lemma convex_onD_Icc:
  assumes "convex_on {x..y} f" "x \<le> (y :: _ :: {real_vector,preorder})"
  shows "\<And>t. t \<ge> 0 \<Longrightarrow> t \<le> 1 \<Longrightarrow>
    f ((1 - t) *\<^sub>R x + t *\<^sub>R y) \<le> (1 - t) * f x + t * f y"
  using assms(2) by (intro convex_onD [OF assms(1)]) simp_all

lemma convex_on_subset: "convex_on t f \<Longrightarrow> s \<subseteq> t \<Longrightarrow> convex_on s f"
  unfolding convex_on_def by auto

lemma convex_on_add [intro]:
  assumes "convex_on s f"
    and "convex_on s g"
  shows "convex_on s (\<lambda>x. f x + g x)"
proof -
  {
    fix x y
    assume "x \<in> s" "y \<in> s"
    moreover
    fix u v :: real
    assume "0 \<le> u" "0 \<le> v" "u + v = 1"
    ultimately
    have "f (u *\<^sub>R x + v *\<^sub>R y) + g (u *\<^sub>R x + v *\<^sub>R y) \<le> (u * f x + v * f y) + (u * g x + v * g y)"
      using assms unfolding convex_on_def by (auto simp: add_mono)
    then have "f (u *\<^sub>R x + v *\<^sub>R y) + g (u *\<^sub>R x + v *\<^sub>R y) \<le> u * (f x + g x) + v * (f y + g y)"
      by (simp add: field_simps)
  }
  then show ?thesis
    unfolding convex_on_def by auto
qed

lemma convex_on_cmul [intro]:
  fixes c :: real
  assumes "0 \<le> c"
    and "convex_on s f"
  shows "convex_on s (\<lambda>x. c * f x)"
proof -
  have *: "u * (c * fx) + v * (c * fy) = c * (u * fx + v * fy)"
    for u c fx v fy :: real
    by (simp add: field_simps)
  show ?thesis using assms(2) and mult_left_mono [OF _ assms(1)]
    unfolding convex_on_def and * by auto
qed

lemma convex_lower:
  assumes "convex_on s f"
    and "x \<in> s"
    and "y \<in> s"
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
  fixes s :: "'a::real_normed_vector set"
  shows "convex_on s (\<lambda>x. dist a x)"
proof (auto simp: convex_on_def dist_norm)
  fix x y
  assume "x \<in> s" "y \<in> s"
  fix u v :: real
  assume "0 \<le> u"
  assume "0 \<le> v"
  assume "u + v = 1"
  have "a = u *\<^sub>R a + v *\<^sub>R a"
    unfolding scaleR_left_distrib[symmetric] and \<open>u + v = 1\<close> by simp
  then have *: "a - (u *\<^sub>R x + v *\<^sub>R y) = (u *\<^sub>R (a - x)) + (v *\<^sub>R (a - y))"
    by (auto simp: algebra_simps)
  show "norm (a - (u *\<^sub>R x + v *\<^sub>R y)) \<le> u * norm (a - x) + v * norm (a - y)"
    unfolding * using norm_triangle_ineq[of "u *\<^sub>R (a - x)" "v *\<^sub>R (a - y)"]
    using \<open>0 \<le> u\<close> \<open>0 \<le> v\<close> by auto
qed


subsection\<^marker>\<open>tag unimportant\<close> \<open>Arithmetic operations on sets preserve convexity\<close>

lemma convex_linear_image:
  assumes "linear f"
    and "convex s"
  shows "convex (f ` s)"
proof -
  interpret f: linear f by fact
  from \<open>convex s\<close> show "convex (f ` s)"
    by (simp add: convex_def f.scaleR [symmetric] f.add [symmetric])
qed

lemma convex_linear_vimage:
  assumes "linear f"
    and "convex s"
  shows "convex (f -` s)"
proof -
  interpret f: linear f by fact
  from \<open>convex s\<close> show "convex (f -` s)"
    by (simp add: convex_def f.add f.scaleR)
qed

lemma convex_scaling:
  assumes "convex s"
  shows "convex ((\<lambda>x. c *\<^sub>R x) ` s)"
proof -
  have "linear (\<lambda>x. c *\<^sub>R x)"
    by (simp add: linearI scaleR_add_right)
  then show ?thesis
    using \<open>convex s\<close> by (rule convex_linear_image)
qed

lemma convex_scaled:
  assumes "convex S"
  shows "convex ((\<lambda>x. x *\<^sub>R c) ` S)"
proof -
  have "linear (\<lambda>x. x *\<^sub>R c)"
    by (simp add: linearI scaleR_add_left)
  then show ?thesis
    using \<open>convex S\<close> by (rule convex_linear_image)
qed

lemma convex_negations:
  assumes "convex S"
  shows "convex ((\<lambda>x. - x) ` S)"
proof -
  have "linear (\<lambda>x. - x)"
    by (simp add: linearI)
  then show ?thesis
    using \<open>convex S\<close> by (rule convex_linear_image)
qed

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

lemma pos_is_convex: "convex {0 :: real <..}"
  unfolding convex_alt
proof safe
  fix y x \<mu> :: real
  assume *: "y > 0" "x > 0" "\<mu> \<ge> 0" "\<mu> \<le> 1"
  {
    assume "\<mu> = 0"
    then have "\<mu> *\<^sub>R x + (1 - \<mu>) *\<^sub>R y = y"
      by simp
    then have "\<mu> *\<^sub>R x + (1 - \<mu>) *\<^sub>R y > 0"
      using * by simp
  }
  moreover
  {
    assume "\<mu> = 1"
    then have "\<mu> *\<^sub>R x + (1 - \<mu>) *\<^sub>R y > 0"
      using * by simp
  }
  moreover
  {
    assume "\<mu> \<noteq> 1" "\<mu> \<noteq> 0"
    then have "\<mu> > 0" "(1 - \<mu>) > 0"
      using * by auto
    then have "\<mu> *\<^sub>R x + (1 - \<mu>) *\<^sub>R y > 0"
      using * by (auto simp: add_pos_pos)
  }
  ultimately show "(1 - \<mu>) *\<^sub>R y + \<mu> *\<^sub>R x > 0"
    by fastforce
qed

lemma convex_on_sum:
  fixes a :: "'a \<Rightarrow> real"
    and y :: "'a \<Rightarrow> 'b::real_vector"
    and f :: "'b \<Rightarrow> real"
  assumes "finite s" "s \<noteq> {}"
    and "convex_on C f"
    and "convex C"
    and "(\<Sum> i \<in> s. a i) = 1"
    and "\<And>i. i \<in> s \<Longrightarrow> a i \<ge> 0"
    and "\<And>i. i \<in> s \<Longrightarrow> y i \<in> C"
  shows "f (\<Sum> i \<in> s. a i *\<^sub>R y i) \<le> (\<Sum> i \<in> s. a i * f (y i))"
  using assms
proof (induct s arbitrary: a rule: finite_ne_induct)
  case (singleton i)
  then have ai: "a i = 1"
    by auto
  then show ?case
    by auto
next
  case (insert i s)
  then have "convex_on C f"
    by simp
  from this[unfolded convex_on_def, rule_format]
  have conv: "\<And>x y \<mu>. x \<in> C \<Longrightarrow> y \<in> C \<Longrightarrow> 0 \<le> \<mu> \<Longrightarrow> \<mu> \<le> 1 \<Longrightarrow>
      f (\<mu> *\<^sub>R x + (1 - \<mu>) *\<^sub>R y) \<le> \<mu> * f x + (1 - \<mu>) * f y"
    by simp
  show ?case
  proof (cases "a i = 1")
    case True
    then have "(\<Sum> j \<in> s. a j) = 0"
      using insert by auto
    then have "\<And>j. j \<in> s \<Longrightarrow> a j = 0"
      using insert by (fastforce simp: sum_nonneg_eq_0_iff)
    then show ?thesis
      using insert by auto
  next
    case False
    from insert have yai: "y i \<in> C" "a i \<ge> 0"
      by auto
    have fis: "finite (insert i s)"
      using insert by auto
    then have ai1: "a i \<le> 1"
      using sum_nonneg_leq_bound[of "insert i s" a] insert by simp
    then have "a i < 1"
      using False by auto
    then have i0: "1 - a i > 0"
      by auto
    let ?a = "\<lambda>j. a j / (1 - a i)"
    have a_nonneg: "?a j \<ge> 0" if "j \<in> s" for j
      using i0 insert that by fastforce
    have "(\<Sum> j \<in> insert i s. a j) = 1"
      using insert by auto
    then have "(\<Sum> j \<in> s. a j) = 1 - a i"
      using sum.insert insert by fastforce
    then have "(\<Sum> j \<in> s. a j) / (1 - a i) = 1"
      using i0 by auto
    then have a1: "(\<Sum> j \<in> s. ?a j) = 1"
      unfolding sum_divide_distrib by simp
    have "convex C" using insert by auto
    then have asum: "(\<Sum> j \<in> s. ?a j *\<^sub>R y j) \<in> C"
      using insert convex_sum [OF \<open>finite s\<close> \<open>convex C\<close> a1 a_nonneg] by auto
    have asum_le: "f (\<Sum> j \<in> s. ?a j *\<^sub>R y j) \<le> (\<Sum> j \<in> s. ?a j * f (y j))"
      using a_nonneg a1 insert by blast
    have "f (\<Sum> j \<in> insert i s. a j *\<^sub>R y j) = f ((\<Sum> j \<in> s. a j *\<^sub>R y j) + a i *\<^sub>R y i)"
      using sum.insert[of s i "\<lambda> j. a j *\<^sub>R y j", OF \<open>finite s\<close> \<open>i \<notin> s\<close>] insert
      by (auto simp only: add.commute)
    also have "\<dots> = f (((1 - a i) * inverse (1 - a i)) *\<^sub>R (\<Sum> j \<in> s. a j *\<^sub>R y j) + a i *\<^sub>R y i)"
      using i0 by auto
    also have "\<dots> = f ((1 - a i) *\<^sub>R (\<Sum> j \<in> s. (a j * inverse (1 - a i)) *\<^sub>R y j) + a i *\<^sub>R y i)"
      using scaleR_right.sum[of "inverse (1 - a i)" "\<lambda> j. a j *\<^sub>R y j" s, symmetric]
      by (auto simp: algebra_simps)
    also have "\<dots> = f ((1 - a i) *\<^sub>R (\<Sum> j \<in> s. ?a j *\<^sub>R y j) + a i *\<^sub>R y i)"
      by (auto simp: divide_inverse)
    also have "\<dots> \<le> (1 - a i) *\<^sub>R f ((\<Sum> j \<in> s. ?a j *\<^sub>R y j)) + a i * f (y i)"
      using conv[of "y i" "(\<Sum> j \<in> s. ?a j *\<^sub>R y j)" "a i", OF yai(1) asum yai(2) ai1]
      by (auto simp: add.commute)
    also have "\<dots> \<le> (1 - a i) * (\<Sum> j \<in> s. ?a j * f (y j)) + a i * f (y i)"
      using add_right_mono [OF mult_left_mono [of _ _ "1 - a i",
            OF asum_le less_imp_le[OF i0]], of "a i * f (y i)"]
      by simp
    also have "\<dots> = (\<Sum> j \<in> s. (1 - a i) * ?a j * f (y j)) + a i * f (y i)"
      unfolding sum_distrib_left[of "1 - a i" "\<lambda> j. ?a j * f (y j)"]
      using i0 by auto
    also have "\<dots> = (\<Sum> j \<in> s. a j * f (y j)) + a i * f (y i)"
      using i0 by auto
    also have "\<dots> = (\<Sum> j \<in> insert i s. a j * f (y j))"
      using insert by auto
    finally show ?thesis
      by simp
  qed
qed

lemma convex_on_alt:
  fixes C :: "'a::real_vector set"
  assumes "convex C"
  shows "convex_on C f \<longleftrightarrow>
    (\<forall>x \<in> C. \<forall> y \<in> C. \<forall> \<mu> :: real. \<mu> \<ge> 0 \<and> \<mu> \<le> 1 \<longrightarrow>
      f (\<mu> *\<^sub>R x + (1 - \<mu>) *\<^sub>R y) \<le> \<mu> * f x + (1 - \<mu>) * f y)"
proof safe
  fix x y
  fix \<mu> :: real
  assume *: "convex_on C f" "x \<in> C" "y \<in> C" "0 \<le> \<mu>" "\<mu> \<le> 1"
  from this[unfolded convex_on_def, rule_format]
  have "0 \<le> u \<Longrightarrow> 0 \<le> v \<Longrightarrow> u + v = 1 \<Longrightarrow> f (u *\<^sub>R x + v *\<^sub>R y) \<le> u * f x + v * f y" for u v
    by auto
  from this [of "\<mu>" "1 - \<mu>", simplified] *
  show "f (\<mu> *\<^sub>R x + (1 - \<mu>) *\<^sub>R y) \<le> \<mu> * f x + (1 - \<mu>) * f y"
    by auto
next
  assume *: "\<forall>x\<in>C. \<forall>y\<in>C. \<forall>\<mu>. 0 \<le> \<mu> \<and> \<mu> \<le> 1 \<longrightarrow>
    f (\<mu> *\<^sub>R x + (1 - \<mu>) *\<^sub>R y) \<le> \<mu> * f x + (1 - \<mu>) * f y"
  {
    fix x y
    fix u v :: real
    assume **: "x \<in> C" "y \<in> C" "u \<ge> 0" "v \<ge> 0" "u + v = 1"
    then have[simp]: "1 - u = v" by auto
    from *[rule_format, of x y u]
    have "f (u *\<^sub>R x + v *\<^sub>R y) \<le> u * f x + v * f y"
      using ** by auto
  }
  then show "convex_on C f"
    unfolding convex_on_def by auto
qed

lemma convex_on_diff:
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
  unfolding convex_on_alt[OF assms(1)]
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
    using convex_on_alt by auto
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
  have less_imp: "f y - f x \<ge> f' x * (y - x)" "f' y * (x - y) \<le> f x - f y"
    if *: "x \<in> C" "y \<in> C" "y > x" for x y :: real
  proof -
    from * have ge: "y - x > 0" "y - x \<ge> 0"
      by auto
    from * have le: "x - y < 0" "x - y \<le> 0"
      by auto
    then obtain z1 where z1: "z1 > x" "z1 < y" "f y - f x = (y - x) * f' z1"
      using subsetD[OF atMostAtLeast_subset_convex[OF \<open>convex C\<close> \<open>x \<in> C\<close> \<open>y \<in> C\<close> \<open>x < y\<close>],
          THEN f', THEN MVT2[OF \<open>x < y\<close>, rule_format, unfolded atLeastAtMost_iff[symmetric]]]
      by auto
    then have "z1 \<in> C"
      using atMostAtLeast_subset_convex \<open>convex C\<close> \<open>x \<in> C\<close> \<open>y \<in> C\<close> \<open>x < y\<close>
      by fastforce
    from z1 have z1': "f x - f y = (x - y) * f' z1"
      by (simp add: field_simps)
    obtain z2 where z2: "z2 > x" "z2 < z1" "f' z1 - f' x = (z1 - x) * f'' z2"
      using subsetD[OF atMostAtLeast_subset_convex[OF \<open>convex C\<close> \<open>x \<in> C\<close> \<open>z1 \<in> C\<close> \<open>x < z1\<close>],
          THEN f'', THEN MVT2[OF \<open>x < z1\<close>, rule_format, unfolded atLeastAtMost_iff[symmetric]]] z1
      by auto
    obtain z3 where z3: "z3 > z1" "z3 < y" "f' y - f' z1 = (y - z1) * f'' z3"
      using subsetD[OF atMostAtLeast_subset_convex[OF \<open>convex C\<close> \<open>z1 \<in> C\<close> \<open>y \<in> C\<close> \<open>z1 < y\<close>],
          THEN f'', THEN MVT2[OF \<open>z1 < y\<close>, rule_format, unfolded atLeastAtMost_iff[symmetric]]] z1
      by auto
    have "f' y - (f x - f y) / (x - y) = f' y - f' z1"
      using * z1' by auto
    also have "\<dots> = (y - z1) * f'' z3"
      using z3 by auto
    finally have cool': "f' y - (f x - f y) / (x - y) = (y - z1) * f'' z3"
      by simp
    have A': "y - z1 \<ge> 0"
      using z1 by auto
    have "z3 \<in> C"
      using z3 * atMostAtLeast_subset_convex \<open>convex C\<close> \<open>x \<in> C\<close> \<open>z1 \<in> C\<close> \<open>x < z1\<close>
      by fastforce
    then have B': "f'' z3 \<ge> 0"
      using assms by auto
    from A' B' have "(y - z1) * f'' z3 \<ge> 0"
      by auto
    from cool' this have "f' y - (f x - f y) / (x - y) \<ge> 0"
      by auto
    from mult_right_mono_neg[OF this le(2)]
    have "f' y * (x - y) - (f x - f y) / (x - y) * (x - y) \<le> 0 * (x - y)"
      by (simp add: algebra_simps)
    then have "f' y * (x - y) - (f x - f y) \<le> 0"
      using le by auto
    then have res: "f' y * (x - y) \<le> f x - f y"
      by auto
    have "(f y - f x) / (y - x) - f' x = f' z1 - f' x"
      using * z1 by auto
    also have "\<dots> = (z1 - x) * f'' z2"
      using z2 by auto
    finally have cool: "(f y - f x) / (y - x) - f' x = (z1 - x) * f'' z2"
      by simp
    have A: "z1 - x \<ge> 0"
      using z1 by auto
    have "z2 \<in> C"
      using z2 z1 * atMostAtLeast_subset_convex \<open>convex C\<close> \<open>z1 \<in> C\<close> \<open>y \<in> C\<close> \<open>z1 < y\<close>
      by fastforce
    then have B: "f'' z2 \<ge> 0"
      using assms by auto
    from A B have "(z1 - x) * f'' z2 \<ge> 0"
      by auto
    with cool have "(f y - f x) / (y - x) - f' x \<ge> 0"
      by auto
    from mult_right_mono[OF this ge(2)]
    have "(f y - f x) / (y - x) * (y - x) - f' x * (y - x) \<ge> 0 * (y - x)"
      by (simp add: algebra_simps)
    then have "f y - f x - f' x * (y - x) \<ge> 0"
      using ge by auto
    then show "f y - f x \<ge> f' x * (y - x)" "f' y * (x - y) \<le> f x - f y"
      using res by auto
  qed
  show ?thesis
  proof (cases "x = y")
    case True
    with x y show ?thesis by auto
  next
    case False
    with less_imp x y show ?thesis
      by (auto simp: neq_iff)
  qed
qed

lemma f''_ge0_imp_convex:
  fixes f :: "real \<Rightarrow> real"
  assumes conv: "convex C"
    and f': "\<And>x. x \<in> C \<Longrightarrow> DERIV f x :> (f' x)"
    and f'': "\<And>x. x \<in> C \<Longrightarrow> DERIV f' x :> (f'' x)"
    and pos: "\<And>x. x \<in> C \<Longrightarrow> f'' x \<ge> 0"
  shows "convex_on C f"
  using f''_imp_f'[OF conv f' f'' pos] assms pos_convex_function
  by fastforce

lemma minus_log_convex:
  fixes b :: real
  assumes "b > 1"
  shows "convex_on {0 <..} (\<lambda> x. - log b x)"
proof -
  have "\<And>z. z > 0 \<Longrightarrow> DERIV (log b) z :> 1 / (ln b * z)"
    using DERIV_log by auto
  then have f': "\<And>z. z > 0 \<Longrightarrow> DERIV (\<lambda> z. - log b z) z :> - 1 / (ln b * z)"
    by (auto simp: DERIV_minus)
  have "\<And>z::real. z > 0 \<Longrightarrow> DERIV inverse z :> - (inverse z ^ Suc (Suc 0))"
    using less_imp_neq[THEN not_sym, THEN DERIV_inverse] by auto
  from this[THEN DERIV_cmult, of _ "- 1 / ln b"]
  have "\<And>z::real. z > 0 \<Longrightarrow>
    DERIV (\<lambda> z. (- 1 / ln b) * inverse z) z :> (- 1 / ln b) * (- (inverse z ^ Suc (Suc 0)))"
    by auto
  then have f''0: "\<And>z::real. z > 0 \<Longrightarrow>
    DERIV (\<lambda> z. - 1 / (ln b * z)) z :> 1 / (ln b * z * z)"
    unfolding inverse_eq_divide by (auto simp: mult.assoc)
  have f''_ge0: "\<And>z::real. z > 0 \<Longrightarrow> 1 / (ln b * z * z) \<ge> 0"
    using \<open>b > 1\<close> by (auto intro!: less_imp_le)
  from f''_ge0_imp_convex[OF pos_is_convex, unfolded greaterThan_iff, OF f' f''0 f''_ge0]
  show ?thesis
    by auto
qed


subsection\<^marker>\<open>tag unimportant\<close> \<open>Convexity of real functions\<close>

lemma convex_on_realI:
  assumes "connected A"
    and "\<And>x. x \<in> A \<Longrightarrow> (f has_real_derivative f' x) (at x)"
    and "\<And>x y. x \<in> A \<Longrightarrow> y \<in> A \<Longrightarrow> x \<le> y \<Longrightarrow> f' x \<le> f' y"
  shows "convex_on A f"
proof (rule convex_on_linorderI)
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
  assumes "A \<subseteq> {0<..}"
  shows "convex_on A (inverse :: real \<Rightarrow> real)"
proof (rule convex_on_subset[OF _ assms], intro convex_on_realI[of _ _ "\<lambda>x. -inverse (x^2)"])
  fix u v :: real
  assume "u \<in> {0<..}" "v \<in> {0<..}" "u \<le> v"
  with assms show "-inverse (u^2) \<le> -inverse (v^2)"
    by (intro le_imp_neg_le le_imp_inverse_le power_mono) (simp_all)
qed (insert assms, auto intro!: derivative_eq_intros simp: field_split_simps power2_eq_square)

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
qed (insert assms(2), simp_all)

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
qed (insert assms(2), simp_all)

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

lemma fst_linear: "linear fst"
  unfolding linear_iff by (simp add: algebra_simps)

lemma snd_linear: "linear snd"
  unfolding linear_iff by (simp add: algebra_simps)

lemma fst_snd_linear: "linear (\<lambda>(x,y). x + y)"
  unfolding linear_iff by (simp add: algebra_simps)

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

lemma sum_delta_notmem:
  assumes "x \<notin> s"
  shows "sum (\<lambda>y. if (y = x) then P x else Q y) s = sum Q s"
    and "sum (\<lambda>y. if (x = y) then P x else Q y) s = sum Q s"
    and "sum (\<lambda>y. if (y = x) then P y else Q y) s = sum Q s"
    and "sum (\<lambda>y. if (x = y) then P y else Q y) s = sum Q s"
  apply (rule_tac [!] sum.cong)
  using assms
  apply auto
  done

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

lemma if_smult: "(if P then x else (y::real)) *\<^sub>R v = (if P then x *\<^sub>R v else y *\<^sub>R v)"
  by (fact if_distrib)

lemma dist_triangle_eq:
  fixes x y z :: "'a::real_inner"
  shows "dist x z = dist x y + dist y z \<longleftrightarrow>
    norm (x - y) *\<^sub>R (y - z) = norm (y - z) *\<^sub>R (x - y)"
proof -
  have *: "x - y + (y - z) = x - z" by auto
  show ?thesis unfolding dist_norm norm_triangle_eq[of "x - y" "y - z", unfolded *]
    by (auto simp:norm_minus_commute)
qed


subsection \<open>Affine set and affine hull\<close>

definition\<^marker>\<open>tag important\<close> affine :: "'a::real_vector set \<Rightarrow> bool"
  where "affine s \<longleftrightarrow> (\<forall>x\<in>s. \<forall>y\<in>s. \<forall>u v. u + v = 1 \<longrightarrow> u *\<^sub>R x + v *\<^sub>R y \<in> s)"

lemma affine_alt: "affine s \<longleftrightarrow> (\<forall>x\<in>s. \<forall>y\<in>s. \<forall>u::real. (1 - u) *\<^sub>R x + u *\<^sub>R y \<in> s)"
  unfolding affine_def by (metis eq_diff_eq')

lemma affine_empty [iff]: "affine {}"
  unfolding affine_def by auto

lemma affine_sing [iff]: "affine {x}"
  unfolding affine_alt by (auto simp: scaleR_left_distrib [symmetric])

lemma affine_UNIV [iff]: "affine UNIV"
  unfolding affine_def by auto

lemma affine_Inter [intro]: "(\<And>s. s\<in>f \<Longrightarrow> affine s) \<Longrightarrow> affine (\<Inter>f)"
  unfolding affine_def by auto

lemma affine_Int[intro]: "affine s \<Longrightarrow> affine t \<Longrightarrow> affine (s \<inter> t)"
  unfolding affine_def by auto

lemma affine_scaling: "affine s \<Longrightarrow> affine (image (\<lambda>x. c *\<^sub>R x) s)"
  apply (clarsimp simp add: affine_def)
  apply (rule_tac x="u *\<^sub>R x + v *\<^sub>R y" in image_eqI)
  apply (auto simp: algebra_simps)
  done

lemma affine_affine_hull [simp]: "affine(affine hull s)"
  unfolding hull_def
  using affine_Inter[of "{t. affine t \<and> s \<subseteq> t}"] by auto

lemma affine_hull_eq[simp]: "(affine hull s = s) \<longleftrightarrow> affine s"
  by (metis affine_affine_hull hull_same)

lemma affine_hyperplane: "affine {x. a \<bullet> x = b}"
  by (simp add: affine_def algebra_simps) (metis distrib_right mult.left_neutral)


subsubsection\<^marker>\<open>tag unimportant\<close> \<open>Some explicit formulations\<close>

text "Formalized by Lars Schewe."

lemma affine:
  fixes V::"'a::real_vector set"
  shows "affine V \<longleftrightarrow>
         (\<forall>S u. finite S \<and> S \<noteq> {} \<and> S \<subseteq> V \<and> sum u S = 1 \<longrightarrow> (\<Sum>x\<in>S. u x *\<^sub>R x) \<in> V)"
proof -
  have "u *\<^sub>R x + v *\<^sub>R y \<in> V" if "x \<in> V" "y \<in> V" "u + v = (1::real)"
    and *: "\<And>S u. \<lbrakk>finite S; S \<noteq> {}; S \<subseteq> V; sum u S = 1\<rbrakk> \<Longrightarrow> (\<Sum>x\<in>S. u x *\<^sub>R x) \<in> V" for x y u v
  proof (cases "x = y")
    case True
    then show ?thesis
      using that by (metis scaleR_add_left scaleR_one)
  next
    case False
    then show ?thesis
      using that *[of "{x,y}" "\<lambda>w. if w = x then u else v"] by auto
  qed
  moreover have "(\<Sum>x\<in>S. u x *\<^sub>R x) \<in> V"
                if *: "\<And>x y u v. \<lbrakk>x\<in>V; y\<in>V; u + v = 1\<rbrakk> \<Longrightarrow> u *\<^sub>R x + v *\<^sub>R y \<in> V"
                  and "finite S" "S \<noteq> {}" "S \<subseteq> V" "sum u S = 1" for S u
  proof -
    define n where "n = card S"
    consider "card S = 0" | "card S = 1" | "card S = 2" | "card S > 2" by linarith
    then show "(\<Sum>x\<in>S. u x *\<^sub>R x) \<in> V"
    proof cases
      assume "card S = 1"
      then obtain a where "S={a}"
        by (auto simp: card_Suc_eq)
      then show ?thesis
        using that by simp
    next
      assume "card S = 2"
      then obtain a b where "S = {a, b}"
        by (metis Suc_1 card_1_singletonE card_Suc_eq)
      then show ?thesis
        using *[of a b] that
        by (auto simp: sum_clauses(2))
    next
      assume "card S > 2"
      then show ?thesis using that n_def
      proof (induct n arbitrary: u S)
        case 0
        then show ?case by auto
      next
        case (Suc n u S)
        have "sum u S = card S" if "\<not> (\<exists>x\<in>S. u x \<noteq> 1)"
          using that unfolding card_eq_sum by auto
        with Suc.prems obtain x where "x \<in> S" and x: "u x \<noteq> 1" by force
        have c: "card (S - {x}) = card S - 1"
          by (simp add: Suc.prems(3) \<open>x \<in> S\<close>)
        have "sum u (S - {x}) = 1 - u x"
          by (simp add: Suc.prems sum_diff1 \<open>x \<in> S\<close>)
        with x have eq1: "inverse (1 - u x) * sum u (S - {x}) = 1"
          by auto
        have inV: "(\<Sum>y\<in>S - {x}. (inverse (1 - u x) * u y) *\<^sub>R y) \<in> V"
        proof (cases "card (S - {x}) > 2")
          case True
          then have S: "S - {x} \<noteq> {}" "card (S - {x}) = n"
            using Suc.prems c by force+
          show ?thesis
          proof (rule Suc.hyps)
            show "(\<Sum>a\<in>S - {x}. inverse (1 - u x) * u a) = 1"
              by (auto simp: eq1 sum_distrib_left[symmetric])
          qed (use S Suc.prems True in auto)
        next
          case False
          then have "card (S - {x}) = Suc (Suc 0)"
            using Suc.prems c by auto
          then obtain a b where ab: "(S - {x}) = {a, b}" "a\<noteq>b"
            unfolding card_Suc_eq by auto
          then show ?thesis
            using eq1 \<open>S \<subseteq> V\<close>
            by (auto simp: sum_distrib_left distrib_left intro!: Suc.prems(2)[of a b])
        qed
        have "u x + (1 - u x) = 1 \<Longrightarrow>
          u x *\<^sub>R x + (1 - u x) *\<^sub>R ((\<Sum>y\<in>S - {x}. u y *\<^sub>R y) /\<^sub>R (1 - u x)) \<in> V"
          by (rule Suc.prems) (use \<open>x \<in> S\<close> Suc.prems inV in \<open>auto simp: scaleR_right.sum\<close>)
        moreover have "(\<Sum>a\<in>S. u a *\<^sub>R a) = u x *\<^sub>R x + (\<Sum>a\<in>S - {x}. u a *\<^sub>R a)"
          by (meson Suc.prems(3) sum.remove \<open>x \<in> S\<close>)
        ultimately show "(\<Sum>x\<in>S. u x *\<^sub>R x) \<in> V"
          by (simp add: x)
      qed
    qed (use \<open>S\<noteq>{}\<close> \<open>finite S\<close> in auto)
  qed
  ultimately show ?thesis
    unfolding affine_def by meson
qed


lemma affine_hull_explicit:
  "affine hull p = {y. \<exists>S u. finite S \<and> S \<noteq> {} \<and> S \<subseteq> p \<and> sum u S = 1 \<and> sum (\<lambda>v. u v *\<^sub>R v) S = y}"
  (is "_ = ?rhs")
proof (rule hull_unique)
  show "p \<subseteq> ?rhs"
  proof (intro subsetI CollectI exI conjI)
    show "\<And>x. sum (\<lambda>z. 1) {x} = 1"
      by auto
  qed auto
  show "?rhs \<subseteq> T" if "p \<subseteq> T" "affine T" for T
    using that unfolding affine by blast
  show "affine ?rhs"
    unfolding affine_def
  proof clarify
    fix u v :: real and sx ux sy uy
    assume uv: "u + v = 1"
      and x: "finite sx" "sx \<noteq> {}" "sx \<subseteq> p" "sum ux sx = (1::real)"
      and y: "finite sy" "sy \<noteq> {}" "sy \<subseteq> p" "sum uy sy = (1::real)" 
    have **: "(sx \<union> sy) \<inter> sx = sx" "(sx \<union> sy) \<inter> sy = sy"
      by auto
    show "\<exists>S w. finite S \<and> S \<noteq> {} \<and> S \<subseteq> p \<and>
        sum w S = 1 \<and> (\<Sum>v\<in>S. w v *\<^sub>R v) = u *\<^sub>R (\<Sum>v\<in>sx. ux v *\<^sub>R v) + v *\<^sub>R (\<Sum>v\<in>sy. uy v *\<^sub>R v)"
    proof (intro exI conjI)
      show "finite (sx \<union> sy)"
        using x y by auto
      show "sum (\<lambda>i. (if i\<in>sx then u * ux i else 0) + (if i\<in>sy then v * uy i else 0)) (sx \<union> sy) = 1"
        using x y uv
        by (simp add: sum_Un sum.distrib sum.inter_restrict[symmetric] sum_distrib_left [symmetric] **)
      have "(\<Sum>i\<in>sx \<union> sy. ((if i \<in> sx then u * ux i else 0) + (if i \<in> sy then v * uy i else 0)) *\<^sub>R i)
          = (\<Sum>i\<in>sx. (u * ux i) *\<^sub>R i) + (\<Sum>i\<in>sy. (v * uy i) *\<^sub>R i)"
        using x y
        unfolding scaleR_left_distrib scaleR_zero_left if_smult
        by (simp add: sum_Un sum.distrib sum.inter_restrict[symmetric]  **)
      also have "\<dots> = u *\<^sub>R (\<Sum>v\<in>sx. ux v *\<^sub>R v) + v *\<^sub>R (\<Sum>v\<in>sy. uy v *\<^sub>R v)"
        unfolding scaleR_scaleR[symmetric] scaleR_right.sum [symmetric] by blast
      finally show "(\<Sum>i\<in>sx \<union> sy. ((if i \<in> sx then u * ux i else 0) + (if i \<in> sy then v * uy i else 0)) *\<^sub>R i) 
                  = u *\<^sub>R (\<Sum>v\<in>sx. ux v *\<^sub>R v) + v *\<^sub>R (\<Sum>v\<in>sy. uy v *\<^sub>R v)" .
    qed (use x y in auto)
  qed
qed

lemma affine_hull_finite:
  assumes "finite S"
  shows "affine hull S = {y. \<exists>u. sum u S = 1 \<and> sum (\<lambda>v. u v *\<^sub>R v) S = y}"
proof -
  have *: "\<exists>h. sum h S = 1 \<and> (\<Sum>v\<in>S. h v *\<^sub>R v) = x" 
    if "F \<subseteq> S" "finite F" "F \<noteq> {}" and sum: "sum u F = 1" and x: "(\<Sum>v\<in>F. u v *\<^sub>R v) = x" for x F u
  proof -
    have "S \<inter> F = F"
      using that by auto
    show ?thesis
    proof (intro exI conjI)
      show "(\<Sum>x\<in>S. if x \<in> F then u x else 0) = 1"
        by (metis (mono_tags, lifting) \<open>S \<inter> F = F\<close> assms sum.inter_restrict sum)
      show "(\<Sum>v\<in>S. (if v \<in> F then u v else 0) *\<^sub>R v) = x"
        by (simp add: if_smult cong: if_cong) (metis (no_types) \<open>S \<inter> F = F\<close> assms sum.inter_restrict x)
    qed
  qed
  show ?thesis
    unfolding affine_hull_explicit using assms
    by (fastforce dest: *)
qed


subsubsection\<^marker>\<open>tag unimportant\<close> \<open>Stepping theorems and hence small special cases\<close>

lemma affine_hull_empty[simp]: "affine hull {} = {}"
  by simp

lemma affine_hull_finite_step:
  fixes y :: "'a::real_vector"
  shows "finite S \<Longrightarrow>
      (\<exists>u. sum u (insert a S) = w \<and> sum (\<lambda>x. u x *\<^sub>R x) (insert a S) = y) \<longleftrightarrow>
      (\<exists>v u. sum u S = w - v \<and> sum (\<lambda>x. u x *\<^sub>R x) S = y - v *\<^sub>R a)" (is "_ \<Longrightarrow> ?lhs = ?rhs")
proof -
  assume fin: "finite S"
  show "?lhs = ?rhs"
  proof
    assume ?lhs
    then obtain u where u: "sum u (insert a S) = w \<and> (\<Sum>x\<in>insert a S. u x *\<^sub>R x) = y"
      by auto
    show ?rhs
    proof (cases "a \<in> S")
      case True
      then show ?thesis
        using u by (simp add: insert_absorb) (metis diff_zero real_vector.scale_zero_left)
    next
      case False
      show ?thesis
        by (rule exI [where x="u a"]) (use u fin False in auto)
    qed
  next
    assume ?rhs
    then obtain v u where vu: "sum u S = w - v"  "(\<Sum>x\<in>S. u x *\<^sub>R x) = y - v *\<^sub>R a"
      by auto
    have *: "\<And>x M. (if x = a then v else M) *\<^sub>R x = (if x = a then v *\<^sub>R x else M *\<^sub>R x)"
      by auto
    show ?lhs
    proof (cases "a \<in> S")
      case True
      show ?thesis
        by (rule exI [where x="\<lambda>x. (if x=a then v else 0) + u x"])
           (simp add: True scaleR_left_distrib sum.distrib sum_clauses fin vu * cong: if_cong)
    next
      case False
      then show ?thesis
        apply (rule_tac x="\<lambda>x. if x=a then v else u x" in exI) 
        apply (simp add: vu sum_clauses(2)[OF fin] *)
        by (simp add: sum_delta_notmem(3) vu)
    qed
  qed
qed

lemma affine_hull_2:
  fixes a b :: "'a::real_vector"
  shows "affine hull {a,b} = {u *\<^sub>R a + v *\<^sub>R b| u v. (u + v = 1)}"
  (is "?lhs = ?rhs")
proof -
  have *:
    "\<And>x y z. z = x - y \<longleftrightarrow> y + z = (x::real)"
    "\<And>x y z. z = x - y \<longleftrightarrow> y + z = (x::'a)" by auto
  have "?lhs = {y. \<exists>u. sum u {a, b} = 1 \<and> (\<Sum>v\<in>{a, b}. u v *\<^sub>R v) = y}"
    using affine_hull_finite[of "{a,b}"] by auto
  also have "\<dots> = {y. \<exists>v u. u b = 1 - v \<and> u b *\<^sub>R b = y - v *\<^sub>R a}"
    by (simp add: affine_hull_finite_step[of "{b}" a])
  also have "\<dots> = ?rhs" unfolding * by auto
  finally show ?thesis by auto
qed

lemma affine_hull_3:
  fixes a b c :: "'a::real_vector"
  shows "affine hull {a,b,c} = { u *\<^sub>R a + v *\<^sub>R b + w *\<^sub>R c| u v w. u + v + w = 1}"
proof -
  have *:
    "\<And>x y z. z = x - y \<longleftrightarrow> y + z = (x::real)"
    "\<And>x y z. z = x - y \<longleftrightarrow> y + z = (x::'a)" by auto
  show ?thesis
    apply (simp add: affine_hull_finite affine_hull_finite_step)
    unfolding *
    apply safe
     apply (metis add.assoc)
    apply (rule_tac x=u in exI, force)
    done
qed

lemma mem_affine:
  assumes "affine S" "x \<in> S" "y \<in> S" "u + v = 1"
  shows "u *\<^sub>R x + v *\<^sub>R y \<in> S"
  using assms affine_def[of S] by auto

lemma mem_affine_3:
  assumes "affine S" "x \<in> S" "y \<in> S" "z \<in> S" "u + v + w = 1"
  shows "u *\<^sub>R x + v *\<^sub>R y + w *\<^sub>R z \<in> S"
proof -
  have "u *\<^sub>R x + v *\<^sub>R y + w *\<^sub>R z \<in> affine hull {x, y, z}"
    using affine_hull_3[of x y z] assms by auto
  moreover
  have "affine hull {x, y, z} \<subseteq> affine hull S"
    using hull_mono[of "{x, y, z}" "S"] assms by auto
  moreover
  have "affine hull S = S"
    using assms affine_hull_eq[of S] by auto
  ultimately show ?thesis by auto
qed

lemma mem_affine_3_minus:
  assumes "affine S" "x \<in> S" "y \<in> S" "z \<in> S"
  shows "x + v *\<^sub>R (y-z) \<in> S"
  using mem_affine_3[of S x y z 1 v "-v"] assms
  by (simp add: algebra_simps)

corollary mem_affine_3_minus2:
    "\<lbrakk>affine S; x \<in> S; y \<in> S; z \<in> S\<rbrakk> \<Longrightarrow> x - v *\<^sub>R (y-z) \<in> S"
  by (metis add_uminus_conv_diff mem_affine_3_minus real_vector.scale_minus_left)


subsubsection\<^marker>\<open>tag unimportant\<close> \<open>Some relations between affine hull and subspaces\<close>

lemma affine_hull_insert_subset_span:
  "affine hull (insert a S) \<subseteq> {a + v| v . v \<in> span {x - a | x . x \<in> S}}"
proof -
  have "\<exists>v T u. x = a + v \<and> (finite T \<and> T \<subseteq> {x - a |x. x \<in> S} \<and> (\<Sum>v\<in>T. u v *\<^sub>R v) = v)"
    if "finite F" "F \<noteq> {}" "F \<subseteq> insert a S" "sum u F = 1" "(\<Sum>v\<in>F. u v *\<^sub>R v) = x"
    for x F u
  proof -
    have *: "(\<lambda>x. x - a) ` (F - {a}) \<subseteq> {x - a |x. x \<in> S}"
      using that by auto
    show ?thesis
    proof (intro exI conjI)
      show "finite ((\<lambda>x. x - a) ` (F - {a}))"
        by (simp add: that(1))
      show "(\<Sum>v\<in>(\<lambda>x. x - a) ` (F - {a}). u(v+a) *\<^sub>R v) = x-a"
        by (simp add: sum.reindex[unfolded inj_on_def] algebra_simps
            sum_subtractf scaleR_left.sum[symmetric] sum_diff1 that)
    qed (use \<open>F \<subseteq> insert a S\<close> in auto)
  qed
  then show ?thesis
    unfolding affine_hull_explicit span_explicit by blast
qed

lemma affine_hull_insert_span:
  assumes "a \<notin> S"
  shows "affine hull (insert a S) = {a + v | v . v \<in> span {x - a | x.  x \<in> S}}"
proof -
  have *: "\<exists>G u. finite G \<and> G \<noteq> {} \<and> G \<subseteq> insert a S \<and> sum u G = 1 \<and> (\<Sum>v\<in>G. u v *\<^sub>R v) = y"
    if "v \<in> span {x - a |x. x \<in> S}" "y = a + v" for y v
  proof -
    from that
    obtain T u where u: "finite T" "T \<subseteq> {x - a |x. x \<in> S}" "a + (\<Sum>v\<in>T. u v *\<^sub>R v) = y"
      unfolding span_explicit by auto
    define F where "F = (\<lambda>x. x + a) ` T"
    have F: "finite F" "F \<subseteq> S" "(\<Sum>v\<in>F. u (v - a) *\<^sub>R (v - a)) = y - a"
      unfolding F_def using u by (auto simp: sum.reindex[unfolded inj_on_def])
    have *: "F \<inter> {a} = {}" "F \<inter> - {a} = F"
      using F assms by auto
    show "\<exists>G u. finite G \<and> G \<noteq> {} \<and> G \<subseteq> insert a S \<and> sum u G = 1 \<and> (\<Sum>v\<in>G. u v *\<^sub>R v) = y"
      apply (rule_tac x = "insert a F" in exI)
      apply (rule_tac x = "\<lambda>x. if x=a then 1 - sum (\<lambda>x. u (x - a)) F else u (x - a)" in exI)
      using assms F
      apply (auto simp:  sum_clauses sum.If_cases if_smult sum_subtractf scaleR_left.sum algebra_simps *)
      done
  qed
  show ?thesis
    by (intro subset_antisym affine_hull_insert_subset_span) (auto simp: affine_hull_explicit dest!: *)
qed

lemma affine_hull_span:
  assumes "a \<in> S"
  shows "affine hull S = {a + v | v. v \<in> span {x - a | x. x \<in> S - {a}}}"
  using affine_hull_insert_span[of a "S - {a}", unfolded insert_Diff[OF assms]] by auto


subsubsection\<^marker>\<open>tag unimportant\<close> \<open>Parallel affine sets\<close>

definition affine_parallel :: "'a::real_vector set \<Rightarrow> 'a::real_vector set \<Rightarrow> bool"
  where "affine_parallel S T \<longleftrightarrow> (\<exists>a. T = (\<lambda>x. a + x) ` S)"

lemma affine_parallel_expl_aux:
  fixes S T :: "'a::real_vector set"
  assumes "\<And>x. x \<in> S \<longleftrightarrow> a + x \<in> T"
  shows "T = (\<lambda>x. a + x) ` S"
proof -
  have "x \<in> ((\<lambda>x. a + x) ` S)" if "x \<in> T" for x
    using that
    by (simp add: image_iff) (metis add.commute diff_add_cancel assms)
  moreover have "T \<ge> (\<lambda>x. a + x) ` S"
    using assms by auto
  ultimately show ?thesis by auto
qed

lemma affine_parallel_expl: "affine_parallel S T \<longleftrightarrow> (\<exists>a. \<forall>x. x \<in> S \<longleftrightarrow> a + x \<in> T)"
  by (auto simp add: affine_parallel_def)
    (use affine_parallel_expl_aux [of S _ T] in blast)

lemma affine_parallel_reflex: "affine_parallel S S"
  unfolding affine_parallel_def
  using image_add_0 by blast

lemma affine_parallel_commut:
  assumes "affine_parallel A B"
  shows "affine_parallel B A"
proof -
  from assms obtain a where B: "B = (\<lambda>x. a + x) ` A"
    unfolding affine_parallel_def by auto
  have [simp]: "(\<lambda>x. x - a) = plus (- a)" by (simp add: fun_eq_iff)
  from B show ?thesis
    using translation_galois [of B a A]
    unfolding affine_parallel_def by blast
qed

lemma affine_parallel_assoc:
  assumes "affine_parallel A B"
    and "affine_parallel B C"
  shows "affine_parallel A C"
proof -
  from assms obtain ab where "B = (\<lambda>x. ab + x) ` A"
    unfolding affine_parallel_def by auto
  moreover
  from assms obtain bc where "C = (\<lambda>x. bc + x) ` B"
    unfolding affine_parallel_def by auto
  ultimately show ?thesis
    using translation_assoc[of bc ab A] unfolding affine_parallel_def by auto
qed

lemma affine_translation_aux:
  fixes a :: "'a::real_vector"
  assumes "affine ((\<lambda>x. a + x) ` S)"
  shows "affine S"
proof -
  {
    fix x y u v
    assume xy: "x \<in> S" "y \<in> S" "(u :: real) + v = 1"
    then have "(a + x) \<in> ((\<lambda>x. a + x) ` S)" "(a + y) \<in> ((\<lambda>x. a + x) ` S)"
      by auto
    then have h1: "u *\<^sub>R  (a + x) + v *\<^sub>R (a + y) \<in> (\<lambda>x. a + x) ` S"
      using xy assms unfolding affine_def by auto
    have "u *\<^sub>R (a + x) + v *\<^sub>R (a + y) = (u + v) *\<^sub>R a + (u *\<^sub>R x + v *\<^sub>R y)"
      by (simp add: algebra_simps)
    also have "\<dots> = a + (u *\<^sub>R x + v *\<^sub>R y)"
      using \<open>u + v = 1\<close> by auto
    ultimately have "a + (u *\<^sub>R x + v *\<^sub>R y) \<in> (\<lambda>x. a + x) ` S"
      using h1 by auto
    then have "u *\<^sub>R x + v *\<^sub>R y \<in> S" by auto
  }
  then show ?thesis unfolding affine_def by auto
qed

lemma affine_translation:
  "affine S \<longleftrightarrow> affine ((+) a ` S)" for a :: "'a::real_vector"
proof
  show "affine ((+) a ` S)" if "affine S"
    using that translation_assoc [of "- a" a S]
    by (auto intro: affine_translation_aux [of "- a" "((+) a ` S)"])
  show "affine S" if "affine ((+) a ` S)"
    using that by (rule affine_translation_aux)
qed

lemma parallel_is_affine:
  fixes S T :: "'a::real_vector set"
  assumes "affine S" "affine_parallel S T"
  shows "affine T"
proof -
  from assms obtain a where "T = (\<lambda>x. a + x) ` S"
    unfolding affine_parallel_def by auto
  then show ?thesis
    using affine_translation assms by auto
qed

lemma subspace_imp_affine: "subspace s \<Longrightarrow> affine s"
  unfolding subspace_def affine_def by auto


subsubsection\<^marker>\<open>tag unimportant\<close> \<open>Subspace parallel to an affine set\<close>

lemma subspace_affine: "subspace S \<longleftrightarrow> affine S \<and> 0 \<in> S"
proof -
  have h0: "subspace S \<Longrightarrow> affine S \<and> 0 \<in> S"
    using subspace_imp_affine[of S] subspace_0 by auto
  {
    assume assm: "affine S \<and> 0 \<in> S"
    {
      fix c :: real
      fix x
      assume x: "x \<in> S"
      have "c *\<^sub>R x = (1-c) *\<^sub>R 0 + c *\<^sub>R x" by auto
      moreover
      have "(1 - c) *\<^sub>R 0 + c *\<^sub>R x \<in> S"
        using affine_alt[of S] assm x by auto
      ultimately have "c *\<^sub>R x \<in> S" by auto
    }
    then have h1: "\<forall>c. \<forall>x \<in> S. c *\<^sub>R x \<in> S" by auto

    {
      fix x y
      assume xy: "x \<in> S" "y \<in> S"
      define u where "u = (1 :: real)/2"
      have "(1/2) *\<^sub>R (x+y) = (1/2) *\<^sub>R (x+y)"
        by auto
      moreover
      have "(1/2) *\<^sub>R (x+y)=(1/2) *\<^sub>R x + (1-(1/2)) *\<^sub>R y"
        by (simp add: algebra_simps)
      moreover
      have "(1 - u) *\<^sub>R x + u *\<^sub>R y \<in> S"
        using affine_alt[of S] assm xy by auto
      ultimately
      have "(1/2) *\<^sub>R (x+y) \<in> S"
        using u_def by auto
      moreover
      have "x + y = 2 *\<^sub>R ((1/2) *\<^sub>R (x+y))"
        by auto
      ultimately
      have "x + y \<in> S"
        using h1[rule_format, of "(1/2) *\<^sub>R (x+y)" "2"] by auto
    }
    then have "\<forall>x \<in> S. \<forall>y \<in> S. x + y \<in> S"
      by auto
    then have "subspace S"
      using h1 assm unfolding subspace_def by auto
  }
  then show ?thesis using h0 by metis
qed

lemma affine_diffs_subspace:
  assumes "affine S" "a \<in> S"
  shows "subspace ((\<lambda>x. (-a)+x) ` S)"
proof -
  have [simp]: "(\<lambda>x. x - a) = plus (- a)" by (simp add: fun_eq_iff)
  have "affine ((\<lambda>x. (-a)+x) ` S)"
    using affine_translation assms by blast
  moreover have "0 \<in> ((\<lambda>x. (-a)+x) ` S)"
    using assms exI[of "(\<lambda>x. x\<in>S \<and> -a+x = 0)" a] by auto
  ultimately show ?thesis using subspace_affine by auto
qed

lemma affine_diffs_subspace_subtract:
  "subspace ((\<lambda>x. x - a) ` S)" if "affine S" "a \<in> S"
  using that affine_diffs_subspace [of _ a] by simp

lemma parallel_subspace_explicit:
  assumes "affine S"
    and "a \<in> S"
  assumes "L \<equiv> {y. \<exists>x \<in> S. (-a) + x = y}"
  shows "subspace L \<and> affine_parallel S L"
proof -
  from assms have "L = plus (- a) ` S" by auto
  then have par: "affine_parallel S L"
    unfolding affine_parallel_def ..
  then have "affine L" using assms parallel_is_affine by auto
  moreover have "0 \<in> L"
    using assms by auto
  ultimately show ?thesis
    using subspace_affine par by auto
qed

lemma parallel_subspace_aux:
  assumes "subspace A"
    and "subspace B"
    and "affine_parallel A B"
  shows "A \<supseteq> B"
proof -
  from assms obtain a where a: "\<forall>x. x \<in> A \<longleftrightarrow> a + x \<in> B"
    using affine_parallel_expl[of A B] by auto
  then have "-a \<in> A"
    using assms subspace_0[of B] by auto
  then have "a \<in> A"
    using assms subspace_neg[of A "-a"] by auto
  then show ?thesis
    using assms a unfolding subspace_def by auto
qed

lemma parallel_subspace:
  assumes "subspace A"
    and "subspace B"
    and "affine_parallel A B"
  shows "A = B"
proof
  show "A \<supseteq> B"
    using assms parallel_subspace_aux by auto
  show "A \<subseteq> B"
    using assms parallel_subspace_aux[of B A] affine_parallel_commut by auto
qed

lemma affine_parallel_subspace:
  assumes "affine S" "S \<noteq> {}"
  shows "\<exists>!L. subspace L \<and> affine_parallel S L"
proof -
  have ex: "\<exists>L. subspace L \<and> affine_parallel S L"
    using assms parallel_subspace_explicit by auto
  {
    fix L1 L2
    assume ass: "subspace L1 \<and> affine_parallel S L1" "subspace L2 \<and> affine_parallel S L2"
    then have "affine_parallel L1 L2"
      using affine_parallel_commut[of S L1] affine_parallel_assoc[of L1 S L2] by auto
    then have "L1 = L2"
      using ass parallel_subspace by auto
  }
  then show ?thesis using ex by auto
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

lemma cone_cone_hull: "cone (cone hull s)"
  unfolding hull_def by auto

lemma cone_hull_eq: "cone hull s = s \<longleftrightarrow> cone s"
  apply (rule hull_eq)
  using cone_Inter
  unfolding subset_eq
  apply auto
  done

lemma mem_cone:
  assumes "cone S" "x \<in> S" "c \<ge> 0"
  shows "c *\<^sub>R x \<in> S"
  using assms cone_def[of S] by auto

lemma cone_contains_0:
  assumes "cone S"
  shows "S \<noteq> {} \<longleftrightarrow> 0 \<in> S"
proof -
  {
    assume "S \<noteq> {}"
    then obtain a where "a \<in> S" by auto
    then have "0 \<in> S"
      using assms mem_cone[of S a 0] by auto
  }
  then show ?thesis by auto
qed

lemma cone_0: "cone {0}"
  unfolding cone_def by auto

lemma cone_Union[intro]: "(\<forall>s\<in>f. cone s) \<longrightarrow> cone (\<Union>f)"
  unfolding cone_def by blast

lemma cone_iff:
  assumes "S \<noteq> {}"
  shows "cone S \<longleftrightarrow> 0 \<in> S \<and> (\<forall>c. c > 0 \<longrightarrow> ((*\<^sub>R) c) ` S = S)"
proof -
  {
    assume "cone S"
    {
      fix c :: real
      assume "c > 0"
      {
        fix x
        assume "x \<in> S"
        then have "x \<in> ((*\<^sub>R) c) ` S"
          unfolding image_def
          using \<open>cone S\<close> \<open>c>0\<close> mem_cone[of S x "1/c"]
            exI[of "(\<lambda>t. t \<in> S \<and> x = c *\<^sub>R t)" "(1 / c) *\<^sub>R x"]
          by auto
      }
      moreover
      {
        fix x
        assume "x \<in> ((*\<^sub>R) c) ` S"
        then have "x \<in> S"
          using \<open>cone S\<close> \<open>c > 0\<close>
          unfolding cone_def image_def \<open>c > 0\<close> by auto
      }
      ultimately have "((*\<^sub>R) c) ` S = S" by blast
    }
    then have "0 \<in> S \<and> (\<forall>c. c > 0 \<longrightarrow> ((*\<^sub>R) c) ` S = S)"
      using \<open>cone S\<close> cone_contains_0[of S] assms by auto
  }
  moreover
  {
    assume a: "0 \<in> S \<and> (\<forall>c. c > 0 \<longrightarrow> ((*\<^sub>R) c) ` S = S)"
    {
      fix x
      assume "x \<in> S"
      fix c1 :: real
      assume "c1 \<ge> 0"
      then have "c1 = 0 \<or> c1 > 0" by auto
      then have "c1 *\<^sub>R x \<in> S" using a \<open>x \<in> S\<close> by auto
    }
    then have "cone S" unfolding cone_def by auto
  }
  ultimately show ?thesis by blast
qed

lemma cone_hull_empty: "cone hull {} = {}"
  by (metis cone_empty cone_hull_eq)

lemma cone_hull_empty_iff: "S = {} \<longleftrightarrow> cone hull S = {}"
  by (metis bot_least cone_hull_empty hull_subset xtrans(5))

lemma cone_hull_contains_0: "S \<noteq> {} \<longleftrightarrow> 0 \<in> cone hull S"
  using cone_cone_hull[of S] cone_contains_0[of "cone hull S"] cone_hull_empty_iff[of S]
  by auto

lemma mem_cone_hull:
  assumes "x \<in> S" "c \<ge> 0"
  shows "c *\<^sub>R x \<in> cone hull S"
  by (metis assms cone_cone_hull hull_inc mem_cone)

proposition cone_hull_expl: "cone hull S = {c *\<^sub>R x | c x. c \<ge> 0 \<and> x \<in> S}"
  (is "?lhs = ?rhs")
proof -
  {
    fix x
    assume "x \<in> ?rhs"
    then obtain cx :: real and xx where x: "x = cx *\<^sub>R xx" "cx \<ge> 0" "xx \<in> S"
      by auto
    fix c :: real
    assume c: "c \<ge> 0"
    then have "c *\<^sub>R x = (c * cx) *\<^sub>R xx"
      using x by (simp add: algebra_simps)
    moreover
    have "c * cx \<ge> 0" using c x by auto
    ultimately
    have "c *\<^sub>R x \<in> ?rhs" using x by auto
  }
  then have "cone ?rhs"
    unfolding cone_def by auto
  then have "?rhs \<in> Collect cone"
    unfolding mem_Collect_eq by auto
  {
    fix x
    assume "x \<in> S"
    then have "1 *\<^sub>R x \<in> ?rhs"
      apply auto
      apply (rule_tac x = 1 in exI, auto)
      done
    then have "x \<in> ?rhs" by auto
  }
  then have "S \<subseteq> ?rhs" by auto
  then have "?lhs \<subseteq> ?rhs"
    using \<open>?rhs \<in> Collect cone\<close> hull_minimal[of S "?rhs" "cone"] by auto
  moreover
  {
    fix x
    assume "x \<in> ?rhs"
    then obtain cx :: real and xx where x: "x = cx *\<^sub>R xx" "cx \<ge> 0" "xx \<in> S"
      by auto
    then have "xx \<in> cone hull S"
      using hull_subset[of S] by auto
    then have "x \<in> ?lhs"
      using x cone_cone_hull[of S] cone_def[of "cone hull S"] by auto
  }
  ultimately show ?thesis by auto
qed


subsection \<open>Affine dependence and consequential theorems\<close>

text "Formalized by Lars Schewe."

definition\<^marker>\<open>tag important\<close> affine_dependent :: "'a::real_vector set \<Rightarrow> bool"
  where "affine_dependent s \<longleftrightarrow> (\<exists>x\<in>s. x \<in> affine hull (s - {x}))"

lemma affine_dependent_subset:
   "\<lbrakk>affine_dependent s; s \<subseteq> t\<rbrakk> \<Longrightarrow> affine_dependent t"
apply (simp add: affine_dependent_def Bex_def)
apply (blast dest: hull_mono [OF Diff_mono [OF _ subset_refl]])
done

lemma affine_independent_subset:
  shows "\<lbrakk>\<not> affine_dependent t; s \<subseteq> t\<rbrakk> \<Longrightarrow> \<not> affine_dependent s"
by (metis affine_dependent_subset)

lemma affine_independent_Diff:
   "\<not> affine_dependent s \<Longrightarrow> \<not> affine_dependent(s - t)"
by (meson Diff_subset affine_dependent_subset)

proposition affine_dependent_explicit:
  "affine_dependent p \<longleftrightarrow>
    (\<exists>S u. finite S \<and> S \<subseteq> p \<and> sum u S = 0 \<and> (\<exists>v\<in>S. u v \<noteq> 0) \<and> sum (\<lambda>v. u v *\<^sub>R v) S = 0)"
proof -
  have "\<exists>S u. finite S \<and> S \<subseteq> p \<and> sum u S = 0 \<and> (\<exists>v\<in>S. u v \<noteq> 0) \<and> (\<Sum>w\<in>S. u w *\<^sub>R w) = 0"
    if "(\<Sum>w\<in>S. u w *\<^sub>R w) = x" "x \<in> p" "finite S" "S \<noteq> {}" "S \<subseteq> p - {x}" "sum u S = 1" for x S u
  proof (intro exI conjI)
    have "x \<notin> S" 
      using that by auto
    then show "(\<Sum>v \<in> insert x S. if v = x then - 1 else u v) = 0"
      using that by (simp add: sum_delta_notmem)
    show "(\<Sum>w \<in> insert x S. (if w = x then - 1 else u w) *\<^sub>R w) = 0"
      using that \<open>x \<notin> S\<close> by (simp add: if_smult sum_delta_notmem cong: if_cong)
  qed (use that in auto)
  moreover have "\<exists>x\<in>p. \<exists>S u. finite S \<and> S \<noteq> {} \<and> S \<subseteq> p - {x} \<and> sum u S = 1 \<and> (\<Sum>v\<in>S. u v *\<^sub>R v) = x"
    if "(\<Sum>v\<in>S. u v *\<^sub>R v) = 0" "finite S" "S \<subseteq> p" "sum u S = 0" "v \<in> S" "u v \<noteq> 0" for S u v
  proof (intro bexI exI conjI)
    have "S \<noteq> {v}"
      using that by auto
    then show "S - {v} \<noteq> {}"
      using that by auto
    show "(\<Sum>x \<in> S - {v}. - (1 / u v) * u x) = 1"
      unfolding sum_distrib_left[symmetric] sum_diff1[OF \<open>finite S\<close>] by (simp add: that)
    show "(\<Sum>x\<in>S - {v}. (- (1 / u v) * u x) *\<^sub>R x) = v"
      unfolding sum_distrib_left [symmetric] scaleR_scaleR[symmetric]
                scaleR_right.sum [symmetric] sum_diff1[OF \<open>finite S\<close>] 
      using that by auto
    show "S - {v} \<subseteq> p - {v}"
      using that by auto
  qed (use that in auto)
  ultimately show ?thesis
    unfolding affine_dependent_def affine_hull_explicit by auto
qed

lemma affine_dependent_explicit_finite:
  fixes S :: "'a::real_vector set"
  assumes "finite S"
  shows "affine_dependent S \<longleftrightarrow>
    (\<exists>u. sum u S = 0 \<and> (\<exists>v\<in>S. u v \<noteq> 0) \<and> sum (\<lambda>v. u v *\<^sub>R v) S = 0)"
  (is "?lhs = ?rhs")
proof
  have *: "\<And>vt u v. (if vt then u v else 0) *\<^sub>R v = (if vt then (u v) *\<^sub>R v else 0::'a)"
    by auto
  assume ?lhs
  then obtain t u v where
    "finite t" "t \<subseteq> S" "sum u t = 0" "v\<in>t" "u v \<noteq> 0"  "(\<Sum>v\<in>t. u v *\<^sub>R v) = 0"
    unfolding affine_dependent_explicit by auto
  then show ?rhs
    apply (rule_tac x="\<lambda>x. if x\<in>t then u x else 0" in exI)
    apply (auto simp: * sum.inter_restrict[OF assms, symmetric] Int_absorb1[OF \<open>t\<subseteq>S\<close>])
    done
next
  assume ?rhs
  then obtain u v where "sum u S = 0"  "v\<in>S" "u v \<noteq> 0" "(\<Sum>v\<in>S. u v *\<^sub>R v) = 0"
    by auto
  then show ?lhs unfolding affine_dependent_explicit
    using assms by auto
qed


subsection\<^marker>\<open>tag unimportant\<close> \<open>Connectedness of convex sets\<close>

lemma connectedD:
  "connected S \<Longrightarrow> open A \<Longrightarrow> open B \<Longrightarrow> S \<subseteq> A \<union> B \<Longrightarrow> A \<inter> B \<inter> S = {} \<Longrightarrow> A \<inter> S = {} \<or> B \<inter> S = {}"
  by (rule Topological_Spaces.topological_space_class.connectedD)

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

corollary connected_UNIV[intro]: "connected (UNIV :: 'a::real_normed_vector set)"
  by (simp add: convex_connected)

lemma convex_prod:
  assumes "\<And>i. i \<in> Basis \<Longrightarrow> convex {x. P i x}"
  shows "convex {x. \<forall>i\<in>Basis. P i (x\<bullet>i)}"
  using assms unfolding convex_def
  by (auto simp: inner_add_left)

lemma convex_positive_orthant: "convex {x::'a::euclidean_space. (\<forall>i\<in>Basis. 0 \<le> x\<bullet>i)}"
  by (rule convex_prod) (simp add: atLeast_def[symmetric] convex_real_interval)

subsection \<open>Convex hull\<close>

lemma convex_convex_hull [iff]: "convex (convex hull s)"
  unfolding hull_def
  using convex_Inter[of "{t. convex t \<and> s \<subseteq> t}"]
  by auto

lemma convex_hull_subset:
    "s \<subseteq> convex hull t \<Longrightarrow> convex hull s \<subseteq> convex hull t"
  by (simp add: convex_convex_hull subset_hull)

lemma convex_hull_eq: "convex hull s = s \<longleftrightarrow> convex s"
  by (metis convex_convex_hull hull_same)

subsubsection\<^marker>\<open>tag unimportant\<close> \<open>Convex hull is "preserved" by a linear function\<close>

lemma convex_hull_linear_image:
  assumes f: "linear f"
  shows "f ` (convex hull s) = convex hull (f ` s)"
proof
  show "convex hull (f ` s) \<subseteq> f ` (convex hull s)"
    by (intro hull_minimal image_mono hull_subset convex_linear_image assms convex_convex_hull)
  show "f ` (convex hull s) \<subseteq> convex hull (f ` s)"
  proof (unfold image_subset_iff_subset_vimage, rule hull_minimal)
    show "s \<subseteq> f -` (convex hull (f ` s))"
      by (fast intro: hull_inc)
    show "convex (f -` (convex hull (f ` s)))"
      by (intro convex_linear_vimage [OF f] convex_convex_hull)
  qed
qed

lemma in_convex_hull_linear_image:
  assumes "linear f"
    and "x \<in> convex hull s"
  shows "f x \<in> convex hull (f ` s)"
  using convex_hull_linear_image[OF assms(1)] assms(2) by auto

lemma convex_hull_Times:
  "convex hull (s \<times> t) = (convex hull s) \<times> (convex hull t)"
proof
  show "convex hull (s \<times> t) \<subseteq> (convex hull s) \<times> (convex hull t)"
    by (intro hull_minimal Sigma_mono hull_subset convex_Times convex_convex_hull)
  have "(x, y) \<in> convex hull (s \<times> t)" if x: "x \<in> convex hull s" and y: "y \<in> convex hull t" for x y
  proof (rule hull_induct [OF x], rule hull_induct [OF y])
    fix x y assume "x \<in> s" and "y \<in> t"
    then show "(x, y) \<in> convex hull (s \<times> t)"
      by (simp add: hull_inc)
  next
    fix x let ?S = "((\<lambda>y. (0, y)) -` (\<lambda>p. (- x, 0) + p) ` (convex hull s \<times> t))"
    have "convex ?S"
      by (intro convex_linear_vimage convex_translation convex_convex_hull,
        simp add: linear_iff)
    also have "?S = {y. (x, y) \<in> convex hull (s \<times> t)}"
      by (auto simp: image_def Bex_def)
    finally show "convex {y. (x, y) \<in> convex hull (s \<times> t)}" .
  next
    show "convex {x. (x, y) \<in> convex hull s \<times> t}"
    proof -
      fix y let ?S = "((\<lambda>x. (x, 0)) -` (\<lambda>p. (0, - y) + p) ` (convex hull s \<times> t))"
      have "convex ?S"
      by (intro convex_linear_vimage convex_translation convex_convex_hull,
        simp add: linear_iff)
      also have "?S = {x. (x, y) \<in> convex hull (s \<times> t)}"
        by (auto simp: image_def Bex_def)
      finally show "convex {x. (x, y) \<in> convex hull (s \<times> t)}" .
    qed
  qed
  then show "(convex hull s) \<times> (convex hull t) \<subseteq> convex hull (s \<times> t)"
    unfolding subset_eq split_paired_Ball_Sigma by blast
qed


subsubsection\<^marker>\<open>tag unimportant\<close> \<open>Stepping theorems for convex hulls of finite sets\<close>

lemma convex_hull_empty[simp]: "convex hull {} = {}"
  by (rule hull_unique) auto

lemma convex_hull_singleton[simp]: "convex hull {a} = {a}"
  by (rule hull_unique) auto

lemma convex_hull_insert:
  fixes S :: "'a::real_vector set"
  assumes "S \<noteq> {}"
  shows "convex hull (insert a S) =
         {x. \<exists>u\<ge>0. \<exists>v\<ge>0. \<exists>b. (u + v = 1) \<and> b \<in> (convex hull S) \<and> (x = u *\<^sub>R a + v *\<^sub>R b)}"
  (is "_ = ?hull")
proof (intro equalityI hull_minimal subsetI)
  fix x
  assume "x \<in> insert a S"
  then have "\<exists>u\<ge>0. \<exists>v\<ge>0. u + v = 1 \<and> (\<exists>b. b \<in> convex hull S \<and> x = u *\<^sub>R a + v *\<^sub>R b)"
  unfolding insert_iff
  proof
    assume "x = a"
    then show ?thesis
      by (rule_tac x=1 in exI) (use assms hull_subset in fastforce)
  next
    assume "x \<in> S"
    with hull_subset[of S convex] show ?thesis
      by force
  qed
  then show "x \<in> ?hull"
    by simp
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
        using as(3) obt1(3) obt2(3) by (auto simp: field_simps)
      also have "\<dots> = u * (v1 + u1 - u1) + v * (v2 + u2 - u2)"
        using as(3) obt1(3) obt2(3) by (auto simp: field_simps)
      also have "\<dots> = u * v1 + v * v2"
        by simp
      finally have **:"1 - (u * u1 + v * u2) = u * v1 + v * v2" by auto
      let ?b = "((u * v1) / (u * v1 + v * v2)) *\<^sub>R b1 + ((v * v2) / (u * v1 + v * v2)) *\<^sub>R b2"
      have zeroes: "0 \<le> u * v1 + v * v2" "0 \<le> u * v1" "0 \<le> u * v1 + v * v2" "0 \<le> v * v2"
        using as(1,2) obt1(1,2) obt2(1,2) by auto
      show ?thesis
      proof
        show "u *\<^sub>R x + v *\<^sub>R y = (u * u1) *\<^sub>R a + (v * u2) *\<^sub>R a + (?b - (u * u1) *\<^sub>R ?b - (v * u2) *\<^sub>R ?b)"
          unfolding xeq yeq * **
          using False by (auto simp: scaleR_left_distrib scaleR_right_distrib)
        show "?b \<in> convex hull S"
          using False zeroes obt1(4) obt2(4)
          by (auto simp: convexD [OF convex_convex_hull] scaleR_left_distrib scaleR_right_distrib  add_divide_distrib[symmetric]  zero_le_divide_iff)
      qed
    qed
    then obtain b where b: "b \<in> convex hull S" 
       "u *\<^sub>R x + v *\<^sub>R y = (u * u1) *\<^sub>R a + (v * u2) *\<^sub>R a + (b - (u * u1) *\<^sub>R b - (v * u2) *\<^sub>R b)" ..

    have u1: "u1 \<le> 1"
      unfolding obt1(3)[symmetric] and not_le using obt1(2) by auto
    have u2: "u2 \<le> 1"
      unfolding obt2(3)[symmetric] and not_le using obt2(2) by auto
    have "u1 * u + u2 * v \<le> max u1 u2 * u + max u1 u2 * v"
    proof (rule add_mono)
      show "u1 * u \<le> max u1 u2 * u" "u2 * v \<le> max u1 u2 * v"
        by (simp_all add: as mult_right_mono)
    qed
    also have "\<dots> \<le> 1"
      unfolding distrib_left[symmetric] and as(3) using u1 u2 by auto
    finally have le1: "u1 * u + u2 * v \<le> 1" .    
    show "u *\<^sub>R x + v *\<^sub>R y \<in> ?hull"
    proof (intro CollectI exI conjI)
      show "0 \<le> u * u1 + v * u2"
        by (simp add: as(1) as(2) obt1(1) obt2(1))
      show "0 \<le> 1 - u * u1 - v * u2"
        by (simp add: le1 diff_diff_add mult.commute)
    qed (use b in \<open>auto simp: algebra_simps\<close>)
  qed
qed

lemma convex_hull_insert_alt:
   "convex hull (insert a S) =
     (if S = {} then {a}
      else {(1 - u) *\<^sub>R a + u *\<^sub>R x |x u. 0 \<le> u \<and> u \<le> 1 \<and> x \<in> convex hull S})"
  apply (auto simp: convex_hull_insert)
  using diff_eq_eq apply fastforce
  by (metis add.group_left_neutral add_le_imp_le_diff diff_add_cancel)

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
proof -
  {
    fix x
    assume "x\<in>?lhs"
    then obtain k u y where
        obt: "\<forall>i\<in>{1::nat..k}. 0 \<le> u i \<and> y i \<in> p" "sum u {1..k} = 1" "(\<Sum>i = 1..k. u i *\<^sub>R y i) = x"
      unfolding convex_hull_indexed by auto

    have fin: "finite {1..k}" by auto
    have fin': "\<And>v. finite {i \<in> {1..k}. y i = v}" by auto
    {
      fix j
      assume "j\<in>{1..k}"
      then have "y j \<in> p" "0 \<le> sum u {i. Suc 0 \<le> i \<and> i \<le> k \<and> y i = y j}"
        using obt(1)[THEN bspec[where x=j]] and obt(2)
        apply simp
        apply (rule sum_nonneg)
        using obt(1)
        apply auto
        done
    }
    moreover
    have "(\<Sum>v\<in>y ` {1..k}. sum u {i \<in> {1..k}. y i = v}) = 1"
      unfolding sum.image_gen[OF fin, symmetric] using obt(2) by auto
    moreover have "(\<Sum>v\<in>y ` {1..k}. sum u {i \<in> {1..k}. y i = v} *\<^sub>R v) = x"
      using sum.image_gen[OF fin, of "\<lambda>i. u i *\<^sub>R y i" y, symmetric]
      unfolding scaleR_left.sum using obt(3) by auto
    ultimately
    have "\<exists>S u. finite S \<and> S \<subseteq> p \<and> (\<forall>x\<in>S. 0 \<le> u x) \<and> sum u S = 1 \<and> (\<Sum>v\<in>S. u v *\<^sub>R v) = x"
      apply (rule_tac x="y ` {1..k}" in exI)
      apply (rule_tac x="\<lambda>v. sum u {i\<in>{1..k}. y i = v}" in exI, auto)
      done
    then have "x\<in>?rhs" by auto
  }
  moreover
  {
    fix y
    assume "y\<in>?rhs"
    then obtain S u where
      obt: "finite S" "S \<subseteq> p" "\<forall>x\<in>S. 0 \<le> u x" "sum u S = 1" "(\<Sum>v\<in>S. u v *\<^sub>R v) = y"
      by auto

    obtain f where f: "inj_on f {1..card S}" "f ` {1..card S} = S"
      using ex_bij_betw_nat_finite_1[OF obt(1)] unfolding bij_betw_def by auto

    {
      fix i :: nat
      assume "i\<in>{1..card S}"
      then have "f i \<in> S"
        using f(2) by blast
      then have "0 \<le> u (f i)" "f i \<in> p" using obt(2,3) by auto
    }
    moreover have *: "finite {1..card S}" by auto
    {
      fix y
      assume "y\<in>S"
      then obtain i where "i\<in>{1..card S}" "f i = y"
        using f using image_iff[of y f "{1..card S}"]
        by auto
      then have "{x. Suc 0 \<le> x \<and> x \<le> card S \<and> f x = y} = {i}"
        apply auto
        using f(1)[unfolded inj_on_def]
        by (metis One_nat_def atLeastAtMost_iff)
      then have "card {x. Suc 0 \<le> x \<and> x \<le> card S \<and> f x = y} = 1" by auto
      then have "(\<Sum>x\<in>{x \<in> {1..card S}. f x = y}. u (f x)) = u y"
          "(\<Sum>x\<in>{x \<in> {1..card S}. f x = y}. u (f x) *\<^sub>R f x) = u y *\<^sub>R y"
        by (auto simp: sum_constant_scaleR)
    }
    then have "(\<Sum>x = 1..card S. u (f x)) = 1" "(\<Sum>i = 1..card S. u (f i) *\<^sub>R f i) = y"
      unfolding sum.image_gen[OF *(1), of "\<lambda>x. u (f x) *\<^sub>R f x" f]
        and sum.image_gen[OF *(1), of "\<lambda>x. u (f x)" f]
      unfolding f
      using sum.cong [of S S "\<lambda>y. (\<Sum>x\<in>{x \<in> {1..card S}. f x = y}. u (f x) *\<^sub>R f x)" "\<lambda>v. u v *\<^sub>R v"]
      using sum.cong [of S S "\<lambda>y. (\<Sum>x\<in>{x \<in> {1..card S}. f x = y}. u (f x))" u]
      unfolding obt(4,5)
      by auto
    ultimately
    have "\<exists>k u x. (\<forall>i\<in>{1..k}. 0 \<le> u i \<and> x i \<in> p) \<and> sum u {1..k} = 1 \<and>
        (\<Sum>i::nat = 1..k. u i *\<^sub>R x i) = y"
      apply (rule_tac x="card S" in exI)
      apply (rule_tac x="u \<circ> f" in exI)
      apply (rule_tac x=f in exI, fastforce)
      done
    then have "y \<in> ?lhs"
      unfolding convex_hull_indexed by auto
  }
  ultimately show ?thesis
    unfolding set_eq_iff by blast
qed


subsubsection\<^marker>\<open>tag unimportant\<close> \<open>A stepping theorem for that expansion\<close>

lemma convex_hull_finite_step:
  fixes S :: "'a::real_vector set"
  assumes "finite S"
  shows
    "(\<exists>u. (\<forall>x\<in>insert a S. 0 \<le> u x) \<and> sum u (insert a S) = w \<and> sum (\<lambda>x. u x *\<^sub>R x) (insert a S) = y)
      \<longleftrightarrow> (\<exists>v\<ge>0. \<exists>u. (\<forall>x\<in>S. 0 \<le> u x) \<and> sum u S = w - v \<and> sum (\<lambda>x. u x *\<^sub>R x) S = y - v *\<^sub>R a)"
  (is "?lhs = ?rhs")
proof (rule, case_tac[!] "a\<in>S")
  assume "a \<in> S"
  then have *: "insert a S = S" by auto
  assume ?lhs
  then show ?rhs
    unfolding *  by (rule_tac x=0 in exI, auto)
next
  assume ?lhs
  then obtain u where
      u: "\<forall>x\<in>insert a S. 0 \<le> u x" "sum u (insert a S) = w" "(\<Sum>x\<in>insert a S. u x *\<^sub>R x) = y"
    by auto
  assume "a \<notin> S"
  then show ?rhs
    apply (rule_tac x="u a" in exI)
    using u(1)[THEN bspec[where x=a]]
    apply simp
    apply (rule_tac x=u in exI)
    using u[unfolded sum_clauses(2)[OF assms]] and \<open>a\<notin>S\<close>
    apply auto
    done
next
  assume "a \<in> S"
  then have *: "insert a S = S" by auto
  have fin: "finite (insert a S)" using assms by auto
  assume ?rhs
  then obtain v u where uv: "v\<ge>0" "\<forall>x\<in>S. 0 \<le> u x" "sum u S = w - v" "(\<Sum>x\<in>S. u x *\<^sub>R x) = y - v *\<^sub>R a"
    by auto
  show ?lhs
    apply (rule_tac x = "\<lambda>x. (if a = x then v else 0) + u x" in exI)
    unfolding scaleR_left_distrib and sum.distrib and sum_delta''[OF fin] and sum.delta'[OF fin]
    unfolding sum_clauses(2)[OF assms]
    using uv and uv(2)[THEN bspec[where x=a]] and \<open>a\<in>S\<close>
    apply auto
    done
next
  assume ?rhs
  then obtain v u where uv: "v\<ge>0" "\<forall>x\<in>S. 0 \<le> u x" "sum u S = w - v" "(\<Sum>x\<in>S. u x *\<^sub>R x) = y - v *\<^sub>R a"
    by auto
  moreover assume "a \<notin> S"
  moreover
  have "(\<Sum>x\<in>S. if a = x then v else u x) = sum u S"  "(\<Sum>x\<in>S. (if a = x then v else u x) *\<^sub>R x) = (\<Sum>x\<in>S. u x *\<^sub>R x)"
    using \<open>a \<notin> S\<close>
    by (auto simp: intro!: sum.cong)
  ultimately show ?lhs
    by (rule_tac x="\<lambda>x. if a = x then v else u x" in exI) (auto simp: sum_clauses(2)[OF assms])
qed


subsubsection\<^marker>\<open>tag unimportant\<close> \<open>Hence some special cases\<close>

lemma convex_hull_2:
  "convex hull {a,b} = {u *\<^sub>R a + v *\<^sub>R b | u v. 0 \<le> u \<and> 0 \<le> v \<and> u + v = 1}"
proof -
  have *: "\<And>u. (\<forall>x\<in>{a, b}. 0 \<le> u x) \<longleftrightarrow> 0 \<le> u a \<and> 0 \<le> u b"
    by auto
  have **: "finite {b}" by auto
  show ?thesis
    apply (simp add: convex_hull_finite)
    unfolding convex_hull_finite_step[OF **, of a 1, unfolded * conj_assoc]
    apply auto
    apply (rule_tac x=v in exI)
    apply (rule_tac x="1 - v" in exI, simp)
    apply (rule_tac x=u in exI, simp)
    apply (rule_tac x="\<lambda>x. v" in exI, simp)
    done
qed

lemma convex_hull_2_alt: "convex hull {a,b} = {a + u *\<^sub>R (b - a) | u.  0 \<le> u \<and> u \<le> 1}"
  unfolding convex_hull_2
proof (rule Collect_cong)
  have *: "\<And>x y ::real. x + y = 1 \<longleftrightarrow> x = 1 - y"
    by auto
  fix x
  show "(\<exists>v u. x = v *\<^sub>R a + u *\<^sub>R b \<and> 0 \<le> v \<and> 0 \<le> u \<and> v + u = 1) \<longleftrightarrow>
    (\<exists>u. x = a + u *\<^sub>R (b - a) \<and> 0 \<le> u \<and> u \<le> 1)"
    unfolding *
    apply auto
    apply (rule_tac[!] x=u in exI)
    apply (auto simp: algebra_simps)
    done
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

lemma affine_hull_subset_span: "(affine hull s) \<subseteq> (span s)"
  by (metis hull_minimal span_superset subspace_imp_affine subspace_span)

lemma convex_hull_subset_span: "(convex hull s) \<subseteq> (span s)"
  by (metis hull_minimal span_superset subspace_imp_convex subspace_span)

lemma convex_hull_subset_affine_hull: "(convex hull s) \<subseteq> (affine hull s)"
  by (metis affine_affine_hull affine_imp_convex hull_minimal hull_subset)

lemma affine_dependent_imp_dependent: "affine_dependent s \<Longrightarrow> dependent s"
  unfolding affine_dependent_def dependent_def
  using affine_hull_subset_span by auto

lemma dependent_imp_affine_dependent:
  assumes "dependent {x - a| x . x \<in> s}"
    and "a \<notin> s"
  shows "affine_dependent (insert a s)"
proof -
  from assms(1)[unfolded dependent_explicit] obtain S u v
    where obt: "finite S" "S \<subseteq> {x - a |x. x \<in> s}" "v\<in>S" "u v  \<noteq> 0" "(\<Sum>v\<in>S. u v *\<^sub>R v) = 0"
    by auto
  define t where "t = (\<lambda>x. x + a) ` S"

  have inj: "inj_on (\<lambda>x. x + a) S"
    unfolding inj_on_def by auto
  have "0 \<notin> S"
    using obt(2) assms(2) unfolding subset_eq by auto
  have fin: "finite t" and "t \<subseteq> s"
    unfolding t_def using obt(1,2) by auto
  then have "finite (insert a t)" and "insert a t \<subseteq> insert a s"
    by auto
  moreover have *: "\<And>P Q. (\<Sum>x\<in>t. (if x = a then P x else Q x)) = (\<Sum>x\<in>t. Q x)"
    apply (rule sum.cong)
    using \<open>a\<notin>s\<close> \<open>t\<subseteq>s\<close>
    apply auto
    done
  have "(\<Sum>x\<in>insert a t. if x = a then - (\<Sum>x\<in>t. u (x - a)) else u (x - a)) = 0"
    unfolding sum_clauses(2)[OF fin] * using \<open>a\<notin>s\<close> \<open>t\<subseteq>s\<close> by auto
  moreover have "\<exists>v\<in>insert a t. (if v = a then - (\<Sum>x\<in>t. u (x - a)) else u (v - a)) \<noteq> 0"
    using obt(3,4) \<open>0\<notin>S\<close>
    by (rule_tac x="v + a" in bexI) (auto simp: t_def)
  moreover have *: "\<And>P Q. (\<Sum>x\<in>t. (if x = a then P x else Q x) *\<^sub>R x) = (\<Sum>x\<in>t. Q x *\<^sub>R x)"
    using \<open>a\<notin>s\<close> \<open>t\<subseteq>s\<close> by (auto intro!: sum.cong)
  have "(\<Sum>x\<in>t. u (x - a)) *\<^sub>R a = (\<Sum>v\<in>t. u (v - a) *\<^sub>R v)"
    unfolding scaleR_left.sum
    unfolding t_def and sum.reindex[OF inj] and o_def
    using obt(5)
    by (auto simp: sum.distrib scaleR_right_distrib)
  then have "(\<Sum>v\<in>insert a t. (if v = a then - (\<Sum>x\<in>t. u (x - a)) else u (v - a)) *\<^sub>R v) = 0"
    unfolding sum_clauses(2)[OF fin]
    using \<open>a\<notin>s\<close> \<open>t\<subseteq>s\<close>
    by (auto simp: *)
  ultimately show ?thesis
    unfolding affine_dependent_explicit
    apply (rule_tac x="insert a t" in exI, auto)
    done
qed

lemma convex_cone:
  "convex s \<and> cone s \<longleftrightarrow> (\<forall>x\<in>s. \<forall>y\<in>s. (x + y) \<in> s) \<and> (\<forall>x\<in>s. \<forall>c\<ge>0. (c *\<^sub>R x) \<in> s)"
  (is "?lhs = ?rhs")
proof -
  {
    fix x y
    assume "x\<in>s" "y\<in>s" and ?lhs
    then have "2 *\<^sub>R x \<in>s" "2 *\<^sub>R y \<in> s"
      unfolding cone_def by auto
    then have "x + y \<in> s"
      using \<open>?lhs\<close>[unfolded convex_def, THEN conjunct1]
      apply (erule_tac x="2*\<^sub>R x" in ballE)
      apply (erule_tac x="2*\<^sub>R y" in ballE)
      apply (erule_tac x="1/2" in allE, simp)
      apply (erule_tac x="1/2" in allE, auto)
      done
  }
  then show ?thesis
    unfolding convex_def cone_def by blast
qed

lemma affine_dependent_biggerset:
  fixes s :: "'a::euclidean_space set"
  assumes "finite s" "card s \<ge> DIM('a) + 2"
  shows "affine_dependent s"
proof -
  have "s \<noteq> {}" using assms by auto
  then obtain a where "a\<in>s" by auto
  have *: "{x - a |x. x \<in> s - {a}} = (\<lambda>x. x - a) ` (s - {a})"
    by auto
  have "card {x - a |x. x \<in> s - {a}} = card (s - {a})"
    unfolding * by (simp add: card_image inj_on_def)
  also have "\<dots> > DIM('a)" using assms(2)
    unfolding card_Diff_singleton[OF assms(1) \<open>a\<in>s\<close>] by auto
  finally show ?thesis
    apply (subst insert_Diff[OF \<open>a\<in>s\<close>, symmetric])
    apply (rule dependent_imp_affine_dependent)
    apply (rule dependent_biggerset, auto)
    done
qed

lemma affine_dependent_biggerset_general:
  assumes "finite (S :: 'a::euclidean_space set)"
    and "card S \<ge> dim S + 2"
  shows "affine_dependent S"
proof -
  from assms(2) have "S \<noteq> {}" by auto
  then obtain a where "a\<in>S" by auto
  have *: "{x - a |x. x \<in> S - {a}} = (\<lambda>x. x - a) ` (S - {a})"
    by auto
  have **: "card {x - a |x. x \<in> S - {a}} = card (S - {a})"
    by (metis (no_types, lifting) "*" card_image diff_add_cancel inj_on_def)
  have "dim {x - a |x. x \<in> S - {a}} \<le> dim S"
    using \<open>a\<in>S\<close> by (auto simp: span_base span_diff intro: subset_le_dim)
  also have "\<dots> < dim S + 1" by auto
  also have "\<dots> \<le> card (S - {a})"
    using assms
    using card_Diff_singleton[OF assms(1) \<open>a\<in>S\<close>]
    by auto
  finally show ?thesis
    apply (subst insert_Diff[OF \<open>a\<in>S\<close>, symmetric])
    apply (rule dependent_imp_affine_dependent)
    apply (rule dependent_biggerset_general)
    unfolding **
    apply auto
    done
qed


subsection\<^marker>\<open>tag unimportant\<close> \<open>Some Properties of Affine Dependent Sets\<close>

lemma affine_independent_0 [simp]: "\<not> affine_dependent {}"
  by (simp add: affine_dependent_def)

lemma affine_independent_1 [simp]: "\<not> affine_dependent {a}"
  by (simp add: affine_dependent_def)

lemma affine_independent_2 [simp]: "\<not> affine_dependent {a,b}"
  by (simp add: affine_dependent_def insert_Diff_if hull_same)

lemma affine_hull_translation: "affine hull ((\<lambda>x. a + x) `  S) = (\<lambda>x. a + x) ` (affine hull S)"
proof -
  have "affine ((\<lambda>x. a + x) ` (affine hull S))"
    using affine_translation affine_affine_hull by blast
  moreover have "(\<lambda>x. a + x) `  S \<subseteq> (\<lambda>x. a + x) ` (affine hull S)"
    using hull_subset[of S] by auto
  ultimately have h1: "affine hull ((\<lambda>x. a + x) `  S) \<subseteq> (\<lambda>x. a + x) ` (affine hull S)"
    by (metis hull_minimal)
  have "affine((\<lambda>x. -a + x) ` (affine hull ((\<lambda>x. a + x) `  S)))"
    using affine_translation affine_affine_hull by blast
  moreover have "(\<lambda>x. -a + x) ` (\<lambda>x. a + x) `  S \<subseteq> (\<lambda>x. -a + x) ` (affine hull ((\<lambda>x. a + x) `  S))"
    using hull_subset[of "(\<lambda>x. a + x) `  S"] by auto
  moreover have "S = (\<lambda>x. -a + x) ` (\<lambda>x. a + x) `  S"
    using translation_assoc[of "-a" a] by auto
  ultimately have "(\<lambda>x. -a + x) ` (affine hull ((\<lambda>x. a + x) `  S)) >= (affine hull S)"
    by (metis hull_minimal)
  then have "affine hull ((\<lambda>x. a + x) ` S) >= (\<lambda>x. a + x) ` (affine hull S)"
    by auto
  then show ?thesis using h1 by auto
qed

lemma affine_dependent_translation:
  assumes "affine_dependent S"
  shows "affine_dependent ((\<lambda>x. a + x) ` S)"
proof -
  obtain x where x: "x \<in> S \<and> x \<in> affine hull (S - {x})"
    using assms affine_dependent_def by auto
  have "(+) a ` (S - {x}) = (+) a ` S - {a + x}"
    by auto
  then have "a + x \<in> affine hull ((\<lambda>x. a + x) ` S - {a + x})"
    using affine_hull_translation[of a "S - {x}"] x by auto
  moreover have "a + x \<in> (\<lambda>x. a + x) ` S"
    using x by auto
  ultimately show ?thesis
    unfolding affine_dependent_def by auto
qed

lemma affine_dependent_translation_eq:
  "affine_dependent S \<longleftrightarrow> affine_dependent ((\<lambda>x. a + x) ` S)"
proof -
  {
    assume "affine_dependent ((\<lambda>x. a + x) ` S)"
    then have "affine_dependent S"
      using affine_dependent_translation[of "((\<lambda>x. a + x) ` S)" "-a"] translation_assoc[of "-a" a]
      by auto
  }
  then show ?thesis
    using affine_dependent_translation by auto
qed

lemma affine_hull_0_dependent:
  assumes "0 \<in> affine hull S"
  shows "dependent S"
proof -
  obtain s u where s_u: "finite s \<and> s \<noteq> {} \<and> s \<subseteq> S \<and> sum u s = 1 \<and> (\<Sum>v\<in>s. u v *\<^sub>R v) = 0"
    using assms affine_hull_explicit[of S] by auto
  then have "\<exists>v\<in>s. u v \<noteq> 0"
    using sum_not_0[of "u" "s"] by auto
  then have "finite s \<and> s \<subseteq> S \<and> (\<exists>v\<in>s. u v \<noteq> 0 \<and> (\<Sum>v\<in>s. u v *\<^sub>R v) = 0)"
    using s_u by auto
  then show ?thesis
    unfolding dependent_explicit[of S] by auto
qed

lemma affine_dependent_imp_dependent2:
  assumes "affine_dependent (insert 0 S)"
  shows "dependent S"
proof -
  obtain x where x: "x \<in> insert 0 S \<and> x \<in> affine hull (insert 0 S - {x})"
    using affine_dependent_def[of "(insert 0 S)"] assms by blast
  then have "x \<in> span (insert 0 S - {x})"
    using affine_hull_subset_span by auto
  moreover have "span (insert 0 S - {x}) = span (S - {x})"
    using insert_Diff_if[of "0" S "{x}"] span_insert_0[of "S-{x}"] by auto
  ultimately have "x \<in> span (S - {x})" by auto
  then have "x \<noteq> 0 \<Longrightarrow> dependent S"
    using x dependent_def by auto
  moreover
  {
    assume "x = 0"
    then have "0 \<in> affine hull S"
      using x hull_mono[of "S - {0}" S] by auto
    then have "dependent S"
      using affine_hull_0_dependent by auto
  }
  ultimately show ?thesis by auto
qed

lemma affine_dependent_iff_dependent:
  assumes "a \<notin> S"
  shows "affine_dependent (insert a S) \<longleftrightarrow> dependent ((\<lambda>x. -a + x) ` S)"
proof -
  have "((+) (- a) ` S) = {x - a| x . x \<in> S}" by auto
  then show ?thesis
    using affine_dependent_translation_eq[of "(insert a S)" "-a"]
      affine_dependent_imp_dependent2 assms
      dependent_imp_affine_dependent[of a S]
    by (auto simp del: uminus_add_conv_diff)
qed

lemma affine_dependent_iff_dependent2:
  assumes "a \<in> S"
  shows "affine_dependent S \<longleftrightarrow> dependent ((\<lambda>x. -a + x) ` (S-{a}))"
proof -
  have "insert a (S - {a}) = S"
    using assms by auto
  then show ?thesis
    using assms affine_dependent_iff_dependent[of a "S-{a}"] by auto
qed

lemma affine_hull_insert_span_gen:
  "affine hull (insert a s) = (\<lambda>x. a + x) ` span ((\<lambda>x. - a + x) ` s)"
proof -
  have h1: "{x - a |x. x \<in> s} = ((\<lambda>x. -a+x) ` s)"
    by auto
  {
    assume "a \<notin> s"
    then have ?thesis
      using affine_hull_insert_span[of a s] h1 by auto
  }
  moreover
  {
    assume a1: "a \<in> s"
    have "\<exists>x. x \<in> s \<and> -a+x=0"
      apply (rule exI[of _ a])
      using a1
      apply auto
      done
    then have "insert 0 ((\<lambda>x. -a+x) ` (s - {a})) = (\<lambda>x. -a+x) ` s"
      by auto
    then have "span ((\<lambda>x. -a+x) ` (s - {a}))=span ((\<lambda>x. -a+x) ` s)"
      using span_insert_0[of "(+) (- a) ` (s - {a})"] by (auto simp del: uminus_add_conv_diff)
    moreover have "{x - a |x. x \<in> (s - {a})} = ((\<lambda>x. -a+x) ` (s - {a}))"
      by auto
    moreover have "insert a (s - {a}) = insert a s"
      by auto
    ultimately have ?thesis
      using affine_hull_insert_span[of "a" "s-{a}"] by auto
  }
  ultimately show ?thesis by auto
qed

lemma affine_hull_span2:
  assumes "a \<in> s"
  shows "affine hull s = (\<lambda>x. a+x) ` span ((\<lambda>x. -a+x) ` (s-{a}))"
  using affine_hull_insert_span_gen[of a "s - {a}", unfolded insert_Diff[OF assms]]
  by auto

lemma affine_hull_span_gen:
  assumes "a \<in> affine hull s"
  shows "affine hull s = (\<lambda>x. a+x) ` span ((\<lambda>x. -a+x) ` s)"
proof -
  have "affine hull (insert a s) = affine hull s"
    using hull_redundant[of a affine s] assms by auto
  then show ?thesis
    using affine_hull_insert_span_gen[of a "s"] by auto
qed

lemma affine_hull_span_0:
  assumes "0 \<in> affine hull S"
  shows "affine hull S = span S"
  using affine_hull_span_gen[of "0" S] assms by auto

lemma extend_to_affine_basis_nonempty:
  fixes S V :: "'n::euclidean_space set"
  assumes "\<not> affine_dependent S" "S \<subseteq> V" "S \<noteq> {}"
  shows "\<exists>T. \<not> affine_dependent T \<and> S \<subseteq> T \<and> T \<subseteq> V \<and> affine hull T = affine hull V"
proof -
  obtain a where a: "a \<in> S"
    using assms by auto
  then have h0: "independent  ((\<lambda>x. -a + x) ` (S-{a}))"
    using affine_dependent_iff_dependent2 assms by auto
  obtain B where B:
    "(\<lambda>x. -a+x) ` (S - {a}) \<subseteq> B \<and> B \<subseteq> (\<lambda>x. -a+x) ` V \<and> independent B \<and> (\<lambda>x. -a+x) ` V \<subseteq> span B"
    using assms
    by (blast intro: maximal_independent_subset_extend[OF _ h0, of "(\<lambda>x. -a + x) ` V"])
  define T where "T = (\<lambda>x. a+x) ` insert 0 B"
  then have "T = insert a ((\<lambda>x. a+x) ` B)"
    by auto
  then have "affine hull T = (\<lambda>x. a+x) ` span B"
    using affine_hull_insert_span_gen[of a "((\<lambda>x. a+x) ` B)"] translation_assoc[of "-a" a B]
    by auto
  then have "V \<subseteq> affine hull T"
    using B assms translation_inverse_subset[of a V "span B"]
    by auto
  moreover have "T \<subseteq> V"
    using T_def B a assms by auto
  ultimately have "affine hull T = affine hull V"
    by (metis Int_absorb1 Int_absorb2 hull_hull hull_mono)
  moreover have "S \<subseteq> T"
    using T_def B translation_inverse_subset[of a "S-{a}" B]
    by auto
  moreover have "\<not> affine_dependent T"
    using T_def affine_dependent_translation_eq[of "insert 0 B"]
      affine_dependent_imp_dependent2 B
    by auto
  ultimately show ?thesis using \<open>T \<subseteq> V\<close> by auto
qed

lemma affine_basis_exists:
  fixes V :: "'n::euclidean_space set"
  shows "\<exists>B. B \<subseteq> V \<and> \<not> affine_dependent B \<and> affine hull V = affine hull B"
proof (cases "V = {}")
  case True
  then show ?thesis
    using affine_independent_0 by auto
next
  case False
  then obtain x where "x \<in> V" by auto
  then show ?thesis
    using affine_dependent_def[of "{x}"] extend_to_affine_basis_nonempty[of "{x}" V]
    by auto
qed

proposition extend_to_affine_basis:
  fixes S V :: "'n::euclidean_space set"
  assumes "\<not> affine_dependent S" "S \<subseteq> V"
  obtains T where "\<not> affine_dependent T" "S \<subseteq> T" "T \<subseteq> V" "affine hull T = affine hull V"
proof (cases "S = {}")
  case True then show ?thesis
    using affine_basis_exists by (metis empty_subsetI that)
next
  case False
  then show ?thesis by (metis assms extend_to_affine_basis_nonempty that)
qed

subsection \<open>Affine Dimension of a Set\<close>

definition\<^marker>\<open>tag important\<close> aff_dim :: "('a::euclidean_space) set \<Rightarrow> int"
  where "aff_dim V =
  (SOME d :: int.
    \<exists>B. affine hull B = affine hull V \<and> \<not> affine_dependent B \<and> of_nat (card B) = d + 1)"

lemma aff_dim_basis_exists:
  fixes V :: "('n::euclidean_space) set"
  shows "\<exists>B. affine hull B = affine hull V \<and> \<not> affine_dependent B \<and> of_nat (card B) = aff_dim V + 1"
proof -
  obtain B where "\<not> affine_dependent B \<and> affine hull B = affine hull V"
    using affine_basis_exists[of V] by auto
  then show ?thesis
    unfolding aff_dim_def
      some_eq_ex[of "\<lambda>d. \<exists>B. affine hull B = affine hull V \<and> \<not> affine_dependent B \<and> of_nat (card B) = d + 1"]
    apply auto
    apply (rule exI[of _ "int (card B) - (1 :: int)"])
    apply (rule exI[of _ "B"], auto)
    done
qed

lemma affine_hull_nonempty: "S \<noteq> {} \<longleftrightarrow> affine hull S \<noteq> {}"
proof -
  have "S = {} \<Longrightarrow> affine hull S = {}"
    using affine_hull_empty by auto
  moreover have "affine hull S = {} \<Longrightarrow> S = {}"
    unfolding hull_def by auto
  ultimately show ?thesis by blast
qed

lemma aff_dim_parallel_subspace_aux:
  fixes B :: "'n::euclidean_space set"
  assumes "\<not> affine_dependent B" "a \<in> B"
  shows "finite B \<and> ((card B) - 1 = dim (span ((\<lambda>x. -a+x) ` (B-{a}))))"
proof -
  have "independent ((\<lambda>x. -a + x) ` (B-{a}))"
    using affine_dependent_iff_dependent2 assms by auto
  then have fin: "dim (span ((\<lambda>x. -a+x) ` (B-{a}))) = card ((\<lambda>x. -a + x) ` (B-{a}))"
    "finite ((\<lambda>x. -a + x) ` (B - {a}))"
    using indep_card_eq_dim_span[of "(\<lambda>x. -a+x) ` (B-{a})"] by auto
  show ?thesis
  proof (cases "(\<lambda>x. -a + x) ` (B - {a}) = {}")
    case True
    have "B = insert a ((\<lambda>x. a + x) ` (\<lambda>x. -a + x) ` (B - {a}))"
      using translation_assoc[of "a" "-a" "(B - {a})"] assms by auto
    then have "B = {a}" using True by auto
    then show ?thesis using assms fin by auto
  next
    case False
    then have "card ((\<lambda>x. -a + x) ` (B - {a})) > 0"
      using fin by auto
    moreover have h1: "card ((\<lambda>x. -a + x) ` (B-{a})) = card (B-{a})"
      by (rule card_image) (use translate_inj_on in blast)
    ultimately have "card (B-{a}) > 0" by auto
    then have *: "finite (B - {a})"
      using card_gt_0_iff[of "(B - {a})"] by auto
    then have "card (B - {a}) = card B - 1"
      using card_Diff_singleton assms by auto
    with * show ?thesis using fin h1 by auto
  qed
qed

lemma aff_dim_parallel_subspace:
  fixes V L :: "'n::euclidean_space set"
  assumes "V \<noteq> {}"
    and "subspace L"
    and "affine_parallel (affine hull V) L"
  shows "aff_dim V = int (dim L)"
proof -
  obtain B where
    B: "affine hull B = affine hull V \<and> \<not> affine_dependent B \<and> int (card B) = aff_dim V + 1"
    using aff_dim_basis_exists by auto
  then have "B \<noteq> {}"
    using assms B affine_hull_nonempty[of V] affine_hull_nonempty[of B]
    by auto
  then obtain a where a: "a \<in> B" by auto
  define Lb where "Lb = span ((\<lambda>x. -a+x) ` (B-{a}))"
  moreover have "affine_parallel (affine hull B) Lb"
    using Lb_def B assms affine_hull_span2[of a B] a
      affine_parallel_commut[of "Lb" "(affine hull B)"]
    unfolding affine_parallel_def
    by auto
  moreover have "subspace Lb"
    using Lb_def subspace_span by auto
  moreover have "affine hull B \<noteq> {}"
    using assms B affine_hull_nonempty[of V] by auto
  ultimately have "L = Lb"
    using assms affine_parallel_subspace[of "affine hull B"] affine_affine_hull[of B] B
    by auto
  then have "dim L = dim Lb"
    by auto
  moreover have "card B - 1 = dim Lb" and "finite B"
    using Lb_def aff_dim_parallel_subspace_aux a B by auto
  ultimately show ?thesis
    using B \<open>B \<noteq> {}\<close> card_gt_0_iff[of B] by auto
qed

lemma aff_independent_finite:
  fixes B :: "'n::euclidean_space set"
  assumes "\<not> affine_dependent B"
  shows "finite B"
proof -
  {
    assume "B \<noteq> {}"
    then obtain a where "a \<in> B" by auto
    then have ?thesis
      using aff_dim_parallel_subspace_aux assms by auto
  }
  then show ?thesis by auto
qed

lemmas independent_finite = independent_imp_finite

lemma span_substd_basis:
  assumes d: "d \<subseteq> Basis"
  shows "span d = {x. \<forall>i\<in>Basis. i \<notin> d \<longrightarrow> x\<bullet>i = 0}"
  (is "_ = ?B")
proof -
  have "d \<subseteq> ?B"
    using d by (auto simp: inner_Basis)
  moreover have s: "subspace ?B"
    using subspace_substandard[of "\<lambda>i. i \<notin> d"] .
  ultimately have "span d \<subseteq> ?B"
    using span_mono[of d "?B"] span_eq_iff[of "?B"] by blast
  moreover have *: "card d \<le> dim (span d)"
    using independent_card_le_dim[of d "span d"] independent_substdbasis[OF assms]
      span_superset[of d]
    by auto
  moreover from * have "dim ?B \<le> dim (span d)"
    using dim_substandard[OF assms] by auto
  ultimately show ?thesis
    using s subspace_dim_equal[of "span d" "?B"] subspace_span[of d] by auto
qed

lemma basis_to_substdbasis_subspace_isomorphism:
  fixes B :: "'a::euclidean_space set"
  assumes "independent B"
  shows "\<exists>f d::'a set. card d = card B \<and> linear f \<and> f ` B = d \<and>
    f ` span B = {x. \<forall>i\<in>Basis. i \<notin> d \<longrightarrow> x \<bullet> i = 0} \<and> inj_on f (span B) \<and> d \<subseteq> Basis"
proof -
  have B: "card B = dim B"
    using dim_unique[of B B "card B"] assms span_superset[of B] by auto
  have "dim B \<le> card (Basis :: 'a set)"
    using dim_subset_UNIV[of B] by simp
  from ex_card[OF this] obtain d :: "'a set" where d: "d \<subseteq> Basis" and t: "card d = dim B"
    by auto
  let ?t = "{x::'a::euclidean_space. \<forall>i\<in>Basis. i \<notin> d \<longrightarrow> x\<bullet>i = 0}"
  have "\<exists>f. linear f \<and> f ` B = d \<and> f ` span B = ?t \<and> inj_on f (span B)"
  proof (intro basis_to_basis_subspace_isomorphism subspace_span subspace_substandard span_superset)
    show "d \<subseteq> {x. \<forall>i\<in>Basis. i \<notin> d \<longrightarrow> x \<bullet> i = 0}"
      using d inner_not_same_Basis by blast
  qed (auto simp: span_substd_basis independent_substdbasis dim_substandard d t B assms)
  with t \<open>card B = dim B\<close> d show ?thesis by auto
qed

lemma aff_dim_empty:
  fixes S :: "'n::euclidean_space set"
  shows "S = {} \<longleftrightarrow> aff_dim S = -1"
proof -
  obtain B where *: "affine hull B = affine hull S"
    and "\<not> affine_dependent B"
    and "int (card B) = aff_dim S + 1"
    using aff_dim_basis_exists by auto
  moreover
  from * have "S = {} \<longleftrightarrow> B = {}"
    using affine_hull_nonempty[of B] affine_hull_nonempty[of S] by auto
  ultimately show ?thesis
    using aff_independent_finite[of B] card_gt_0_iff[of B] by auto
qed

lemma aff_dim_empty_eq [simp]: "aff_dim ({}::'a::euclidean_space set) = -1"
  by (simp add: aff_dim_empty [symmetric])

lemma aff_dim_affine_hull [simp]: "aff_dim (affine hull S) = aff_dim S"
  unfolding aff_dim_def using hull_hull[of _ S] by auto

lemma aff_dim_affine_hull2:
  assumes "affine hull S = affine hull T"
  shows "aff_dim S = aff_dim T"
  unfolding aff_dim_def using assms by auto

lemma aff_dim_unique:
  fixes B V :: "'n::euclidean_space set"
  assumes "affine hull B = affine hull V \<and> \<not> affine_dependent B"
  shows "of_nat (card B) = aff_dim V + 1"
proof (cases "B = {}")
  case True
  then have "V = {}"
    using affine_hull_nonempty[of V] affine_hull_nonempty[of B] assms
    by auto
  then have "aff_dim V = (-1::int)"
    using aff_dim_empty by auto
  then show ?thesis
    using \<open>B = {}\<close> by auto
next
  case False
  then obtain a where a: "a \<in> B" by auto
  define Lb where "Lb = span ((\<lambda>x. -a+x) ` (B-{a}))"
  have "affine_parallel (affine hull B) Lb"
    using Lb_def affine_hull_span2[of a B] a
      affine_parallel_commut[of "Lb" "(affine hull B)"]
    unfolding affine_parallel_def by auto
  moreover have "subspace Lb"
    using Lb_def subspace_span by auto
  ultimately have "aff_dim B = int(dim Lb)"
    using aff_dim_parallel_subspace[of B Lb] \<open>B \<noteq> {}\<close> by auto
  moreover have "(card B) - 1 = dim Lb" "finite B"
    using Lb_def aff_dim_parallel_subspace_aux a assms by auto
  ultimately have "of_nat (card B) = aff_dim B + 1"
    using \<open>B \<noteq> {}\<close> card_gt_0_iff[of B] by auto
  then show ?thesis
    using aff_dim_affine_hull2 assms by auto
qed

lemma aff_dim_affine_independent:
  fixes B :: "'n::euclidean_space set"
  assumes "\<not> affine_dependent B"
  shows "of_nat (card B) = aff_dim B + 1"
  using aff_dim_unique[of B B] assms by auto

lemma affine_independent_iff_card:
    fixes s :: "'a::euclidean_space set"
    shows "\<not> affine_dependent s \<longleftrightarrow> finite s \<and> aff_dim s = int(card s) - 1"
  apply (rule iffI)
  apply (simp add: aff_dim_affine_independent aff_independent_finite)
  by (metis affine_basis_exists [of s] aff_dim_unique card_subset_eq diff_add_cancel of_nat_eq_iff)

lemma aff_dim_sing [simp]:
  fixes a :: "'n::euclidean_space"
  shows "aff_dim {a} = 0"
  using aff_dim_affine_independent[of "{a}"] affine_independent_1 by auto

lemma aff_dim_2 [simp]: "aff_dim {a,b} = (if a = b then 0 else 1)"
proof (clarsimp)
  assume "a \<noteq> b"
  then have "aff_dim{a,b} = card{a,b} - 1"
    using affine_independent_2 [of a b] aff_dim_affine_independent by fastforce
  also have "\<dots> = 1"
    using \<open>a \<noteq> b\<close> by simp
  finally show "aff_dim {a, b} = 1" .
qed

lemma aff_dim_inner_basis_exists:
  fixes V :: "('n::euclidean_space) set"
  shows "\<exists>B. B \<subseteq> V \<and> affine hull B = affine hull V \<and>
    \<not> affine_dependent B \<and> of_nat (card B) = aff_dim V + 1"
proof -
  obtain B where B: "\<not> affine_dependent B" "B \<subseteq> V" "affine hull B = affine hull V"
    using affine_basis_exists[of V] by auto
  then have "of_nat(card B) = aff_dim V+1" using aff_dim_unique by auto
  with B show ?thesis by auto
qed

lemma aff_dim_le_card:
  fixes V :: "'n::euclidean_space set"
  assumes "finite V"
  shows "aff_dim V \<le> of_nat (card V) - 1"
proof -
  obtain B where B: "B \<subseteq> V" "of_nat (card B) = aff_dim V + 1"
    using aff_dim_inner_basis_exists[of V] by auto
  then have "card B \<le> card V"
    using assms card_mono by auto
  with B show ?thesis by auto
qed

lemma aff_dim_parallel_eq:
  fixes S T :: "'n::euclidean_space set"
  assumes "affine_parallel (affine hull S) (affine hull T)"
  shows "aff_dim S = aff_dim T"
proof -
  {
    assume "T \<noteq> {}" "S \<noteq> {}"
    then obtain L where L: "subspace L \<and> affine_parallel (affine hull T) L"
      using affine_parallel_subspace[of "affine hull T"]
        affine_affine_hull[of T] affine_hull_nonempty
      by auto
    then have "aff_dim T = int (dim L)"
      using aff_dim_parallel_subspace \<open>T \<noteq> {}\<close> by auto
    moreover have *: "subspace L \<and> affine_parallel (affine hull S) L"
       using L affine_parallel_assoc[of "affine hull S" "affine hull T" L] assms by auto
    moreover from * have "aff_dim S = int (dim L)"
      using aff_dim_parallel_subspace \<open>S \<noteq> {}\<close> by auto
    ultimately have ?thesis by auto
  }
  moreover
  {
    assume "S = {}"
    then have "S = {}" and "T = {}"
      using assms affine_hull_nonempty
      unfolding affine_parallel_def
      by auto
    then have ?thesis using aff_dim_empty by auto
  }
  moreover
  {
    assume "T = {}"
    then have "S = {}" and "T = {}"
      using assms affine_hull_nonempty
      unfolding affine_parallel_def
      by auto
    then have ?thesis
      using aff_dim_empty by auto
  }
  ultimately show ?thesis by blast
qed

lemma aff_dim_translation_eq:
  "aff_dim ((+) a ` S) = aff_dim S" for a :: "'n::euclidean_space"
proof -
  have "affine_parallel (affine hull S) (affine hull ((\<lambda>x. a + x) ` S))"
    unfolding affine_parallel_def
    apply (rule exI[of _ "a"])
    using affine_hull_translation[of a S]
    apply auto
    done
  then show ?thesis
    using aff_dim_parallel_eq[of S "(\<lambda>x. a + x) ` S"] by auto
qed

lemma aff_dim_translation_eq_subtract:
  "aff_dim ((\<lambda>x. x - a) ` S) = aff_dim S" for a :: "'n::euclidean_space"
  using aff_dim_translation_eq [of "- a"] by (simp cong: image_cong_simp)

lemma aff_dim_affine:
  fixes S L :: "'n::euclidean_space set"
  assumes "S \<noteq> {}"
    and "affine S"
    and "subspace L"
    and "affine_parallel S L"
  shows "aff_dim S = int (dim L)"
proof -
  have *: "affine hull S = S"
    using assms affine_hull_eq[of S] by auto
  then have "affine_parallel (affine hull S) L"
    using assms by (simp add: *)
  then show ?thesis
    using assms aff_dim_parallel_subspace[of S L] by blast
qed

lemma dim_affine_hull:
  fixes S :: "'n::euclidean_space set"
  shows "dim (affine hull S) = dim S"
proof -
  have "dim (affine hull S) \<ge> dim S"
    using dim_subset by auto
  moreover have "dim (span S) \<ge> dim (affine hull S)"
    using dim_subset affine_hull_subset_span by blast
  moreover have "dim (span S) = dim S"
    using dim_span by auto
  ultimately show ?thesis by auto
qed

lemma aff_dim_subspace:
  fixes S :: "'n::euclidean_space set"
  assumes "subspace S"
  shows "aff_dim S = int (dim S)"
proof (cases "S={}")
  case True with assms show ?thesis
    by (simp add: subspace_affine)
next
  case False
  with aff_dim_affine[of S S] assms subspace_imp_affine[of S] affine_parallel_reflex[of S] subspace_affine
  show ?thesis by auto
qed

lemma aff_dim_zero:
  fixes S :: "'n::euclidean_space set"
  assumes "0 \<in> affine hull S"
  shows "aff_dim S = int (dim S)"
proof -
  have "subspace (affine hull S)"
    using subspace_affine[of "affine hull S"] affine_affine_hull assms
    by auto
  then have "aff_dim (affine hull S) = int (dim (affine hull S))"
    using assms aff_dim_subspace[of "affine hull S"] by auto
  then show ?thesis
    using aff_dim_affine_hull[of S] dim_affine_hull[of S]
    by auto
qed

lemma aff_dim_eq_dim:
  "aff_dim S = int (dim ((+) (- a) ` S))" if "a \<in> affine hull S"
    for S :: "'n::euclidean_space set"
proof -
  have "0 \<in> affine hull (+) (- a) ` S"
    unfolding affine_hull_translation
    using that by (simp add: ac_simps)
  with aff_dim_zero show ?thesis
    by (metis aff_dim_translation_eq)
qed

lemma aff_dim_eq_dim_subtract:
  "aff_dim S = int (dim ((\<lambda>x. x - a) ` S))" if "a \<in> affine hull S"
    for S :: "'n::euclidean_space set"
  using aff_dim_eq_dim [of a] that by (simp cong: image_cong_simp)

lemma aff_dim_UNIV [simp]: "aff_dim (UNIV :: 'n::euclidean_space set) = int(DIM('n))"
  using aff_dim_subspace[of "(UNIV :: 'n::euclidean_space set)"]
    dim_UNIV[where 'a="'n::euclidean_space"]
  by auto

lemma aff_dim_geq:
  fixes V :: "'n::euclidean_space set"
  shows "aff_dim V \<ge> -1"
proof -
  obtain B where "affine hull B = affine hull V"
    and "\<not> affine_dependent B"
    and "int (card B) = aff_dim V + 1"
    using aff_dim_basis_exists by auto
  then show ?thesis by auto
qed

lemma aff_dim_negative_iff [simp]:
  fixes S :: "'n::euclidean_space set"
  shows "aff_dim S < 0 \<longleftrightarrow>S = {}"
by (metis aff_dim_empty aff_dim_geq diff_0 eq_iff zle_diff1_eq)

lemma aff_lowdim_subset_hyperplane:
  fixes S :: "'a::euclidean_space set"
  assumes "aff_dim S < DIM('a)"
  obtains a b where "a \<noteq> 0" "S \<subseteq> {x. a \<bullet> x = b}"
proof (cases "S={}")
  case True
  moreover
  have "(SOME b. b \<in> Basis) \<noteq> 0"
    by (metis norm_some_Basis norm_zero zero_neq_one)
  ultimately show ?thesis
    using that by blast
next
  case False
  then obtain c S' where "c \<notin> S'" "S = insert c S'"
    by (meson equals0I mk_disjoint_insert)
  have "dim ((+) (-c) ` S) < DIM('a)"
    by (metis \<open>S = insert c S'\<close> aff_dim_eq_dim assms hull_inc insertI1 of_nat_less_imp_less)
  then obtain a where "a \<noteq> 0" "span ((+) (-c) ` S) \<subseteq> {x. a \<bullet> x = 0}"
    using lowdim_subset_hyperplane by blast
  moreover
  have "a \<bullet> w = a \<bullet> c" if "span ((+) (- c) ` S) \<subseteq> {x. a \<bullet> x = 0}" "w \<in> S" for w
  proof -
    have "w-c \<in> span ((+) (- c) ` S)"
      by (simp add: span_base \<open>w \<in> S\<close>)
    with that have "w-c \<in> {x. a \<bullet> x = 0}"
      by blast
    then show ?thesis
      by (auto simp: algebra_simps)
  qed
  ultimately have "S \<subseteq> {x. a \<bullet> x = a \<bullet> c}"
    by blast
  then show ?thesis
    by (rule that[OF \<open>a \<noteq> 0\<close>])
qed

lemma affine_independent_card_dim_diffs:
  fixes S :: "'a :: euclidean_space set"
  assumes "\<not> affine_dependent S" "a \<in> S"
    shows "card S = dim {x - a|x. x \<in> S} + 1"
proof -
  have 1: "{b - a|b. b \<in> (S - {a})} \<subseteq> {x - a|x. x \<in> S}" by auto
  have 2: "x - a \<in> span {b - a |b. b \<in> S - {a}}" if "x \<in> S" for x
  proof (cases "x = a")
    case True then show ?thesis by (simp add: span_clauses)
  next
    case False then show ?thesis
      using assms by (blast intro: span_base that)
  qed
  have "\<not> affine_dependent (insert a S)"
    by (simp add: assms insert_absorb)
  then have 3: "independent {b - a |b. b \<in> S - {a}}"
      using dependent_imp_affine_dependent by fastforce
  have "{b - a |b. b \<in> S - {a}} = (\<lambda>b. b-a) ` (S - {a})"
    by blast
  then have "card {b - a |b. b \<in> S - {a}} = card ((\<lambda>b. b-a) ` (S - {a}))"
    by simp
  also have "\<dots> = card (S - {a})"
    by (metis (no_types, lifting) card_image diff_add_cancel inj_onI)
  also have "\<dots> = card S - 1"
    by (simp add: aff_independent_finite assms)
  finally have 4: "card {b - a |b. b \<in> S - {a}} = card S - 1" .
  have "finite S"
    by (meson assms aff_independent_finite)
  with \<open>a \<in> S\<close> have "card S \<noteq> 0" by auto
  moreover have "dim {x - a |x. x \<in> S} = card S - 1"
    using 2 by (blast intro: dim_unique [OF 1 _ 3 4])
  ultimately show ?thesis
    by auto
qed

lemma independent_card_le_aff_dim:
  fixes B :: "'n::euclidean_space set"
  assumes "B \<subseteq> V"
  assumes "\<not> affine_dependent B"
  shows "int (card B) \<le> aff_dim V + 1"
proof -
  obtain T where T: "\<not> affine_dependent T \<and> B \<subseteq> T \<and> T \<subseteq> V \<and> affine hull T = affine hull V"
    by (metis assms extend_to_affine_basis[of B V])
  then have "of_nat (card T) = aff_dim V + 1"
    using aff_dim_unique by auto
  then show ?thesis
    using T card_mono[of T B] aff_independent_finite[of T] by auto
qed

lemma aff_dim_subset:
  fixes S T :: "'n::euclidean_space set"
  assumes "S \<subseteq> T"
  shows "aff_dim S \<le> aff_dim T"
proof -
  obtain B where B: "\<not> affine_dependent B" "B \<subseteq> S" "affine hull B = affine hull S"
    "of_nat (card B) = aff_dim S + 1"
    using aff_dim_inner_basis_exists[of S] by auto
  then have "int (card B) \<le> aff_dim T + 1"
    using assms independent_card_le_aff_dim[of B T] by auto
  with B show ?thesis by auto
qed

lemma aff_dim_le_DIM:
  fixes S :: "'n::euclidean_space set"
  shows "aff_dim S \<le> int (DIM('n))"
proof -
  have "aff_dim (UNIV :: 'n::euclidean_space set) = int(DIM('n))"
    using aff_dim_UNIV by auto
  then show "aff_dim (S:: 'n::euclidean_space set) \<le> int(DIM('n))"
    using aff_dim_subset[of S "(UNIV :: ('n::euclidean_space) set)"] subset_UNIV by auto
qed

lemma affine_dim_equal:
  fixes S :: "'n::euclidean_space set"
  assumes "affine S" "affine T" "S \<noteq> {}" "S \<subseteq> T" "aff_dim S = aff_dim T"
  shows "S = T"
proof -
  obtain a where "a \<in> S" using assms by auto
  then have "a \<in> T" using assms by auto
  define LS where "LS = {y. \<exists>x \<in> S. (-a) + x = y}"
  then have ls: "subspace LS" "affine_parallel S LS"
    using assms parallel_subspace_explicit[of S a LS] \<open>a \<in> S\<close> by auto
  then have h1: "int(dim LS) = aff_dim S"
    using assms aff_dim_affine[of S LS] by auto
  have "T \<noteq> {}" using assms by auto
  define LT where "LT = {y. \<exists>x \<in> T. (-a) + x = y}"
  then have lt: "subspace LT \<and> affine_parallel T LT"
    using assms parallel_subspace_explicit[of T a LT] \<open>a \<in> T\<close> by auto
  then have "int(dim LT) = aff_dim T"
    using assms aff_dim_affine[of T LT] \<open>T \<noteq> {}\<close> by auto
  then have "dim LS = dim LT"
    using h1 assms by auto
  moreover have "LS \<le> LT"
    using LS_def LT_def assms by auto
  ultimately have "LS = LT"
    using subspace_dim_equal[of LS LT] ls lt by auto
  moreover have "S = {x. \<exists>y \<in> LS. a+y=x}"
    using LS_def by auto
  moreover have "T = {x. \<exists>y \<in> LT. a+y=x}"
    using LT_def by auto
  ultimately show ?thesis by auto
qed

lemma aff_dim_eq_0:
  fixes S :: "'a::euclidean_space set"
  shows "aff_dim S = 0 \<longleftrightarrow> (\<exists>a. S = {a})"
proof (cases "S = {}")
  case True
  then show ?thesis
    by auto
next
  case False
  then obtain a where "a \<in> S" by auto
  show ?thesis
  proof safe
    assume 0: "aff_dim S = 0"
    have "\<not> {a,b} \<subseteq> S" if "b \<noteq> a" for b
      by (metis "0" aff_dim_2 aff_dim_subset not_one_le_zero that)
    then show "\<exists>a. S = {a}"
      using \<open>a \<in> S\<close> by blast
  qed auto
qed

lemma affine_hull_UNIV:
  fixes S :: "'n::euclidean_space set"
  assumes "aff_dim S = int(DIM('n))"
  shows "affine hull S = (UNIV :: ('n::euclidean_space) set)"
proof -
  have "S \<noteq> {}"
    using assms aff_dim_empty[of S] by auto
  have h0: "S \<subseteq> affine hull S"
    using hull_subset[of S _] by auto
  have h1: "aff_dim (UNIV :: ('n::euclidean_space) set) = aff_dim S"
    using aff_dim_UNIV assms by auto
  then have h2: "aff_dim (affine hull S) \<le> aff_dim (UNIV :: ('n::euclidean_space) set)"
    using aff_dim_le_DIM[of "affine hull S"] assms h0 by auto
  have h3: "aff_dim S \<le> aff_dim (affine hull S)"
    using h0 aff_dim_subset[of S "affine hull S"] assms by auto
  then have h4: "aff_dim (affine hull S) = aff_dim (UNIV :: ('n::euclidean_space) set)"
    using h0 h1 h2 by auto
  then show ?thesis
    using affine_dim_equal[of "affine hull S" "(UNIV :: ('n::euclidean_space) set)"]
      affine_affine_hull[of S] affine_UNIV assms h4 h0 \<open>S \<noteq> {}\<close>
    by auto
qed

lemma disjoint_affine_hull:
  fixes s :: "'n::euclidean_space set"
  assumes "\<not> affine_dependent s" "t \<subseteq> s" "u \<subseteq> s" "t \<inter> u = {}"
    shows "(affine hull t) \<inter> (affine hull u) = {}"
proof -
  have "finite s" using assms by (simp add: aff_independent_finite)
  then have "finite t" "finite u" using assms finite_subset by blast+
  { fix y
    assume yt: "y \<in> affine hull t" and yu: "y \<in> affine hull u"
    then obtain a b
           where a1 [simp]: "sum a t = 1" and [simp]: "sum (\<lambda>v. a v *\<^sub>R v) t = y"
             and [simp]: "sum b u = 1" "sum (\<lambda>v. b v *\<^sub>R v) u = y"
      by (auto simp: affine_hull_finite \<open>finite t\<close> \<open>finite u\<close>)
    define c where "c x = (if x \<in> t then a x else if x \<in> u then -(b x) else 0)" for x
    have [simp]: "s \<inter> t = t" "s \<inter> - t \<inter> u = u" using assms by auto
    have "sum c s = 0"
      by (simp add: c_def comm_monoid_add_class.sum.If_cases \<open>finite s\<close> sum_negf)
    moreover have "\<not> (\<forall>v\<in>s. c v = 0)"
      by (metis (no_types) IntD1 \<open>s \<inter> t = t\<close> a1 c_def sum_not_0 zero_neq_one)
    moreover have "(\<Sum>v\<in>s. c v *\<^sub>R v) = 0"
      by (simp add: c_def if_smult sum_negf
             comm_monoid_add_class.sum.If_cases \<open>finite s\<close>)
    ultimately have False
      using assms \<open>finite s\<close> by (auto simp: affine_dependent_explicit)
  }
  then show ?thesis by blast
qed

lemma aff_dim_convex_hull:
  fixes S :: "'n::euclidean_space set"
  shows "aff_dim (convex hull S) = aff_dim S"
  using aff_dim_affine_hull[of S] convex_hull_subset_affine_hull[of S]
    hull_subset[of S "convex"] aff_dim_subset[of S "convex hull S"]
    aff_dim_subset[of "convex hull S" "affine hull S"]
  by auto

subsection \<open>Caratheodory's theorem\<close>

lemma convex_hull_caratheodory_aff_dim:
  fixes p :: "('a::euclidean_space) set"
  shows "convex hull p =
    {y. \<exists>s u. finite s \<and> s \<subseteq> p \<and> card s \<le> aff_dim p + 1 \<and>
      (\<forall>x\<in>s. 0 \<le> u x) \<and> sum u s = 1 \<and> sum (\<lambda>v. u v *\<^sub>R v) s = y}"
  unfolding convex_hull_explicit set_eq_iff mem_Collect_eq
proof (intro allI iffI)
  fix y
  let ?P = "\<lambda>n. \<exists>s u. finite s \<and> card s = n \<and> s \<subseteq> p \<and> (\<forall>x\<in>s. 0 \<le> u x) \<and>
    sum u s = 1 \<and> (\<Sum>v\<in>s. u v *\<^sub>R v) = y"
  assume "\<exists>s u. finite s \<and> s \<subseteq> p \<and> (\<forall>x\<in>s. 0 \<le> u x) \<and> sum u s = 1 \<and> (\<Sum>v\<in>s. u v *\<^sub>R v) = y"
  then obtain N where "?P N" by auto
  then have "\<exists>n\<le>N. (\<forall>k<n. \<not> ?P k) \<and> ?P n"
    apply (rule_tac ex_least_nat_le, auto)
    done
  then obtain n where "?P n" and smallest: "\<forall>k<n. \<not> ?P k"
    by blast
  then obtain s u where obt: "finite s" "card s = n" "s\<subseteq>p" "\<forall>x\<in>s. 0 \<le> u x"
    "sum u s = 1"  "(\<Sum>v\<in>s. u v *\<^sub>R v) = y" by auto

  have "card s \<le> aff_dim p + 1"
  proof (rule ccontr, simp only: not_le)
    assume "aff_dim p + 1 < card s"
    then have "affine_dependent s"
      using affine_dependent_biggerset[OF obt(1)] independent_card_le_aff_dim not_less obt(3)
      by blast
    then obtain w v where wv: "sum w s = 0" "v\<in>s" "w v \<noteq> 0" "(\<Sum>v\<in>s. w v *\<^sub>R v) = 0"
      using affine_dependent_explicit_finite[OF obt(1)] by auto
    define i where "i = (\<lambda>v. (u v) / (- w v)) ` {v\<in>s. w v < 0}"
    define t where "t = Min i"
    have "\<exists>x\<in>s. w x < 0"
    proof (rule ccontr, simp add: not_less)
      assume as:"\<forall>x\<in>s. 0 \<le> w x"
      then have "sum w (s - {v}) \<ge> 0"
        apply (rule_tac sum_nonneg, auto)
        done
      then have "sum w s > 0"
        unfolding sum.remove[OF obt(1) \<open>v\<in>s\<close>]
        using as[THEN bspec[where x=v]]  \<open>v\<in>s\<close>  \<open>w v \<noteq> 0\<close> by auto
      then show False using wv(1) by auto
    qed
    then have "i \<noteq> {}" unfolding i_def by auto
    then have "t \<ge> 0"
      using Min_ge_iff[of i 0 ] and obt(1)
      unfolding t_def i_def
      using obt(4)[unfolded le_less]
      by (auto simp: divide_le_0_iff)
    have t: "\<forall>v\<in>s. u v + t * w v \<ge> 0"
    proof
      fix v
      assume "v \<in> s"
      then have v: "0 \<le> u v"
        using obt(4)[THEN bspec[where x=v]] by auto
      show "0 \<le> u v + t * w v"
      proof (cases "w v < 0")
        case False
        thus ?thesis using v \<open>t\<ge>0\<close> by auto
      next
        case True
        then have "t \<le> u v / (- w v)"
          using \<open>v\<in>s\<close> unfolding t_def i_def
          apply (rule_tac Min_le)
          using obt(1) apply auto
          done
        then show ?thesis
          unfolding real_0_le_add_iff
          using pos_le_divide_eq[OF True[unfolded neg_0_less_iff_less[symmetric]]]
          by auto
      qed
    qed
    obtain a where "a \<in> s" and "t = (\<lambda>v. (u v) / (- w v)) a" and "w a < 0"
      using Min_in[OF _ \<open>i\<noteq>{}\<close>] and obt(1) unfolding i_def t_def by auto
    then have a: "a \<in> s" "u a + t * w a = 0" by auto
    have *: "\<And>f. sum f (s - {a}) = sum f s - ((f a)::'b::ab_group_add)"
      unfolding sum.remove[OF obt(1) \<open>a\<in>s\<close>] by auto
    have "(\<Sum>v\<in>s. u v + t * w v) = 1"
      unfolding sum.distrib wv(1) sum_distrib_left[symmetric] obt(5) by auto
    moreover have "(\<Sum>v\<in>s. u v *\<^sub>R v + (t * w v) *\<^sub>R v) - (u a *\<^sub>R a + (t * w a) *\<^sub>R a) = y"
      unfolding sum.distrib obt(6) scaleR_scaleR[symmetric] scaleR_right.sum [symmetric] wv(4)
      using a(2) [THEN eq_neg_iff_add_eq_0 [THEN iffD2]] by simp
    ultimately have "?P (n - 1)"
      apply (rule_tac x="(s - {a})" in exI)
      apply (rule_tac x="\<lambda>v. u v + t * w v" in exI)
      using obt(1-3) and t and a
      apply (auto simp: * scaleR_left_distrib)
      done
    then show False
      using smallest[THEN spec[where x="n - 1"]] by auto
  qed
  then show "\<exists>s u. finite s \<and> s \<subseteq> p \<and> card s \<le> aff_dim p + 1 \<and>
      (\<forall>x\<in>s. 0 \<le> u x) \<and> sum u s = 1 \<and> (\<Sum>v\<in>s. u v *\<^sub>R v) = y"
    using obt by auto
qed auto

lemma caratheodory_aff_dim:
  fixes p :: "('a::euclidean_space) set"
  shows "convex hull p = {x. \<exists>s. finite s \<and> s \<subseteq> p \<and> card s \<le> aff_dim p + 1 \<and> x \<in> convex hull s}"
        (is "?lhs = ?rhs")
proof
  show "?lhs \<subseteq> ?rhs"
    apply (subst convex_hull_caratheodory_aff_dim, clarify)
    apply (rule_tac x=s in exI)
    apply (simp add: hull_subset convex_explicit [THEN iffD1, OF convex_convex_hull])
    done
next
  show "?rhs \<subseteq> ?lhs"
    using hull_mono by blast
qed

lemma convex_hull_caratheodory:
  fixes p :: "('a::euclidean_space) set"
  shows "convex hull p =
            {y. \<exists>s u. finite s \<and> s \<subseteq> p \<and> card s \<le> DIM('a) + 1 \<and>
              (\<forall>x\<in>s. 0 \<le> u x) \<and> sum u s = 1 \<and> sum (\<lambda>v. u v *\<^sub>R v) s = y}"
        (is "?lhs = ?rhs")
proof (intro set_eqI iffI)
  fix x
  assume "x \<in> ?lhs" then show "x \<in> ?rhs"
    apply (simp only: convex_hull_caratheodory_aff_dim Set.mem_Collect_eq)
    apply (erule ex_forward)+
    using aff_dim_le_DIM [of p]
    apply simp
    done
next
  fix x
  assume "x \<in> ?rhs" then show "x \<in> ?lhs"
    by (auto simp: convex_hull_explicit)
qed

theorem caratheodory:
  "convex hull p =
    {x::'a::euclidean_space. \<exists>s. finite s \<and> s \<subseteq> p \<and>
      card s \<le> DIM('a) + 1 \<and> x \<in> convex hull s}"
proof safe
  fix x
  assume "x \<in> convex hull p"
  then obtain s u where "finite s" "s \<subseteq> p" "card s \<le> DIM('a) + 1"
    "\<forall>x\<in>s. 0 \<le> u x" "sum u s = 1" "(\<Sum>v\<in>s. u v *\<^sub>R v) = x"
    unfolding convex_hull_caratheodory by auto
  then show "\<exists>s. finite s \<and> s \<subseteq> p \<and> card s \<le> DIM('a) + 1 \<and> x \<in> convex hull s"
    apply (rule_tac x=s in exI)
    using hull_subset[of s convex]
    using convex_convex_hull[simplified convex_explicit, of s,
      THEN spec[where x=s], THEN spec[where x=u]]
    apply auto
    done
next
  fix x s
  assume  "finite s" "s \<subseteq> p" "card s \<le> DIM('a) + 1" "x \<in> convex hull s"
  then show "x \<in> convex hull p"
    using hull_mono[OF \<open>s\<subseteq>p\<close>] by auto
qed

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
  unfolding set_plus_image
  apply (subst convex_hull_linear_image [symmetric])
  apply (simp add: linear_iff scaleR_right_distrib)
  apply (simp add: convex_hull_Times)
  done

lemma translation_eq_singleton_plus: "(\<lambda>x. a + x) ` T = {a} + T"
  unfolding set_plus_def by auto

lemma convex_hull_translation:
  "convex hull ((\<lambda>x. a + x) ` S) = (\<lambda>x. a + x) ` (convex hull S)"
  unfolding translation_eq_singleton_plus
  by (simp only: convex_hull_set_plus convex_hull_singleton)

lemma convex_hull_scaling:
  "convex hull ((\<lambda>x. c *\<^sub>R x) ` S) = (\<lambda>x. c *\<^sub>R x) ` (convex hull S)"
  using linear_scaleR by (rule convex_hull_linear_image [symmetric])

lemma convex_hull_affinity:
  "convex hull ((\<lambda>x. a + c *\<^sub>R x) ` S) = (\<lambda>x. a + c *\<^sub>R x) ` (convex hull S)"
  by(simp only: image_image[symmetric] convex_hull_scaling convex_hull_translation)


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
    using cone_cone_hull[of S] xy cone_def[of "cone hull S"] by auto
  from * obtain cx :: real and xx where x: "u *\<^sub>R x = cx *\<^sub>R xx" "cx \<ge> 0" "xx \<in> S"
    using cone_hull_expl[of S] by auto
  from * obtain cy :: real and yy where y: "v *\<^sub>R y = cy *\<^sub>R yy" "cy \<ge> 0" "yy \<in> S"
    using cone_hull_expl[of S] by auto
  {
    assume "cx + cy \<le> 0"
    then have "u *\<^sub>R x = 0" and "v *\<^sub>R y = 0"
      using x y by auto
    then have "u *\<^sub>R x + v *\<^sub>R y = 0"
      by auto
    then have "u *\<^sub>R x + v *\<^sub>R y \<in> cone hull S"
      using cone_hull_contains_0[of S] \<open>S \<noteq> {}\<close> by auto
  }
  moreover
  {
    assume "cx + cy > 0"
    then have "(cx / (cx + cy)) *\<^sub>R xx + (cy / (cx + cy)) *\<^sub>R yy \<in> S"
      using assms mem_convex_alt[of S xx yy cx cy] x y by auto
    then have "cx *\<^sub>R xx + cy *\<^sub>R yy \<in> cone hull S"
      using mem_cone_hull[of "(cx/(cx+cy)) *\<^sub>R xx + (cy/(cx+cy)) *\<^sub>R yy" S "cx+cy"] \<open>cx+cy>0\<close>
      by (auto simp: scaleR_right_distrib)
    then have "u *\<^sub>R x + v *\<^sub>R y \<in> cone hull S"
      using x y by auto
  }
  moreover have "cx + cy \<le> 0 \<or> cx + cy > 0" by auto
  ultimately show "u *\<^sub>R x + v *\<^sub>R y \<in> cone hull S" by blast
qed

lemma cone_convex_hull:
  assumes "cone S"
  shows "cone (convex hull S)"
proof (cases "S = {}")
  case True
  then show ?thesis by auto
next
  case False
  then have *: "0 \<in> S \<and> (\<forall>c. c > 0 \<longrightarrow> (*\<^sub>R) c ` S = S)"
    using cone_iff[of S] assms by auto
  {
    fix c :: real
    assume "c > 0"
    then have "(*\<^sub>R) c ` (convex hull S) = convex hull ((*\<^sub>R) c ` S)"
      using convex_hull_scaling[of _ S] by auto
    also have "\<dots> = convex hull S"
      using * \<open>c > 0\<close> by auto
    finally have "(*\<^sub>R) c ` (convex hull S) = convex hull S"
      by auto
  }
  then have "0 \<in> convex hull S" "\<And>c. c > 0 \<Longrightarrow> ((*\<^sub>R) c ` (convex hull S)) = (convex hull S)"
    using * hull_subset[of S convex] by auto
  then show ?thesis
    using \<open>S \<noteq> {}\<close> cone_iff[of "convex hull S"] by auto
qed

subsection \<open>Radon's theorem\<close>

text "Formalized by Lars Schewe."

lemma Radon_ex_lemma:
  assumes "finite c" "affine_dependent c"
  shows "\<exists>u. sum u c = 0 \<and> (\<exists>v\<in>c. u v \<noteq> 0) \<and> sum (\<lambda>v. u v *\<^sub>R v) c = 0"
proof -
  from assms(2)[unfolded affine_dependent_explicit]
  obtain s u where
      "finite s" "s \<subseteq> c" "sum u s = 0" "\<exists>v\<in>s. u v \<noteq> 0" "(\<Sum>v\<in>s. u v *\<^sub>R v) = 0"
    by blast
  then show ?thesis
    apply (rule_tac x="\<lambda>v. if v\<in>s then u v else 0" in exI)
    unfolding if_smult scaleR_zero_left and sum.inter_restrict[OF assms(1), symmetric]
    apply (auto simp: Int_absorb1)
    done
qed

lemma Radon_s_lemma:
  assumes "finite s"
    and "sum f s = (0::real)"
  shows "sum f {x\<in>s. 0 < f x} = - sum f {x\<in>s. f x < 0}"
proof -
  have *: "\<And>x. (if f x < 0 then f x else 0) + (if 0 < f x then f x else 0) = f x"
    by auto
  show ?thesis
    unfolding add_eq_0_iff[symmetric] and sum.inter_filter[OF assms(1)]
      and sum.distrib[symmetric] and *
    using assms(2)
    by assumption
qed

lemma Radon_v_lemma:
  assumes "finite s"
    and "sum f s = 0"
    and "\<forall>x. g x = (0::real) \<longrightarrow> f x = (0::'a::euclidean_space)"
  shows "(sum f {x\<in>s. 0 < g x}) = - sum f {x\<in>s. g x < 0}"
proof -
  have *: "\<And>x. (if 0 < g x then f x else 0) + (if g x < 0 then f x else 0) = f x"
    using assms(3) by auto
  show ?thesis
    unfolding eq_neg_iff_add_eq_0 and sum.inter_filter[OF assms(1)]
      and sum.distrib[symmetric] and *
    using assms(2)
    apply assumption
    done
qed

lemma Radon_partition:
  assumes "finite c" "affine_dependent c"
  shows "\<exists>m p. m \<inter> p = {} \<and> m \<union> p = c \<and> (convex hull m) \<inter> (convex hull p) \<noteq> {}"
proof -
  obtain u v where uv: "sum u c = 0" "v\<in>c" "u v \<noteq> 0"  "(\<Sum>v\<in>c. u v *\<^sub>R v) = 0"
    using Radon_ex_lemma[OF assms] by auto
  have fin: "finite {x \<in> c. 0 < u x}" "finite {x \<in> c. 0 > u x}"
    using assms(1) by auto
  define z  where "z = inverse (sum u {x\<in>c. u x > 0}) *\<^sub>R sum (\<lambda>x. u x *\<^sub>R x) {x\<in>c. u x > 0}"
  have "sum u {x \<in> c. 0 < u x} \<noteq> 0"
  proof (cases "u v \<ge> 0")
    case False
    then have "u v < 0" by auto
    then show ?thesis
    proof (cases "\<exists>w\<in>{x \<in> c. 0 < u x}. u w > 0")
      case True
      then show ?thesis
        using sum_nonneg_eq_0_iff[of _ u, OF fin(1)] by auto
    next
      case False
      then have "sum u c \<le> sum (\<lambda>x. if x=v then u v else 0) c"
        apply (rule_tac sum_mono, auto)
        done
      then show ?thesis
        unfolding sum.delta[OF assms(1)] using uv(2) and \<open>u v < 0\<close> and uv(1) by auto
    qed
  qed (insert sum_nonneg_eq_0_iff[of _ u, OF fin(1)] uv(2-3), auto)

  then have *: "sum u {x\<in>c. u x > 0} > 0"
    unfolding less_le
    apply (rule_tac conjI)
    apply (rule_tac sum_nonneg, auto)
    done
  moreover have "sum u ({x \<in> c. 0 < u x} \<union> {x \<in> c. u x < 0}) = sum u c"
    "(\<Sum>x\<in>{x \<in> c. 0 < u x} \<union> {x \<in> c. u x < 0}. u x *\<^sub>R x) = (\<Sum>x\<in>c. u x *\<^sub>R x)"
    using assms(1)
    apply (rule_tac[!] sum.mono_neutral_left, auto)
    done
  then have "sum u {x \<in> c. 0 < u x} = - sum u {x \<in> c. 0 > u x}"
    "(\<Sum>x\<in>{x \<in> c. 0 < u x}. u x *\<^sub>R x) = - (\<Sum>x\<in>{x \<in> c. 0 > u x}. u x *\<^sub>R x)"
    unfolding eq_neg_iff_add_eq_0
    using uv(1,4)
    by (auto simp: sum.union_inter_neutral[OF fin, symmetric])
  moreover have "\<forall>x\<in>{v \<in> c. u v < 0}. 0 \<le> inverse (sum u {x \<in> c. 0 < u x}) * - u x"
    apply rule
    apply (rule mult_nonneg_nonneg)
    using *
    apply auto
    done
  ultimately have "z \<in> convex hull {v \<in> c. u v \<le> 0}"
    unfolding convex_hull_explicit mem_Collect_eq
    apply (rule_tac x="{v \<in> c. u v < 0}" in exI)
    apply (rule_tac x="\<lambda>y. inverse (sum u {x\<in>c. u x > 0}) * - u y" in exI)
    using assms(1) unfolding scaleR_scaleR[symmetric] scaleR_right.sum [symmetric] and z_def
    apply (auto simp: sum_negf sum_distrib_left[symmetric])
    done
  moreover have "\<forall>x\<in>{v \<in> c. 0 < u v}. 0 \<le> inverse (sum u {x \<in> c. 0 < u x}) * u x"
    apply rule
    apply (rule mult_nonneg_nonneg)
    using *
    apply auto
    done
  then have "z \<in> convex hull {v \<in> c. u v > 0}"
    unfolding convex_hull_explicit mem_Collect_eq
    apply (rule_tac x="{v \<in> c. 0 < u v}" in exI)
    apply (rule_tac x="\<lambda>y. inverse (sum u {x\<in>c. u x > 0}) * u y" in exI)
    using assms(1)
    unfolding scaleR_scaleR[symmetric] scaleR_right.sum [symmetric] and z_def
    using *
    apply (auto simp: sum_negf sum_distrib_left[symmetric])
    done
  ultimately show ?thesis
    apply (rule_tac x="{v\<in>c. u v \<le> 0}" in exI)
    apply (rule_tac x="{v\<in>c. u v > 0}" in exI, auto)
    done
qed

theorem Radon:
  assumes "affine_dependent c"
  obtains m p where "m \<subseteq> c" "p \<subseteq> c" "m \<inter> p = {}" "(convex hull m) \<inter> (convex hull p) \<noteq> {}"
proof -
  from assms[unfolded affine_dependent_explicit]
  obtain s u where
      "finite s" "s \<subseteq> c" "sum u s = 0" "\<exists>v\<in>s. u v \<noteq> 0" "(\<Sum>v\<in>s. u v *\<^sub>R v) = 0"
    by blast
  then have *: "finite s" "affine_dependent s" and s: "s \<subseteq> c"
    unfolding affine_dependent_explicit by auto
  from Radon_partition[OF *]
  obtain m p where "m \<inter> p = {}" "m \<union> p = s" "convex hull m \<inter> convex hull p \<noteq> {}"
    by blast
  then show ?thesis
    apply (rule_tac that[of p m])
    using s
    apply auto
    done
qed


subsection \<open>Helly's theorem\<close>

lemma Helly_induct:
  fixes f :: "'a::euclidean_space set set"
  assumes "card f = n"
    and "n \<ge> DIM('a) + 1"
    and "\<forall>s\<in>f. convex s" "\<forall>t\<subseteq>f. card t = DIM('a) + 1 \<longrightarrow> \<Inter>t \<noteq> {}"
  shows "\<Inter>f \<noteq> {}"
  using assms
proof (induction n arbitrary: f)
  case 0
  then show ?case by auto
next
  case (Suc n)
  have "finite f"
    using \<open>card f = Suc n\<close> by (auto intro: card_ge_0_finite)
  show "\<Inter>f \<noteq> {}"
  proof (cases "n = DIM('a)")
    case True
    then show ?thesis
      by (simp add: Suc.prems(1) Suc.prems(4))
  next
    case False
    have "\<Inter>(f - {s}) \<noteq> {}" if "s \<in> f" for s
    proof (rule Suc.IH[rule_format])
      show "card (f - {s}) = n"
        by (simp add: Suc.prems(1) \<open>finite f\<close> that)
      show "DIM('a) + 1 \<le> n"
        using False Suc.prems(2) by linarith
      show "\<And>t. \<lbrakk>t \<subseteq> f - {s}; card t = DIM('a) + 1\<rbrakk> \<Longrightarrow> \<Inter>t \<noteq> {}"
        by (simp add: Suc.prems(4) subset_Diff_insert)
    qed (use Suc in auto)
    then have "\<forall>s\<in>f. \<exists>x. x \<in> \<Inter>(f - {s})"
      by blast
    then obtain X where X: "\<And>s. s\<in>f \<Longrightarrow> X s \<in> \<Inter>(f - {s})"
      by metis
    show ?thesis
    proof (cases "inj_on X f")
      case False
      then obtain s t where "s\<noteq>t" and st: "s\<in>f" "t\<in>f" "X s = X t"
        unfolding inj_on_def by auto
      then have *: "\<Inter>f = \<Inter>(f - {s}) \<inter> \<Inter>(f - {t})" by auto
      show ?thesis
        by (metis "*" X disjoint_iff_not_equal st)
    next
      case True
      then obtain m p where mp: "m \<inter> p = {}" "m \<union> p = X ` f" "convex hull m \<inter> convex hull p \<noteq> {}"
        using Radon_partition[of "X ` f"] and affine_dependent_biggerset[of "X ` f"]
        unfolding card_image[OF True] and \<open>card f = Suc n\<close>
        using Suc(3) \<open>finite f\<close> and False
        by auto
      have "m \<subseteq> X ` f" "p \<subseteq> X ` f"
        using mp(2) by auto
      then obtain g h where gh:"m = X ` g" "p = X ` h" "g \<subseteq> f" "h \<subseteq> f"
        unfolding subset_image_iff by auto
      then have "f \<union> (g \<union> h) = f" by auto
      then have f: "f = g \<union> h"
        using inj_on_Un_image_eq_iff[of X f "g \<union> h"] and True
        unfolding mp(2)[unfolded image_Un[symmetric] gh]
        by auto
      have *: "g \<inter> h = {}"
        using mp(1)
        unfolding gh
        using inj_on_image_Int[OF True gh(3,4)]
        by auto
      have "convex hull (X ` h) \<subseteq> \<Inter>g" "convex hull (X ` g) \<subseteq> \<Inter>h"
        by (rule hull_minimal; use X * f in \<open>auto simp: Suc.prems(3) convex_Inter\<close>)+
      then show ?thesis
        unfolding f using mp(3)[unfolded gh] by blast
    qed
  qed 
qed

theorem Helly:
  fixes f :: "'a::euclidean_space set set"
  assumes "card f \<ge> DIM('a) + 1" "\<forall>s\<in>f. convex s"
    and "\<And>t. \<lbrakk>t\<subseteq>f; card t = DIM('a) + 1\<rbrakk> \<Longrightarrow> \<Inter>t \<noteq> {}"
  shows "\<Inter>f \<noteq> {}"
  apply (rule Helly_induct)
  using assms
  apply auto
  done

subsection \<open>Epigraphs of convex functions\<close>

definition\<^marker>\<open>tag important\<close> "epigraph S (f :: _ \<Rightarrow> real) = {xy. fst xy \<in> S \<and> f (fst xy) \<le> snd xy}"

lemma mem_epigraph: "(x, y) \<in> epigraph S f \<longleftrightarrow> x \<in> S \<and> f x \<le> y"
  unfolding epigraph_def by auto

lemma convex_epigraph: "convex (epigraph S f) \<longleftrightarrow> convex_on S f \<and> convex S"
proof safe
  assume L: "convex (epigraph S f)"
  then show "convex_on S f"
    by (auto simp: convex_def convex_on_def epigraph_def)
  show "convex S"
    using L
    apply (clarsimp simp: convex_def convex_on_def epigraph_def)
    apply (erule_tac x=x in allE)
    apply (erule_tac x="f x" in allE, safe)
    apply (erule_tac x=y in allE)
    apply (erule_tac x="f y" in allE)
    apply (auto simp: )
    done
next
  assume "convex_on S f" "convex S"
  then show "convex (epigraph S f)"
    unfolding convex_def convex_on_def epigraph_def
    apply safe
     apply (rule_tac [2] y="u * f a + v * f aa" in order_trans)
      apply (auto intro!:mult_left_mono add_mono)
    done
qed

lemma convex_epigraphI: "convex_on S f \<Longrightarrow> convex S \<Longrightarrow> convex (epigraph S f)"
  unfolding convex_epigraph by auto

lemma convex_epigraph_convex: "convex S \<Longrightarrow> convex_on S f \<longleftrightarrow> convex(epigraph S f)"
  by (simp add: convex_epigraph)


subsubsection\<^marker>\<open>tag unimportant\<close> \<open>Use this to derive general bound property of convex function\<close>

lemma convex_on:
  assumes "convex S"
  shows "convex_on S f \<longleftrightarrow>
    (\<forall>k u x. (\<forall>i\<in>{1..k::nat}. 0 \<le> u i \<and> x i \<in> S) \<and> sum u {1..k} = 1 \<longrightarrow>
      f (sum (\<lambda>i. u i *\<^sub>R x i) {1..k}) \<le> sum (\<lambda>i. u i * f(x i)) {1..k})"

  unfolding convex_epigraph_convex[OF assms] convex epigraph_def Ball_def mem_Collect_eq
  unfolding fst_sum snd_sum fst_scaleR snd_scaleR
  apply safe
    apply (drule_tac x=k in spec)
    apply (drule_tac x=u in spec)
    apply (drule_tac x="\<lambda>i. (x i, f (x i))" in spec)
    apply simp
  using assms[unfolded convex] apply simp
  apply (rule_tac y="\<Sum>i = 1..k. u i * f (fst (x i))" in order_trans, force)
   apply (rule sum_mono)
   apply (erule_tac x=i in allE)
  unfolding real_scaleR_def
   apply (rule mult_left_mono)
  using assms[unfolded convex] apply auto
  done

subsection\<^marker>\<open>tag unimportant\<close> \<open>A bound within a convex hull\<close>

lemma convex_on_convex_hull_bound:
  assumes "convex_on (convex hull s) f"
    and "\<forall>x\<in>s. f x \<le> b"
  shows "\<forall>x\<in> convex hull s. f x \<le> b"
proof
  fix x
  assume "x \<in> convex hull s"
  then obtain k u v where
    obt: "\<forall>i\<in>{1..k::nat}. 0 \<le> u i \<and> v i \<in> s" "sum u {1..k} = 1" "(\<Sum>i = 1..k. u i *\<^sub>R v i) = x"
    unfolding convex_hull_indexed mem_Collect_eq by auto
  have "(\<Sum>i = 1..k. u i * f (v i)) \<le> b"
    using sum_mono[of "{1..k}" "\<lambda>i. u i * f (v i)" "\<lambda>i. u i * b"]
    unfolding sum_distrib_right[symmetric] obt(2) mult_1
    apply (drule_tac meta_mp)
    apply (rule mult_left_mono)
    using assms(2) obt(1)
    apply auto
    done
  then show "f x \<le> b"
    using assms(1)[unfolded convex_on[OF convex_convex_hull], rule_format, of k u v]
    unfolding obt(2-3)
    using obt(1) and hull_subset[unfolded subset_eq, rule_format, of _ s]
    by auto
qed

lemma inner_sum_Basis[simp]: "i \<in> Basis \<Longrightarrow> (\<Sum>Basis) \<bullet> i = 1"
  by (simp add: inner_sum_left sum.If_cases inner_Basis)

lemma convex_set_plus:
  assumes "convex S" and "convex T" shows "convex (S + T)"
proof -
  have "convex (\<Union>x\<in> S. \<Union>y \<in> T. {x + y})"
    using assms by (rule convex_sums)
  moreover have "(\<Union>x\<in> S. \<Union>y \<in> T. {x + y}) = S + T"
    unfolding set_plus_def by auto
  finally show "convex (S + T)" .
qed

lemma convex_set_sum:
  assumes "\<And>i. i \<in> A \<Longrightarrow> convex (B i)"
  shows "convex (\<Sum>i\<in>A. B i)"
proof (cases "finite A")
  case True then show ?thesis using assms
    by induct (auto simp: convex_set_plus)
qed auto

lemma finite_set_sum:
  assumes "finite A" and "\<forall>i\<in>A. finite (B i)" shows "finite (\<Sum>i\<in>A. B i)"
  using assms by (induct set: finite, simp, simp add: finite_set_plus)

lemma box_eq_set_sum_Basis:
  shows "{x. \<forall>i\<in>Basis. x\<bullet>i \<in> B i} = (\<Sum>i\<in>Basis. image (\<lambda>x. x *\<^sub>R i) (B i))"
  apply (subst set_sum_alt [OF finite_Basis], safe)
  apply (fast intro: euclidean_representation [symmetric])
  apply (subst inner_sum_left)
apply (rename_tac f)
  apply (subgoal_tac "(\<Sum>x\<in>Basis. f x \<bullet> i) = f i \<bullet> i")
  apply (drule (1) bspec)
  apply clarsimp
  apply (frule sum.remove [OF finite_Basis])
  apply (erule trans, simp)
  apply (rule sum.neutral, clarsimp)
  apply (frule_tac x=i in bspec, assumption)
  apply (drule_tac x=x in bspec, assumption, clarsimp)
  apply (cut_tac u=x and v=i in inner_Basis, assumption+)
  apply (rule ccontr, simp)
  done

lemma convex_hull_set_sum:
  "convex hull (\<Sum>i\<in>A. B i) = (\<Sum>i\<in>A. convex hull (B i))"
proof (cases "finite A")
  assume "finite A" then show ?thesis
    by (induct set: finite, simp, simp add: convex_hull_set_plus)
qed simp


end