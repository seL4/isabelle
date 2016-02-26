(*  Title:      HOL/Library/Convex.thy
    Author:     Armin Heller, TU Muenchen
    Author:     Johannes Hoelzl, TU Muenchen
*)

section \<open>Convexity in real vector spaces\<close>

theory Convex
imports Product_Vector
begin

subsection \<open>Convexity\<close>

definition convex :: "'a::real_vector set \<Rightarrow> bool"
  where "convex s \<longleftrightarrow> (\<forall>x\<in>s. \<forall>y\<in>s. \<forall>u\<ge>0. \<forall>v\<ge>0. u + v = 1 \<longrightarrow> u *\<^sub>R x + v *\<^sub>R y \<in> s)"

lemma convexI:
  assumes "\<And>x y u v. x \<in> s \<Longrightarrow> y \<in> s \<Longrightarrow> 0 \<le> u \<Longrightarrow> 0 \<le> v \<Longrightarrow> u + v = 1 \<Longrightarrow> u *\<^sub>R x + v *\<^sub>R y \<in> s"
  shows "convex s"
  using assms unfolding convex_def by fast

lemma convexD:
  assumes "convex s" and "x \<in> s" and "y \<in> s" and "0 \<le> u" and "0 \<le> v" and "u + v = 1"
  shows "u *\<^sub>R x + v *\<^sub>R y \<in> s"
  using assms unfolding convex_def by fast

lemma convex_alt:
  "convex s \<longleftrightarrow> (\<forall>x\<in>s. \<forall>y\<in>s. \<forall>u. 0 \<le> u \<and> u \<le> 1 \<longrightarrow> ((1 - u) *\<^sub>R x + u *\<^sub>R y) \<in> s)"
  (is "_ \<longleftrightarrow> ?alt")
proof
  assume alt[rule_format]: ?alt
  {
    fix x y and u v :: real
    assume mem: "x \<in> s" "y \<in> s"
    assume "0 \<le> u" "0 \<le> v"
    moreover
    assume "u + v = 1"
    then have "u = 1 - v" by auto
    ultimately have "u *\<^sub>R x + v *\<^sub>R y \<in> s"
      using alt[OF mem] by auto
  }
  then show "convex s"
    unfolding convex_def by auto
qed (auto simp: convex_def)

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

lemma convex_Inter: "(\<forall>s\<in>f. convex s) \<Longrightarrow> convex(\<Inter>f)"
  unfolding convex_def by auto

lemma convex_Int: "convex s \<Longrightarrow> convex t \<Longrightarrow> convex (s \<inter> t)"
  unfolding convex_def by auto

lemma convex_INT: "\<forall>i\<in>A. convex (B i) \<Longrightarrow> convex (\<Inter>i\<in>A. B i)"
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


subsection \<open>Explicit expressions for convexity in terms of arbitrary sums\<close>

lemma convex_setsum:
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
  have "a i + setsum a s = 1"
    and "0 \<le> a i"
    and "\<forall>j\<in>s. 0 \<le> a j"
    and "y i \<in> C"
    and "\<forall>j\<in>s. y j \<in> C"
    using insert.hyps(1,2) insert.prems by simp_all
  then have "0 \<le> setsum a s"
    by (simp add: setsum_nonneg)
  have "a i *\<^sub>R y i + (\<Sum>j\<in>s. a j *\<^sub>R y j) \<in> C"
  proof (cases)
    assume z: "setsum a s = 0"
    with \<open>a i + setsum a s = 1\<close> have "a i = 1"
      by simp
    from setsum_nonneg_0 [OF \<open>finite s\<close> _ z] \<open>\<forall>j\<in>s. 0 \<le> a j\<close> have "\<forall>j\<in>s. a j = 0"
      by simp
    show ?thesis using \<open>a i = 1\<close> and \<open>\<forall>j\<in>s. a j = 0\<close> and \<open>y i \<in> C\<close>
      by simp
  next
    assume nz: "setsum a s \<noteq> 0"
    with \<open>0 \<le> setsum a s\<close> have "0 < setsum a s"
      by simp
    then have "(\<Sum>j\<in>s. (a j / setsum a s) *\<^sub>R y j) \<in> C"
      using \<open>\<forall>j\<in>s. 0 \<le> a j\<close> and \<open>\<forall>j\<in>s. y j \<in> C\<close>
      by (simp add: IH setsum_divide_distrib [symmetric])
    from \<open>convex C\<close> and \<open>y i \<in> C\<close> and this and \<open>0 \<le> a i\<close>
      and \<open>0 \<le> setsum a s\<close> and \<open>a i + setsum a s = 1\<close>
    have "a i *\<^sub>R y i + setsum a s *\<^sub>R (\<Sum>j\<in>s. (a j / setsum a s) *\<^sub>R y j) \<in> C"
      by (rule convexD)
    then show ?thesis
      by (simp add: scaleR_setsum_right nz)
  qed
  then show ?case using \<open>finite s\<close> and \<open>i \<notin> s\<close>
    by simp
qed

lemma convex:
  "convex s \<longleftrightarrow> (\<forall>(k::nat) u x. (\<forall>i. 1\<le>i \<and> i\<le>k \<longrightarrow> 0 \<le> u i \<and> x i \<in>s) \<and> (setsum u {1..k} = 1)
      \<longrightarrow> setsum (\<lambda>i. u i *\<^sub>R x i) {1..k} \<in> s)"
proof safe
  fix k :: nat
  fix u :: "nat \<Rightarrow> real"
  fix x
  assume "convex s"
    "\<forall>i. 1 \<le> i \<and> i \<le> k \<longrightarrow> 0 \<le> u i \<and> x i \<in> s"
    "setsum u {1..k} = 1"
  with convex_setsum[of "{1 .. k}" s] show "(\<Sum>j\<in>{1 .. k}. u j *\<^sub>R x j) \<in> s"
    by auto
next
  assume *: "\<forall>k u x. (\<forall> i :: nat. 1 \<le> i \<and> i \<le> k \<longrightarrow> 0 \<le> u i \<and> x i \<in> s) \<and> setsum u {1..k} = 1
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
    then have "setsum ?u {1 .. 2} = 1"
      using setsum.If_cases[of "{(1 :: nat) .. 2}" "\<lambda> x. x = 1" "\<lambda> x. \<mu>" "\<lambda> x. 1 - \<mu>"]
      by auto
    with *[rule_format, of "2" ?u ?x] have s: "(\<Sum>j \<in> {1..2}. ?u j *\<^sub>R ?x j) \<in> s"
      using mu xy by auto
    have grarr: "(\<Sum>j \<in> {Suc (Suc 0)..2}. ?u j *\<^sub>R ?x j) = (1 - \<mu>) *\<^sub>R y"
      using setsum_head_Suc[of "Suc (Suc 0)" 2 "\<lambda> j. (1 - \<mu>) *\<^sub>R y"] by auto
    from setsum_head_Suc[of "Suc 0" 2 "\<lambda> j. ?u j *\<^sub>R ?x j", simplified this]
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
    (\<forall>t u. finite t \<and> t \<subseteq> s \<and> (\<forall>x\<in>t. 0 \<le> u x) \<and> setsum u t = 1 \<longrightarrow> setsum (\<lambda>x. u x *\<^sub>R x) t \<in> s)"
proof safe
  fix t
  fix u :: "'a \<Rightarrow> real"
  assume "convex s"
    and "finite t"
    and "t \<subseteq> s" "\<forall>x\<in>t. 0 \<le> u x" "setsum u t = 1"
  then show "(\<Sum>x\<in>t. u x *\<^sub>R x) \<in> s"
    using convex_setsum[of t s u "\<lambda> x. x"] by auto
next
  assume *: "\<forall>t. \<forall> u. finite t \<and> t \<subseteq> s \<and> (\<forall>x\<in>t. 0 \<le> u x) \<and>
    setsum u t = 1 \<longrightarrow> (\<Sum>x\<in>t. u x *\<^sub>R x) \<in> s"
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
  shows "convex s \<longleftrightarrow> (\<forall>u. (\<forall>x\<in>s. 0 \<le> u x) \<and> setsum u s = 1 \<longrightarrow> setsum (\<lambda>x. u x *\<^sub>R x) s \<in> s)"
  unfolding convex_explicit
proof safe
  fix t u
  assume sum: "\<forall>u. (\<forall>x\<in>s. 0 \<le> u x) \<and> setsum u s = 1 \<longrightarrow> (\<Sum>x\<in>s. u x *\<^sub>R x) \<in> s"
    and as: "finite t" "t \<subseteq> s" "\<forall>x\<in>t. 0 \<le> u x" "setsum u t = (1::real)"
  have *: "s \<inter> t = t"
    using as(2) by auto
  have if_distrib_arg: "\<And>P f g x. (if P then f else g) x = (if P then f x else g x)"
    by simp
  show "(\<Sum>x\<in>t. u x *\<^sub>R x) \<in> s"
   using sum[THEN spec[where x="\<lambda>x. if x\<in>t then u x else 0"]] as *
   by (auto simp: assms setsum.If_cases if_distrib if_distrib_arg)
qed (erule_tac x=s in allE, erule_tac x=u in allE, auto)


subsection \<open>Functions that are convex on a set\<close>

definition convex_on :: "'a::real_vector set \<Rightarrow> ('a \<Rightarrow> real) \<Rightarrow> bool"
  where "convex_on s f \<longleftrightarrow>
    (\<forall>x\<in>s. \<forall>y\<in>s. \<forall>u\<ge>0. \<forall>v\<ge>0. u + v = 1 \<longrightarrow> f (u *\<^sub>R x + v *\<^sub>R y) \<le> u * f x + v * f y)"

lemma convex_onI [intro?]:
  assumes "\<And>t x y. t > 0 \<Longrightarrow> t < 1 \<Longrightarrow> x \<in> A \<Longrightarrow> y \<in> A \<Longrightarrow>
             f ((1 - t) *\<^sub>R x + t *\<^sub>R y) \<le> (1 - t) * f x + t * f y"
  shows   "convex_on A f"
  unfolding convex_on_def
proof clarify
  fix x y u v assume A: "x \<in> A" "y \<in> A" "(u::real) \<ge> 0" "v \<ge> 0" "u + v = 1"
  from A(5) have [simp]: "v = 1 - u" by (simp add: algebra_simps)
  from A(1-4) show "f (u *\<^sub>R x + v *\<^sub>R y) \<le> u * f x + v * f y" using assms[of u y x]
    by (cases "u = 0 \<or> u = 1") (auto simp: algebra_simps)
qed

lemma convex_on_linorderI [intro?]:
  fixes A :: "('a::{linorder,real_vector}) set"
  assumes "\<And>t x y. t > 0 \<Longrightarrow> t < 1 \<Longrightarrow> x \<in> A \<Longrightarrow> y \<in> A \<Longrightarrow> x < y \<Longrightarrow>
             f ((1 - t) *\<^sub>R x + t *\<^sub>R y) \<le> (1 - t) * f x + t * f y"
  shows   "convex_on A f"
proof
  fix t x y assume A: "x \<in> A" "y \<in> A" "(t::real) > 0" "t < 1"
  with assms[of t x y] assms[of "1 - t" y x]
  show "f ((1 - t) *\<^sub>R x + t *\<^sub>R y) \<le> (1 - t) * f x + t * f y"
    by (cases x y rule: linorder_cases) (auto simp: algebra_simps)
qed

lemma convex_onD:
  assumes "convex_on A f"
  shows   "\<And>t x y. t \<ge> 0 \<Longrightarrow> t \<le> 1 \<Longrightarrow> x \<in> A \<Longrightarrow> y \<in> A \<Longrightarrow>
             f ((1 - t) *\<^sub>R x + t *\<^sub>R y) \<le> (1 - t) * f x + t * f y"
  using assms unfolding convex_on_def by auto

lemma convex_onD_Icc:
  assumes "convex_on {x..y} f" "x \<le> (y :: _ :: {real_vector,preorder})"
  shows   "\<And>t. t \<ge> 0 \<Longrightarrow> t \<le> 1 \<Longrightarrow>
             f ((1 - t) *\<^sub>R x + t *\<^sub>R y) \<le> (1 - t) * f x + t * f y"
  using assms(2) by (intro convex_onD[OF assms(1)]) simp_all

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
  have *: "\<And>u c fx v fy :: real. u * (c * fx) + v * (c * fy) = c * (u * fx + v * fy)"
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


subsection \<open>Arithmetic operations on sets preserve convexity\<close>

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
  assumes "convex s"
  shows "convex ((\<lambda>x. x *\<^sub>R c) ` s)"
proof -
  have "linear (\<lambda>x. x *\<^sub>R c)"
    by (simp add: linearI scaleR_add_left)
  then show ?thesis
    using \<open>convex s\<close> by (rule convex_linear_image)
qed

lemma convex_negations:
  assumes "convex s"
  shows "convex ((\<lambda>x. - x) ` s)"
proof -
  have "linear (\<lambda>x. - x)"
    by (simp add: linearI)
  then show ?thesis
    using \<open>convex s\<close> by (rule convex_linear_image)
qed

lemma convex_sums:
  assumes "convex s"
    and "convex t"
  shows "convex {x + y| x y. x \<in> s \<and> y \<in> t}"
proof -
  have "linear (\<lambda>(x, y). x + y)"
    by (auto intro: linearI simp: scaleR_add_right)
  with assms have "convex ((\<lambda>(x, y). x + y) ` (s \<times> t))"
    by (intro convex_linear_image convex_Times)
  also have "((\<lambda>(x, y). x + y) ` (s \<times> t)) = {x + y| x y. x \<in> s \<and> y \<in> t}"
    by auto
  finally show ?thesis .
qed

lemma convex_differences:
  assumes "convex s" "convex t"
  shows "convex {x - y| x y. x \<in> s \<and> y \<in> t}"
proof -
  have "{x - y| x y. x \<in> s \<and> y \<in> t} = {x + y |x y. x \<in> s \<and> y \<in> uminus ` t}"
    by (auto simp: diff_conv_add_uminus simp del: add_uminus_conv_diff)
  then show ?thesis
    using convex_sums[OF assms(1) convex_negations[OF assms(2)]] by auto
qed

lemma convex_translation:
  assumes "convex s"
  shows "convex ((\<lambda>x. a + x) ` s)"
proof -
  have "{a + y |y. y \<in> s} = (\<lambda>x. a + x) ` s"
    by auto
  then show ?thesis
    using convex_sums[OF convex_singleton[of a] assms] by auto
qed

lemma convex_affinity:
  assumes "convex s"
  shows "convex ((\<lambda>x. a + c *\<^sub>R x) ` s)"
proof -
  have "(\<lambda>x. a + c *\<^sub>R x) ` s = op + a ` op *\<^sub>R c ` s"
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
    then have "\<mu> *\<^sub>R x + (1 - \<mu>) *\<^sub>R y = y" by simp
    then have "\<mu> *\<^sub>R x + (1 - \<mu>) *\<^sub>R y > 0" using * by simp
  }
  moreover
  {
    assume "\<mu> = 1"
    then have "\<mu> *\<^sub>R x + (1 - \<mu>) *\<^sub>R y > 0" using * by simp
  }
  moreover
  {
    assume "\<mu> \<noteq> 1" "\<mu> \<noteq> 0"
    then have "\<mu> > 0" "(1 - \<mu>) > 0" using * by auto
    then have "\<mu> *\<^sub>R x + (1 - \<mu>) *\<^sub>R y > 0" using *
      by (auto simp: add_pos_pos)
  }
  ultimately show "(1 - \<mu>) *\<^sub>R y + \<mu> *\<^sub>R x > 0"
    using assms by fastforce
qed

lemma convex_on_setsum:
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
  then have ai: "a i = 1" by auto
  then show ?case by auto
next
  case (insert i s)
  then have "convex_on C f" by simp
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
      using insert by (fastforce simp: setsum_nonneg_eq_0_iff)
    then show ?thesis
      using insert by auto
  next
    case False
    from insert have yai: "y i \<in> C" "a i \<ge> 0"
      by auto
    have fis: "finite (insert i s)"
      using insert by auto
    then have ai1: "a i \<le> 1"
      using setsum_nonneg_leq_bound[of "insert i s" a] insert by simp
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
      using setsum.insert insert by fastforce
    then have "(\<Sum> j \<in> s. a j) / (1 - a i) = 1"
      using i0 by auto
    then have a1: "(\<Sum> j \<in> s. ?a j) = 1"
      unfolding setsum_divide_distrib by simp
    have "convex C" using insert by auto
    then have asum: "(\<Sum> j \<in> s. ?a j *\<^sub>R y j) \<in> C"
      using insert convex_setsum[OF \<open>finite s\<close>
        \<open>convex C\<close> a1 a_nonneg] by auto
    have asum_le: "f (\<Sum> j \<in> s. ?a j *\<^sub>R y j) \<le> (\<Sum> j \<in> s. ?a j * f (y j))"
      using a_nonneg a1 insert by blast
    have "f (\<Sum> j \<in> insert i s. a j *\<^sub>R y j) = f ((\<Sum> j \<in> s. a j *\<^sub>R y j) + a i *\<^sub>R y i)"
      using setsum.insert[of s i "\<lambda> j. a j *\<^sub>R y j", OF \<open>finite s\<close> \<open>i \<notin> s\<close>] insert
      by (auto simp only: add.commute)
    also have "\<dots> = f (((1 - a i) * inverse (1 - a i)) *\<^sub>R (\<Sum> j \<in> s. a j *\<^sub>R y j) + a i *\<^sub>R y i)"
      using i0 by auto
    also have "\<dots> = f ((1 - a i) *\<^sub>R (\<Sum> j \<in> s. (a j * inverse (1 - a i)) *\<^sub>R y j) + a i *\<^sub>R y i)"
      using scaleR_right.setsum[of "inverse (1 - a i)" "\<lambda> j. a j *\<^sub>R y j" s, symmetric]
      by (auto simp: algebra_simps)
    also have "\<dots> = f ((1 - a i) *\<^sub>R (\<Sum> j \<in> s. ?a j *\<^sub>R y j) + a i *\<^sub>R y i)"
      by (auto simp: divide_inverse)
    also have "\<dots> \<le> (1 - a i) *\<^sub>R f ((\<Sum> j \<in> s. ?a j *\<^sub>R y j)) + a i * f (y i)"
      using conv[of "y i" "(\<Sum> j \<in> s. ?a j *\<^sub>R y j)" "a i", OF yai(1) asum yai(2) ai1]
      by (auto simp: add.commute)
    also have "\<dots> \<le> (1 - a i) * (\<Sum> j \<in> s. ?a j * f (y j)) + a i * f (y i)"
      using add_right_mono[OF mult_left_mono[of _ _ "1 - a i",
        OF asum_le less_imp_le[OF i0]], of "a i * f (y i)"] by simp
    also have "\<dots> = (\<Sum> j \<in> s. (1 - a i) * ?a j * f (y j)) + a i * f (y i)"
      unfolding setsum_right_distrib[of "1 - a i" "\<lambda> j. ?a j * f (y j)"] using i0 by auto
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
  have "\<And>u v. 0 \<le> u \<Longrightarrow> 0 \<le> v \<Longrightarrow> u + v = 1 \<Longrightarrow> f (u *\<^sub>R x + v *\<^sub>R y) \<le> u * f x + v * f y"
    by auto
  from this[of "\<mu>" "1 - \<mu>", simplified] *
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
  def a \<equiv> "(t - y) / (x - y)"
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
    using add_mono[OF mult_left_mono[OF leq[OF xpos *(2)] \<open>\<mu> \<ge> 0\<close>]
      mult_left_mono[OF leq[OF xpos *(3)] \<open>1 - \<mu> \<ge> 0\<close>]]
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
      using assms unfolding add_divide_distrib by (auto simp: field_simps)
    also have "\<dots> = z"
      using assms by (auto simp: field_simps)
    finally show ?thesis
      using comb by auto
  qed
  show "z \<in> C" using z less assms
    unfolding atLeastAtMost_iff le_less by auto
qed

lemma f''_imp_f':
  fixes f :: "real \<Rightarrow> real"
  assumes "convex C"
    and f': "\<And>x. x \<in> C \<Longrightarrow> DERIV f x :> (f' x)"
    and f'': "\<And>x. x \<in> C \<Longrightarrow> DERIV f' x :> (f'' x)"
    and pos: "\<And>x. x \<in> C \<Longrightarrow> f'' x \<ge> 0"
    and "x \<in> C" "y \<in> C"
  shows "f' x * (y - x) \<le> f y - f x"
  using assms
proof -
  {
    fix x y :: real
    assume *: "x \<in> C" "y \<in> C" "y > x"
    then have ge: "y - x > 0" "y - x \<ge> 0"
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
    then have "f y - f x \<ge> f' x * (y - x)" "f' y * (x - y) \<le> f x - f y"
      using res by auto
  } note less_imp = this
  {
    fix x y :: real
    assume "x \<in> C" "y \<in> C" "x \<noteq> y"
    then have"f y - f x \<ge> f' x * (y - x)"
    unfolding neq_iff using less_imp by auto
  }
  moreover
  {
    fix x y :: real
    assume "x \<in> C" "y \<in> C" "x = y"
    then have "f y - f x \<ge> f' x * (y - x)" by auto
  }
  ultimately show ?thesis using assms by blast
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
  have "\<And>z :: real. z > 0 \<Longrightarrow> DERIV inverse z :> - (inverse z ^ Suc (Suc 0))"
    using less_imp_neq[THEN not_sym, THEN DERIV_inverse] by auto
  from this[THEN DERIV_cmult, of _ "- 1 / ln b"]
  have "\<And>z :: real. z > 0 \<Longrightarrow>
    DERIV (\<lambda> z. (- 1 / ln b) * inverse z) z :> (- 1 / ln b) * (- (inverse z ^ Suc (Suc 0)))"
    by auto
  then have f''0: "\<And>z::real. z > 0 \<Longrightarrow>
    DERIV (\<lambda> z. - 1 / (ln b * z)) z :> 1 / (ln b * z * z)"
    unfolding inverse_eq_divide by (auto simp: mult.assoc)
  have f''_ge0: "\<And>z::real. z > 0 \<Longrightarrow> 1 / (ln b * z * z) \<ge> 0"
    using \<open>b > 1\<close> by (auto intro!: less_imp_le)
  from f''_ge0_imp_convex[OF pos_is_convex,
    unfolded greaterThan_iff, OF f' f''0 f''_ge0]
  show ?thesis by auto
qed


subsection \<open>Convexity of real functions\<close>

lemma convex_on_realI:
  assumes "connected A"
  assumes "\<And>x. x \<in> A \<Longrightarrow> (f has_real_derivative f' x) (at x)"
  assumes "\<And>x y. x \<in> A \<Longrightarrow> y \<in> A \<Longrightarrow> x \<le> y \<Longrightarrow> f' x \<le> f' y"
  shows   "convex_on A f"
proof (rule convex_on_linorderI)
  fix t x y :: real
  assume t: "t > 0" "t < 1" and xy: "x \<in> A" "y \<in> A" "x < y"
  def z \<equiv> "(1 - t) * x + t * y"
  with \<open>connected A\<close> and xy have ivl: "{x..y} \<subseteq> A" using connected_contains_Icc by blast

  from xy t have xz: "z > x" by (simp add: z_def algebra_simps)
  have "y - z = (1 - t) * (y - x)" by (simp add: z_def algebra_simps)
  also from xy t have "... > 0" by (intro mult_pos_pos) simp_all
  finally have yz: "z < y" by simp

  from assms xz yz ivl t have "\<exists>\<xi>. \<xi> > x \<and> \<xi> < z \<and> f z - f x = (z - x) * f' \<xi>"
    by (intro MVT2) (auto intro!: assms(2))
  then obtain \<xi> where \<xi>: "\<xi> > x" "\<xi> < z" "f' \<xi> = (f z - f x) / (z - x)" by auto
  from assms xz yz ivl t have "\<exists>\<eta>. \<eta> > z \<and> \<eta> < y \<and> f y - f z = (y - z) * f' \<eta>"
    by (intro MVT2) (auto intro!: assms(2))
  then obtain \<eta> where \<eta>: "\<eta> > z" "\<eta> < y" "f' \<eta> = (f y - f z) / (y - z)" by auto

  from \<eta>(3) have "(f y - f z) / (y - z) = f' \<eta>" ..
  also from \<xi> \<eta> ivl have "\<xi> \<in> A" "\<eta> \<in> A" by auto
  with \<xi> \<eta> have "f' \<eta> \<ge> f' \<xi>" by (intro assms(3)) auto
  also from \<xi>(3) have "f' \<xi> = (f z - f x) / (z - x)" .
  finally have "(f y - f z) * (z - x) \<ge> (f z - f x) * (y - z)"
    using xz yz by (simp add: field_simps)
  also have "z - x = t * (y - x)" by (simp add: z_def algebra_simps)
  also have "y - z = (1 - t) * (y - x)" by (simp add: z_def algebra_simps)
  finally have "(f y - f z) * t \<ge> (f z - f x) * (1 - t)" using xy by simp
  thus "(1 - t) * f x + t * f y \<ge> f ((1 - t) *\<^sub>R x + t *\<^sub>R y)"
    by (simp add: z_def algebra_simps)
qed

lemma convex_on_inverse:
  assumes "A \<subseteq> {0<..}"
  shows   "convex_on A (inverse :: real \<Rightarrow> real)"
proof (rule convex_on_subset[OF _ assms], intro convex_on_realI[of _ _ "\<lambda>x. -inverse (x^2)"])
  fix u v :: real assume "u \<in> {0<..}" "v \<in> {0<..}" "u \<le> v"
  with assms show "-inverse (u^2) \<le> -inverse (v^2)"
    by (intro le_imp_neg_le le_imp_inverse_le power_mono) (simp_all)
qed (insert assms, auto intro!: derivative_eq_intros simp: divide_simps power2_eq_square)

lemma convex_onD_Icc':
  assumes "convex_on {x..y} f" "c \<in> {x..y}"
  defines "d \<equiv> y - x"
  shows   "f c \<le> (f y - f x) / d * (c - x) + f x"
proof (cases y x rule: linorder_cases)
  assume less: "x < y"
  hence d: "d > 0" by (simp add: d_def)
  from assms(2) less have A: "0 \<le> (c - x) / d" "(c - x) / d \<le> 1"
    by (simp_all add: d_def divide_simps)
  have "f c = f (x + (c - x) * 1)" by simp
  also from less have "1 = ((y - x) / d)" by (simp add: d_def)
  also from d have "x + (c - x) * \<dots> = (1 - (c - x) / d) *\<^sub>R x + ((c - x) / d) *\<^sub>R y"
    by (simp add: field_simps)
  also have "f \<dots> \<le> (1 - (c - x) / d) * f x + (c - x) / d * f y" using assms less
    by (intro convex_onD_Icc) simp_all
  also from d have "\<dots> = (f y - f x) / d * (c - x) + f x" by (simp add: field_simps)
  finally show ?thesis .
qed (insert assms(2), simp_all)

lemma convex_onD_Icc'':
  assumes "convex_on {x..y} f" "c \<in> {x..y}"
  defines "d \<equiv> y - x"
  shows   "f c \<le> (f x - f y) / d * (y - c) + f y"
proof (cases y x rule: linorder_cases)
  assume less: "x < y"
  hence d: "d > 0" by (simp add: d_def)
  from assms(2) less have A: "0 \<le> (y - c) / d" "(y - c) / d \<le> 1"
    by (simp_all add: d_def divide_simps)
  have "f c = f (y - (y - c) * 1)" by simp
  also from less have "1 = ((y - x) / d)" by (simp add: d_def)
  also from d have "y - (y - c) * \<dots> = (1 - (1 - (y - c) / d)) *\<^sub>R x + (1 - (y - c) / d) *\<^sub>R y"
    by (simp add: field_simps)
  also have "f \<dots> \<le> (1 - (1 - (y - c) / d)) * f x + (1 - (y - c) / d) * f y" using assms less
    by (intro convex_onD_Icc) (simp_all add: field_simps)
  also from d have "\<dots> = (f x - f y) / d * (y - c) + f y" by (simp add: field_simps)
  finally show ?thesis .
qed (insert assms(2), simp_all)


end
