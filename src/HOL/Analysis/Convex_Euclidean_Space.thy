(* Title:      HOL/Analysis/Convex_Euclidean_Space.thy
   Author:     L C Paulson, University of Cambridge
   Author:     Robert Himmelmann, TU Muenchen
   Author:     Bogdan Grechuk, University of Edinburgh
   Author:     Armin Heller, TU Muenchen
   Author:     Johannes Hoelzl, TU Muenchen
*)

section \<open>Convex sets, functions and related things\<close>

theory Convex_Euclidean_Space
imports
  Connected
  "HOL-Library.Set_Algebras"
begin

lemma swap_continuous: (*move to Topological_Spaces?*)
  assumes "continuous_on (cbox (a,c) (b,d)) (\<lambda>(x,y). f x y)"
    shows "continuous_on (cbox (c,a) (d,b)) (\<lambda>(x, y). f y x)"
proof -
  have "(\<lambda>(x, y). f y x) = (\<lambda>(x, y). f x y) \<circ> prod.swap"
    by auto
  then show ?thesis
    apply (rule ssubst)
    apply (rule continuous_on_compose)
    apply (simp add: split_def)
    apply (rule continuous_intros | simp add: assms)+
    done
qed

lemma substdbasis_expansion_unique:
  assumes d: "d \<subseteq> Basis"
  shows "(\<Sum>i\<in>d. f i *\<^sub>R i) = (x::'a::euclidean_space) \<longleftrightarrow>
    (\<forall>i\<in>Basis. (i \<in> d \<longrightarrow> f i = x \<bullet> i) \<and> (i \<notin> d \<longrightarrow> x \<bullet> i = 0))"
proof -
  have *: "\<And>x a b P. x * (if P then a else b) = (if P then x * a else x * b)"
    by auto
  have **: "finite d"
    by (auto intro: finite_subset[OF assms])
  have ***: "\<And>i. i \<in> Basis \<Longrightarrow> (\<Sum>i\<in>d. f i *\<^sub>R i) \<bullet> i = (\<Sum>x\<in>d. if x = i then f x else 0)"
    using d
    by (auto intro!: sum.cong simp: inner_Basis inner_sum_left)
  show ?thesis
    unfolding euclidean_eq_iff[where 'a='a] by (auto simp: sum.delta[OF **] ***)
qed

lemma independent_substdbasis: "d \<subseteq> Basis \<Longrightarrow> independent d"
  by (rule independent_mono[OF independent_Basis])

lemma dim_cball:
  assumes "e > 0"
  shows "dim (cball (0 :: 'n::euclidean_space) e) = DIM('n)"
proof -
  {
    fix x :: "'n::euclidean_space"
    define y where "y = (e / norm x) *\<^sub>R x"
    then have "y \<in> cball 0 e"
      using assms by auto
    moreover have *: "x = (norm x / e) *\<^sub>R y"
      using y_def assms by simp
    moreover from * have "x = (norm x/e) *\<^sub>R y"
      by auto
    ultimately have "x \<in> span (cball 0 e)"
      using span_scale[of y "cball 0 e" "norm x/e"]
        span_superset[of "cball 0 e"]
      by (simp add: span_base)
  }
  then have "span (cball 0 e) = (UNIV :: 'n::euclidean_space set)"
    by auto
  then show ?thesis
    using dim_span[of "cball (0 :: 'n::euclidean_space) e"] by (auto simp: dim_UNIV)
qed

lemma sum_not_0: "sum f A \<noteq> 0 \<Longrightarrow> \<exists>a \<in> A. f a \<noteq> 0"
  by (rule ccontr) auto

lemma subset_translation_eq [simp]:
    fixes a :: "'a::real_vector" shows "(+) a ` s \<subseteq> (+) a ` t \<longleftrightarrow> s \<subseteq> t"
  by auto

lemma translate_inj_on:
  fixes A :: "'a::ab_group_add set"
  shows "inj_on (\<lambda>x. a + x) A"
  unfolding inj_on_def by auto

lemma translation_assoc:
  fixes a b :: "'a::ab_group_add"
  shows "(\<lambda>x. b + x) ` ((\<lambda>x. a + x) ` S) = (\<lambda>x. (a + b) + x) ` S"
  by auto

lemma translation_invert:
  fixes a :: "'a::ab_group_add"
  assumes "(\<lambda>x. a + x) ` A = (\<lambda>x. a + x) ` B"
  shows "A = B"
proof -
  have "(\<lambda>x. -a + x) ` ((\<lambda>x. a + x) ` A) = (\<lambda>x. - a + x) ` ((\<lambda>x. a + x) ` B)"
    using assms by auto
  then show ?thesis
    using translation_assoc[of "-a" a A] translation_assoc[of "-a" a B] by auto
qed

lemma translation_galois:
  fixes a :: "'a::ab_group_add"
  shows "T = ((\<lambda>x. a + x) ` S) \<longleftrightarrow> S = ((\<lambda>x. (- a) + x) ` T)"
  using translation_assoc[of "-a" a S]
  apply auto
  using translation_assoc[of a "-a" T]
  apply auto
  done

lemma translation_inverse_subset:
  assumes "((\<lambda>x. - a + x) ` V) \<le> (S :: 'n::ab_group_add set)"
  shows "V \<le> ((\<lambda>x. a + x) ` S)"
proof -
  {
    fix x
    assume "x \<in> V"
    then have "x-a \<in> S" using assms by auto
    then have "x \<in> {a + v |v. v \<in> S}"
      apply auto
      apply (rule exI[of _ "x-a"], simp)
      done
    then have "x \<in> ((\<lambda>x. a+x) ` S)" by auto
  }
  then show ?thesis by auto
qed

subsection \<open>Convexity\<close>

definition%important convex :: "'a::real_vector set \<Rightarrow> bool"
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


subsection%unimportant \<open>Explicit expressions for convexity in terms of arbitrary sums\<close>

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
      using sum_head_Suc[of "Suc (Suc 0)" 2 "\<lambda> j. (1 - \<mu>) *\<^sub>R y"] by auto
    from sum_head_Suc[of "Suc 0" 2 "\<lambda> j. ?u j *\<^sub>R ?x j", simplified this]
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

definition%important convex_on :: "'a::real_vector set \<Rightarrow> ('a \<Rightarrow> real) \<Rightarrow> bool"
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


subsection%unimportant \<open>Arithmetic operations on sets preserve convexity\<close>

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
  assumes "convex S"
  shows "convex ((\<lambda>x. a + x) ` S)"
proof -
  have "(\<Union> x\<in> {a}. \<Union>y \<in> S. {x + y}) = (\<lambda>x. a + x) ` S"
    by auto
  then show ?thesis
    using convex_sums[OF convex_singleton[of a] assms] by auto
qed

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


subsection%unimportant \<open>Convexity of real functions\<close>

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
qed (insert assms, auto intro!: derivative_eq_intros simp: divide_simps power2_eq_square)

lemma convex_onD_Icc':
  assumes "convex_on {x..y} f" "c \<in> {x..y}"
  defines "d \<equiv> y - x"
  shows "f c \<le> (f y - f x) / d * (c - x) + f x"
proof (cases x y rule: linorder_cases)
  case less
  then have d: "d > 0"
    by (simp add: d_def)
  from assms(2) less have A: "0 \<le> (c - x) / d" "(c - x) / d \<le> 1"
    by (simp_all add: d_def divide_simps)
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
    by (simp_all add: d_def divide_simps)
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

lemma convex_supp_sum:
  assumes "convex S" and 1: "supp_sum u I = 1"
      and "\<And>i. i \<in> I \<Longrightarrow> 0 \<le> u i \<and> (u i = 0 \<or> f i \<in> S)"
    shows "supp_sum (\<lambda>i. u i *\<^sub>R f i) I \<in> S"
proof -
  have fin: "finite {i \<in> I. u i \<noteq> 0}"
    using 1 sum.infinite by (force simp: supp_sum_def support_on_def)
  then have eq: "supp_sum (\<lambda>i. u i *\<^sub>R f i) I = sum (\<lambda>i. u i *\<^sub>R f i) {i \<in> I. u i \<noteq> 0}"
    by (force intro: sum.mono_neutral_left simp: supp_sum_def support_on_def)
  show ?thesis
    apply (simp add: eq)
    apply (rule convex_sum [OF fin \<open>convex S\<close>])
    using 1 assms apply (auto simp: supp_sum_def support_on_def)
    done
qed

lemma convex_translation_eq [simp]: "convex ((\<lambda>x. a + x) ` s) \<longleftrightarrow> convex s"
  by (metis convex_translation translation_galois)

lemma convex_linear_image_eq [simp]:
    fixes f :: "'a::real_vector \<Rightarrow> 'b::real_vector"
    shows "\<lbrakk>linear f; inj f\<rbrakk> \<Longrightarrow> convex (f ` s) \<longleftrightarrow> convex s"
    by (metis (no_types) convex_linear_image convex_linear_vimage inj_vimage_image_eq)

lemma closure_bounded_linear_image_subset:
  assumes f: "bounded_linear f"
  shows "f ` closure S \<subseteq> closure (f ` S)"
  using linear_continuous_on [OF f] closed_closure closure_subset
  by (rule image_closure_subset)

lemma closure_linear_image_subset:
  fixes f :: "'m::euclidean_space \<Rightarrow> 'n::real_normed_vector"
  assumes "linear f"
  shows "f ` (closure S) \<subseteq> closure (f ` S)"
  using assms unfolding linear_conv_bounded_linear
  by (rule closure_bounded_linear_image_subset)

lemma closed_injective_linear_image:
    fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
    assumes S: "closed S" and f: "linear f" "inj f"
    shows "closed (f ` S)"
proof -
  obtain g where g: "linear g" "g \<circ> f = id"
    using linear_injective_left_inverse [OF f] by blast
  then have confg: "continuous_on (range f) g"
    using linear_continuous_on linear_conv_bounded_linear by blast
  have [simp]: "g ` f ` S = S"
    using g by (simp add: image_comp)
  have cgf: "closed (g ` f ` S)"
    by (simp add: \<open>g \<circ> f = id\<close> S image_comp)
  have [simp]: "(range f \<inter> g -` S) = f ` S"
    using g unfolding o_def id_def image_def by auto metis+
  show ?thesis
  proof (rule closedin_closed_trans [of "range f"])
    show "closedin (subtopology euclidean (range f)) (f ` S)"
      using continuous_closedin_preimage [OF confg cgf] by simp
    show "closed (range f)"
      apply (rule closed_injective_image_subspace)
      using f apply (auto simp: linear_linear linear_injective_0)
      done
  qed
qed

lemma closed_injective_linear_image_eq:
    fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
    assumes f: "linear f" "inj f"
      shows "(closed(image f s) \<longleftrightarrow> closed s)"
  by (metis closed_injective_linear_image closure_eq closure_linear_image_subset closure_subset_eq f(1) f(2) inj_image_subset_iff)

lemma closure_injective_linear_image:
    fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
    shows "\<lbrakk>linear f; inj f\<rbrakk> \<Longrightarrow> f ` (closure S) = closure (f ` S)"
  apply (rule subset_antisym)
  apply (simp add: closure_linear_image_subset)
  by (simp add: closure_minimal closed_injective_linear_image closure_subset image_mono)

lemma closure_bounded_linear_image:
    fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
    shows "\<lbrakk>linear f; bounded S\<rbrakk> \<Longrightarrow> f ` (closure S) = closure (f ` S)"
  apply (rule subset_antisym, simp add: closure_linear_image_subset)
  apply (rule closure_minimal, simp add: closure_subset image_mono)
  by (meson bounded_closure closed_closure compact_continuous_image compact_eq_bounded_closed linear_continuous_on linear_conv_bounded_linear)

lemma closure_scaleR:
  fixes S :: "'a::real_normed_vector set"
  shows "((*\<^sub>R) c) ` (closure S) = closure (((*\<^sub>R) c) ` S)"
proof
  show "((*\<^sub>R) c) ` (closure S) \<subseteq> closure (((*\<^sub>R) c) ` S)"
    using bounded_linear_scaleR_right
    by (rule closure_bounded_linear_image_subset)
  show "closure (((*\<^sub>R) c) ` S) \<subseteq> ((*\<^sub>R) c) ` (closure S)"
    by (intro closure_minimal image_mono closure_subset closed_scaling closed_closure)
qed

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

lemma sphere_eq_empty [simp]:
  fixes a :: "'a::{real_normed_vector, perfect_space}"
  shows "sphere a r = {} \<longleftrightarrow> r < 0"
by (auto simp: sphere_def dist_norm) (metis dist_norm le_less_linear vector_choose_dist)

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

definition%important affine :: "'a::real_vector set \<Rightarrow> bool"
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


subsubsection%unimportant \<open>Some explicit formulations (from Lars Schewe)\<close>

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
          by (simp add: Suc.prems sum_diff1_ring \<open>x \<in> S\<close>)
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


subsubsection%unimportant \<open>Stepping theorems and hence small special cases\<close>

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


subsubsection%unimportant \<open>Some relations between affine hull and subspaces\<close>

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


subsubsection%unimportant \<open>Parallel affine sets\<close>

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
  unfolding affine_parallel_def
  using affine_parallel_expl_aux[of S _ T] by auto

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
    unfolding affine_parallel_def by auto
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
  fixes a :: "'a::real_vector"
  shows "affine S \<longleftrightarrow> affine ((\<lambda>x. a + x) ` S)"
proof -
  have "affine S \<Longrightarrow> affine ((\<lambda>x. a + x) ` S)"
    using affine_translation_aux[of "-a" "((\<lambda>x. a + x) ` S)"]
    using translation_assoc[of "-a" a S] by auto
  then show ?thesis using affine_translation_aux by auto
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


subsubsection%unimportant \<open>Subspace parallel to an affine set\<close>

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
    using  affine_translation assms by auto
  moreover have "0 \<in> ((\<lambda>x. (-a)+x) ` S)"
    using assms exI[of "(\<lambda>x. x\<in>S \<and> -a+x = 0)" a] by auto
  ultimately show ?thesis using subspace_affine by auto
qed

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

definition%important cone :: "'a::real_vector set \<Rightarrow> bool"
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
      ultimately have "((*\<^sub>R) c) ` S = S" by auto
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

lemma cone_closure:
  fixes S :: "'a::real_normed_vector set"
  assumes "cone S"
  shows "cone (closure S)"
proof (cases "S = {}")
  case True
  then show ?thesis by auto
next
  case False
  then have "0 \<in> S \<and> (\<forall>c. c > 0 \<longrightarrow> (*\<^sub>R) c ` S = S)"
    using cone_iff[of S] assms by auto
  then have "0 \<in> closure S \<and> (\<forall>c. c > 0 \<longrightarrow> (*\<^sub>R) c ` closure S = closure S)"
    using closure_subset by (auto simp: closure_scaleR)
  then show ?thesis
    using False cone_iff[of "closure S"] by auto
qed


subsection \<open>Affine dependence and consequential theorems (from Lars Schewe)\<close>

definition%important affine_dependent :: "'a::real_vector set \<Rightarrow> bool"
  where "affine_dependent s \<longleftrightarrow> (\<exists>x\<in>s. x \<in> affine hull (s - {x}))"

lemma affine_dependent_subset:
   "\<lbrakk>affine_dependent s; s \<subseteq> t\<rbrakk> \<Longrightarrow> affine_dependent t"
apply (simp add: affine_dependent_def Bex_def)
apply (blast dest: hull_mono [OF Diff_mono [OF _ subset_refl]])
done

lemma affine_independent_subset:
  shows "\<lbrakk>~ affine_dependent t; s \<subseteq> t\<rbrakk> \<Longrightarrow> ~ affine_dependent s"
by (metis affine_dependent_subset)

lemma affine_independent_Diff:
   "~ affine_dependent s \<Longrightarrow> ~ affine_dependent(s - t)"
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


subsection%unimportant \<open>Connectedness of convex sets\<close>

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

corollary component_complement_connected:
  fixes S :: "'a::real_normed_vector set"
  assumes "connected S" "C \<in> components (-S)"
  shows "connected(-C)"
  using component_diff_connected [of S UNIV] assms
  by (auto simp: Compl_eq_Diff_UNIV)

proposition clopen:
  fixes S :: "'a :: real_normed_vector set"
  shows "closed S \<and> open S \<longleftrightarrow> S = {} \<or> S = UNIV"
    by (force intro!: connected_UNIV [unfolded connected_clopen, rule_format])

corollary compact_open:
  fixes S :: "'a :: euclidean_space set"
  shows "compact S \<and> open S \<longleftrightarrow> S = {}"
  by (auto simp: compact_eq_bounded_closed clopen)

corollary finite_imp_not_open:
    fixes S :: "'a::{real_normed_vector, perfect_space} set"
    shows "\<lbrakk>finite S; open S\<rbrakk> \<Longrightarrow> S={}"
  using clopen [of S] finite_imp_closed not_bounded_UNIV by blast

corollary empty_interior_finite:
    fixes S :: "'a::{real_normed_vector, perfect_space} set"
    shows "finite S \<Longrightarrow> interior S = {}"
  by (metis interior_subset finite_subset open_interior [of S] finite_imp_not_open)

text \<open>Balls, being convex, are connected.\<close>

lemma convex_prod:
  assumes "\<And>i. i \<in> Basis \<Longrightarrow> convex {x. P i x}"
  shows "convex {x. \<forall>i\<in>Basis. P i (x\<bullet>i)}"
  using assms unfolding convex_def
  by (auto simp: inner_add_left)

lemma convex_positive_orthant: "convex {x::'a::euclidean_space. (\<forall>i\<in>Basis. 0 \<le> x\<bullet>i)}"
  by (rule convex_prod) (simp add: atLeast_def[symmetric] convex_real_interval)

lemma convex_local_global_minimum:
  fixes s :: "'a::real_normed_vector set"
  assumes "e > 0"
    and "convex_on s f"
    and "ball x e \<subseteq> s"
    and "\<forall>y\<in>ball x e. f x \<le> f y"
  shows "\<forall>y\<in>s. f x \<le> f y"
proof (rule ccontr)
  have "x \<in> s" using assms(1,3) by auto
  assume "\<not> ?thesis"
  then obtain y where "y\<in>s" and y: "f x > f y" by auto
  then have xy: "0 < dist x y"  by auto
  then obtain u where "0 < u" "u \<le> 1" and u: "u < e / dist x y"
    using field_lbound_gt_zero[of 1 "e / dist x y"] xy \<open>e>0\<close> by auto
  then have "f ((1-u) *\<^sub>R x + u *\<^sub>R y) \<le> (1-u) * f x + u * f y"
    using \<open>x\<in>s\<close> \<open>y\<in>s\<close>
    using assms(2)[unfolded convex_on_def,
      THEN bspec[where x=x], THEN bspec[where x=y], THEN spec[where x="1-u"]]
    by auto
  moreover
  have *: "x - ((1 - u) *\<^sub>R x + u *\<^sub>R y) = u *\<^sub>R (x - y)"
    by (simp add: algebra_simps)
  have "(1 - u) *\<^sub>R x + u *\<^sub>R y \<in> ball x e"
    unfolding mem_ball dist_norm
    unfolding * and norm_scaleR and abs_of_pos[OF \<open>0<u\<close>]
    unfolding dist_norm[symmetric]
    using u
    unfolding pos_less_divide_eq[OF xy]
    by auto
  then have "f x \<le> f ((1 - u) *\<^sub>R x + u *\<^sub>R y)"
    using assms(4) by auto
  ultimately show False
    using mult_strict_left_mono[OF y \<open>u>0\<close>]
    unfolding left_diff_distrib
    by auto
qed

lemma convex_ball [iff]:
  fixes x :: "'a::real_normed_vector"
  shows "convex (ball x e)"
proof (auto simp: convex_def)
  fix y z
  assume yz: "dist x y < e" "dist x z < e"
  fix u v :: real
  assume uv: "0 \<le> u" "0 \<le> v" "u + v = 1"
  have "dist x (u *\<^sub>R y + v *\<^sub>R z) \<le> u * dist x y + v * dist x z"
    using uv yz
    using convex_on_dist [of "ball x e" x, unfolded convex_on_def,
      THEN bspec[where x=y], THEN bspec[where x=z]]
    by auto
  then show "dist x (u *\<^sub>R y + v *\<^sub>R z) < e"
    using convex_bound_lt[OF yz uv] by auto
qed

lemma convex_cball [iff]:
  fixes x :: "'a::real_normed_vector"
  shows "convex (cball x e)"
proof -
  {
    fix y z
    assume yz: "dist x y \<le> e" "dist x z \<le> e"
    fix u v :: real
    assume uv: "0 \<le> u" "0 \<le> v" "u + v = 1"
    have "dist x (u *\<^sub>R y + v *\<^sub>R z) \<le> u * dist x y + v * dist x z"
      using uv yz
      using convex_on_dist [of "cball x e" x, unfolded convex_on_def,
        THEN bspec[where x=y], THEN bspec[where x=z]]
      by auto
    then have "dist x (u *\<^sub>R y + v *\<^sub>R z) \<le> e"
      using convex_bound_le[OF yz uv] by auto
  }
  then show ?thesis by (auto simp: convex_def Ball_def)
qed

lemma connected_ball [iff]:
  fixes x :: "'a::real_normed_vector"
  shows "connected (ball x e)"
  using convex_connected convex_ball by auto

lemma connected_cball [iff]:
  fixes x :: "'a::real_normed_vector"
  shows "connected (cball x e)"
  using convex_connected convex_cball by auto


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

lemma bounded_convex_hull:
  fixes s :: "'a::real_normed_vector set"
  assumes "bounded s"
  shows "bounded (convex hull s)"
proof -
  from assms obtain B where B: "\<forall>x\<in>s. norm x \<le> B"
    unfolding bounded_iff by auto
  show ?thesis
    apply (rule bounded_subset[OF bounded_cball, of _ 0 B])
    unfolding subset_hull[of convex, OF convex_cball]
    unfolding subset_eq mem_cball dist_norm using B
    apply auto
    done
qed

lemma finite_imp_bounded_convex_hull:
  fixes s :: "'a::real_normed_vector set"
  shows "finite s \<Longrightarrow> bounded (convex hull s)"
  using bounded_convex_hull finite_imp_bounded
  by auto


subsubsection%unimportant \<open>Convex hull is "preserved" by a linear function\<close>

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


subsubsection%unimportant \<open>Stepping theorems for convex hulls of finite sets\<close>

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

subsubsection%unimportant \<open>Explicit expression for convex hull\<close>

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


subsubsection%unimportant \<open>Another formulation from Lars Schewe\<close>

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
      unfolding sum_image_gen[OF fin, symmetric] using obt(2) by auto
    moreover have "(\<Sum>v\<in>y ` {1..k}. sum u {i \<in> {1..k}. y i = v} *\<^sub>R v) = x"
      using sum_image_gen[OF fin, of "\<lambda>i. u i *\<^sub>R y i" y, symmetric]
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
      unfolding sum_image_gen[OF *(1), of "\<lambda>x. u (f x) *\<^sub>R f x" f]
        and sum_image_gen[OF *(1), of "\<lambda>x. u (f x)" f]
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


subsubsection%unimportant \<open>A stepping theorem for that expansion\<close>

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


subsubsection%unimportant \<open>Hence some special cases\<close>

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


subsection%unimportant \<open>Relations among closure notions and corresponding hulls\<close>

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


subsection%unimportant \<open>Some Properties of Affine Dependent Sets\<close>

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

definition%important aff_dim :: "('a::euclidean_space) set \<Rightarrow> int"
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
    shows "~ affine_dependent s \<longleftrightarrow> finite s \<and> aff_dim s = int(card s) - 1"
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
  fixes a :: "'n::euclidean_space"
  shows "aff_dim ((\<lambda>x. a + x) ` S) = aff_dim S"
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
  fixes S :: "'n::euclidean_space set"
  assumes "a \<in> affine hull S"
  shows "aff_dim S = int (dim ((\<lambda>x. -a+x) ` S))"
proof -
  have "0 \<in> affine hull ((\<lambda>x. -a+x) ` S)"
    unfolding Convex_Euclidean_Space.affine_hull_translation
    using assms by (simp add: ab_group_add_class.ab_left_minus image_iff)
  with aff_dim_zero show ?thesis
    by (metis aff_dim_translation_eq)
qed

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
  assumes "~ affine_dependent S" "a \<in> S"
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
    have "~ {a,b} \<subseteq> S" if "b \<noteq> a" for b
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
  assumes "~ affine_dependent s" "t \<subseteq> s" "u \<subseteq> s" "t \<inter> u = {}"
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
    moreover have "~ (\<forall>v\<in>s. c v = 0)"
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

lemma aff_dim_cball:
  fixes a :: "'n::euclidean_space"
  assumes "e > 0"
  shows "aff_dim (cball a e) = int (DIM('n))"
proof -
  have "(\<lambda>x. a + x) ` (cball 0 e) \<subseteq> cball a e"
    unfolding cball_def dist_norm by auto
  then have "aff_dim (cball (0 :: 'n::euclidean_space) e) \<le> aff_dim (cball a e)"
    using aff_dim_translation_eq[of a "cball 0 e"]
          aff_dim_subset[of "(+) a ` cball 0 e" "cball a e"]
    by auto
  moreover have "aff_dim (cball (0 :: 'n::euclidean_space) e) = int (DIM('n))"
    using hull_inc[of "(0 :: 'n::euclidean_space)" "cball 0 e"]
      centre_in_cball[of "(0 :: 'n::euclidean_space)"] assms
    by (simp add: dim_cball[of e] aff_dim_zero[of "cball 0 e"])
  ultimately show ?thesis
    using aff_dim_le_DIM[of "cball a e"] by auto
qed

lemma aff_dim_open:
  fixes S :: "'n::euclidean_space set"
  assumes "open S"
    and "S \<noteq> {}"
  shows "aff_dim S = int (DIM('n))"
proof -
  obtain x where "x \<in> S"
    using assms by auto
  then obtain e where e: "e > 0" "cball x e \<subseteq> S"
    using open_contains_cball[of S] assms by auto
  then have "aff_dim (cball x e) \<le> aff_dim S"
    using aff_dim_subset by auto
  with e show ?thesis
    using aff_dim_cball[of e x] aff_dim_le_DIM[of S] by auto
qed

lemma low_dim_interior:
  fixes S :: "'n::euclidean_space set"
  assumes "\<not> aff_dim S = int (DIM('n))"
  shows "interior S = {}"
proof -
  have "aff_dim(interior S) \<le> aff_dim S"
    using interior_subset aff_dim_subset[of "interior S" S] by auto
  then show ?thesis
    using aff_dim_open[of "interior S"] aff_dim_le_DIM[of S] assms by auto
qed

corollary empty_interior_lowdim:
  fixes S :: "'n::euclidean_space set"
  shows "dim S < DIM ('n) \<Longrightarrow> interior S = {}"
by (metis low_dim_interior affine_hull_UNIV dim_affine_hull less_not_refl dim_UNIV)

corollary aff_dim_nonempty_interior:
  fixes S :: "'a::euclidean_space set"
  shows "interior S \<noteq> {} \<Longrightarrow> aff_dim S = DIM('a)"
by (metis low_dim_interior)


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


subsection \<open>Relative interior of a set\<close>

definition%important "rel_interior S =
  {x. \<exists>T. openin (subtopology euclidean (affine hull S)) T \<and> x \<in> T \<and> T \<subseteq> S}"

lemma rel_interior_mono:
   "\<lbrakk>S \<subseteq> T; affine hull S = affine hull T\<rbrakk>
   \<Longrightarrow> (rel_interior S) \<subseteq> (rel_interior T)"
  by (auto simp: rel_interior_def)

lemma rel_interior_maximal:
   "\<lbrakk>T \<subseteq> S; openin(subtopology euclidean (affine hull S)) T\<rbrakk> \<Longrightarrow> T \<subseteq> (rel_interior S)"
  by (auto simp: rel_interior_def)

lemma rel_interior:
  "rel_interior S = {x \<in> S. \<exists>T. open T \<and> x \<in> T \<and> T \<inter> affine hull S \<subseteq> S}"
  unfolding rel_interior_def[of S] openin_open[of "affine hull S"]
  apply auto
proof -
  fix x T
  assume *: "x \<in> S" "open T" "x \<in> T" "T \<inter> affine hull S \<subseteq> S"
  then have **: "x \<in> T \<inter> affine hull S"
    using hull_inc by auto
  show "\<exists>Tb. (\<exists>Ta. open Ta \<and> Tb = affine hull S \<inter> Ta) \<and> x \<in> Tb \<and> Tb \<subseteq> S"
    apply (rule_tac x = "T \<inter> (affine hull S)" in exI)
    using * **
    apply auto
    done
qed

lemma mem_rel_interior: "x \<in> rel_interior S \<longleftrightarrow> (\<exists>T. open T \<and> x \<in> T \<inter> S \<and> T \<inter> affine hull S \<subseteq> S)"
  by (auto simp: rel_interior)

lemma mem_rel_interior_ball:
  "x \<in> rel_interior S \<longleftrightarrow> x \<in> S \<and> (\<exists>e. e > 0 \<and> ball x e \<inter> affine hull S \<subseteq> S)"
  apply (simp add: rel_interior, safe)
  apply (force simp: open_contains_ball)
  apply (rule_tac x = "ball x e" in exI, simp)
  done

lemma rel_interior_ball:
  "rel_interior S = {x \<in> S. \<exists>e. e > 0 \<and> ball x e \<inter> affine hull S \<subseteq> S}"
  using mem_rel_interior_ball [of _ S] by auto

lemma mem_rel_interior_cball:
  "x \<in> rel_interior S \<longleftrightarrow> x \<in> S \<and> (\<exists>e. e > 0 \<and> cball x e \<inter> affine hull S \<subseteq> S)"
  apply (simp add: rel_interior, safe)
  apply (force simp: open_contains_cball)
  apply (rule_tac x = "ball x e" in exI)
  apply (simp add: subset_trans [OF ball_subset_cball], auto)
  done

lemma rel_interior_cball:
  "rel_interior S = {x \<in> S. \<exists>e. e > 0 \<and> cball x e \<inter> affine hull S \<subseteq> S}"
  using mem_rel_interior_cball [of _ S] by auto

lemma rel_interior_empty [simp]: "rel_interior {} = {}"
   by (auto simp: rel_interior_def)

lemma affine_hull_sing [simp]: "affine hull {a :: 'n::euclidean_space} = {a}"
  by (metis affine_hull_eq affine_sing)

lemma rel_interior_sing [simp]:
    fixes a :: "'n::euclidean_space"  shows "rel_interior {a} = {a}"
  apply (auto simp: rel_interior_ball)
  apply (rule_tac x=1 in exI, force)
  done

lemma subset_rel_interior:
  fixes S T :: "'n::euclidean_space set"
  assumes "S \<subseteq> T"
    and "affine hull S = affine hull T"
  shows "rel_interior S \<subseteq> rel_interior T"
  using assms by (auto simp: rel_interior_def)

lemma rel_interior_subset: "rel_interior S \<subseteq> S"
  by (auto simp: rel_interior_def)

lemma rel_interior_subset_closure: "rel_interior S \<subseteq> closure S"
  using rel_interior_subset by (auto simp: closure_def)

lemma interior_subset_rel_interior: "interior S \<subseteq> rel_interior S"
  by (auto simp: rel_interior interior_def)

lemma interior_rel_interior:
  fixes S :: "'n::euclidean_space set"
  assumes "aff_dim S = int(DIM('n))"
  shows "rel_interior S = interior S"
proof -
  have "affine hull S = UNIV"
    using assms affine_hull_UNIV[of S] by auto
  then show ?thesis
    unfolding rel_interior interior_def by auto
qed

lemma rel_interior_interior:
  fixes S :: "'n::euclidean_space set"
  assumes "affine hull S = UNIV"
  shows "rel_interior S = interior S"
  using assms unfolding rel_interior interior_def by auto

lemma rel_interior_open:
  fixes S :: "'n::euclidean_space set"
  assumes "open S"
  shows "rel_interior S = S"
  by (metis assms interior_eq interior_subset_rel_interior rel_interior_subset set_eq_subset)

lemma interior_ball [simp]: "interior (ball x e) = ball x e"
  by (simp add: interior_open)

lemma interior_rel_interior_gen:
  fixes S :: "'n::euclidean_space set"
  shows "interior S = (if aff_dim S = int(DIM('n)) then rel_interior S else {})"
  by (metis interior_rel_interior low_dim_interior)

lemma rel_interior_nonempty_interior:
  fixes S :: "'n::euclidean_space set"
  shows "interior S \<noteq> {} \<Longrightarrow> rel_interior S = interior S"
by (metis interior_rel_interior_gen)

lemma affine_hull_nonempty_interior:
  fixes S :: "'n::euclidean_space set"
  shows "interior S \<noteq> {} \<Longrightarrow> affine hull S = UNIV"
by (metis affine_hull_UNIV interior_rel_interior_gen)

lemma rel_interior_affine_hull [simp]:
  fixes S :: "'n::euclidean_space set"
  shows "rel_interior (affine hull S) = affine hull S"
proof -
  have *: "rel_interior (affine hull S) \<subseteq> affine hull S"
    using rel_interior_subset by auto
  {
    fix x
    assume x: "x \<in> affine hull S"
    define e :: real where "e = 1"
    then have "e > 0" "ball x e \<inter> affine hull (affine hull S) \<subseteq> affine hull S"
      using hull_hull[of _ S] by auto
    then have "x \<in> rel_interior (affine hull S)"
      using x rel_interior_ball[of "affine hull S"] by auto
  }
  then show ?thesis using * by auto
qed

lemma rel_interior_UNIV [simp]: "rel_interior (UNIV :: ('n::euclidean_space) set) = UNIV"
  by (metis open_UNIV rel_interior_open)

lemma rel_interior_convex_shrink:
  fixes S :: "'a::euclidean_space set"
  assumes "convex S"
    and "c \<in> rel_interior S"
    and "x \<in> S"
    and "0 < e"
    and "e \<le> 1"
  shows "x - e *\<^sub>R (x - c) \<in> rel_interior S"
proof -
  obtain d where "d > 0" and d: "ball c d \<inter> affine hull S \<subseteq> S"
    using assms(2) unfolding  mem_rel_interior_ball by auto
  {
    fix y
    assume as: "dist (x - e *\<^sub>R (x - c)) y < e * d" "y \<in> affine hull S"
    have *: "y = (1 - (1 - e)) *\<^sub>R ((1 / e) *\<^sub>R y - ((1 - e) / e) *\<^sub>R x) + (1 - e) *\<^sub>R x"
      using \<open>e > 0\<close> by (auto simp: scaleR_left_diff_distrib scaleR_right_diff_distrib)
    have "x \<in> affine hull S"
      using assms hull_subset[of S] by auto
    moreover have "1 / e + - ((1 - e) / e) = 1"
      using \<open>e > 0\<close> left_diff_distrib[of "1" "(1-e)" "1/e"] by auto
    ultimately have **: "(1 / e) *\<^sub>R y - ((1 - e) / e) *\<^sub>R x \<in> affine hull S"
      using as affine_affine_hull[of S] mem_affine[of "affine hull S" y x "(1 / e)" "-((1 - e) / e)"]
      by (simp add: algebra_simps)
    have "dist c ((1 / e) *\<^sub>R y - ((1 - e) / e) *\<^sub>R x) = \<bar>1/e\<bar> * norm (e *\<^sub>R c - y + (1 - e) *\<^sub>R x)"
      unfolding dist_norm norm_scaleR[symmetric]
      apply (rule arg_cong[where f=norm])
      using \<open>e > 0\<close>
      apply (auto simp: euclidean_eq_iff[where 'a='a] field_simps inner_simps)
      done
    also have "\<dots> = \<bar>1/e\<bar> * norm (x - e *\<^sub>R (x - c) - y)"
      by (auto intro!:arg_cong[where f=norm] simp add: algebra_simps)
    also have "\<dots> < d"
      using as[unfolded dist_norm] and \<open>e > 0\<close>
      by (auto simp:pos_divide_less_eq[OF \<open>e > 0\<close>] mult.commute)
    finally have "y \<in> S"
      apply (subst *)
      apply (rule assms(1)[unfolded convex_alt,rule_format])
      apply (rule d[THEN subsetD])
      unfolding mem_ball
      using assms(3-5) **
      apply auto
      done
  }
  then have "ball (x - e *\<^sub>R (x - c)) (e*d) \<inter> affine hull S \<subseteq> S"
    by auto
  moreover have "e * d > 0"
    using \<open>e > 0\<close> \<open>d > 0\<close> by simp
  moreover have c: "c \<in> S"
    using assms rel_interior_subset by auto
  moreover from c have "x - e *\<^sub>R (x - c) \<in> S"
    using convexD_alt[of S x c e]
    apply (simp add: algebra_simps)
    using assms
    apply auto
    done
  ultimately show ?thesis
    using mem_rel_interior_ball[of "x - e *\<^sub>R (x - c)" S] \<open>e > 0\<close> by auto
qed

lemma interior_real_semiline:
  fixes a :: real
  shows "interior {a..} = {a<..}"
proof -
  {
    fix y
    assume "a < y"
    then have "y \<in> interior {a..}"
      apply (simp add: mem_interior)
      apply (rule_tac x="(y-a)" in exI)
      apply (auto simp: dist_norm)
      done
  }
  moreover
  {
    fix y
    assume "y \<in> interior {a..}"
    then obtain e where e: "e > 0" "cball y e \<subseteq> {a..}"
      using mem_interior_cball[of y "{a..}"] by auto
    moreover from e have "y - e \<in> cball y e"
      by (auto simp: cball_def dist_norm)
    ultimately have "a \<le> y - e" by blast
    then have "a < y" using e by auto
  }
  ultimately show ?thesis by auto
qed

lemma continuous_ge_on_Ioo:
  assumes "continuous_on {c..d} g" "\<And>x. x \<in> {c<..<d} \<Longrightarrow> g x \<ge> a" "c < d" "x \<in> {c..d}"
  shows "g (x::real) \<ge> (a::real)"
proof-
  from assms(3) have "{c..d} = closure {c<..<d}" by (rule closure_greaterThanLessThan[symmetric])
  also from assms(2) have "{c<..<d} \<subseteq> (g -` {a..} \<inter> {c..d})" by auto
  hence "closure {c<..<d} \<subseteq> closure (g -` {a..} \<inter> {c..d})" by (rule closure_mono)
  also from assms(1) have "closed (g -` {a..} \<inter> {c..d})"
    by (auto simp: continuous_on_closed_vimage)
  hence "closure (g -` {a..} \<inter> {c..d}) = g -` {a..} \<inter> {c..d}" by simp
  finally show ?thesis using \<open>x \<in> {c..d}\<close> by auto
qed

lemma interior_real_semiline':
  fixes a :: real
  shows "interior {..a} = {..<a}"
proof -
  {
    fix y
    assume "a > y"
    then have "y \<in> interior {..a}"
      apply (simp add: mem_interior)
      apply (rule_tac x="(a-y)" in exI)
      apply (auto simp: dist_norm)
      done
  }
  moreover
  {
    fix y
    assume "y \<in> interior {..a}"
    then obtain e where e: "e > 0" "cball y e \<subseteq> {..a}"
      using mem_interior_cball[of y "{..a}"] by auto
    moreover from e have "y + e \<in> cball y e"
      by (auto simp: cball_def dist_norm)
    ultimately have "a \<ge> y + e" by auto
    then have "a > y" using e by auto
  }
  ultimately show ?thesis by auto
qed

lemma interior_atLeastAtMost_real [simp]: "interior {a..b} = {a<..<b :: real}"
proof-
  have "{a..b} = {a..} \<inter> {..b}" by auto
  also have "interior \<dots> = {a<..} \<inter> {..<b}"
    by (simp add: interior_real_semiline interior_real_semiline')
  also have "\<dots> = {a<..<b}" by auto
  finally show ?thesis .
qed

lemma interior_atLeastLessThan [simp]:
  fixes a::real shows "interior {a..<b} = {a<..<b}"
  by (metis atLeastLessThan_def greaterThanLessThan_def interior_atLeastAtMost_real interior_Int interior_interior interior_real_semiline)

lemma interior_lessThanAtMost [simp]:
  fixes a::real shows "interior {a<..b} = {a<..<b}"
  by (metis atLeastAtMost_def greaterThanAtMost_def interior_atLeastAtMost_real interior_Int
            interior_interior interior_real_semiline)

lemma interior_greaterThanLessThan_real [simp]: "interior {a<..<b} = {a<..<b :: real}"
  by (metis interior_atLeastAtMost_real interior_interior)

lemma frontier_real_Iic [simp]:
  fixes a :: real
  shows "frontier {..a} = {a}"
  unfolding frontier_def by (auto simp: interior_real_semiline')

lemma rel_interior_real_box [simp]:
  fixes a b :: real
  assumes "a < b"
  shows "rel_interior {a .. b} = {a <..< b}"
proof -
  have "box a b \<noteq> {}"
    using assms
    unfolding set_eq_iff
    by (auto intro!: exI[of _ "(a + b) / 2"] simp: box_def)
  then show ?thesis
    using interior_rel_interior_gen[of "cbox a b", symmetric]
    by (simp split: if_split_asm del: box_real add: box_real[symmetric] interior_cbox)
qed

lemma rel_interior_real_semiline [simp]:
  fixes a :: real
  shows "rel_interior {a..} = {a<..}"
proof -
  have *: "{a<..} \<noteq> {}"
    unfolding set_eq_iff by (auto intro!: exI[of _ "a + 1"])
  then show ?thesis using interior_real_semiline interior_rel_interior_gen[of "{a..}"]
    by (auto split: if_split_asm)
qed

subsubsection \<open>Relative open sets\<close>

definition%important "rel_open S \<longleftrightarrow> rel_interior S = S"

lemma rel_open: "rel_open S \<longleftrightarrow> openin (subtopology euclidean (affine hull S)) S"
  unfolding rel_open_def rel_interior_def
  apply auto
  using openin_subopen[of "subtopology euclidean (affine hull S)" S]
  apply auto
  done

lemma openin_rel_interior: "openin (subtopology euclidean (affine hull S)) (rel_interior S)"
  apply (simp add: rel_interior_def)
  apply (subst openin_subopen, blast)
  done

lemma openin_set_rel_interior:
   "openin (subtopology euclidean S) (rel_interior S)"
by (rule openin_subset_trans [OF openin_rel_interior rel_interior_subset hull_subset])

lemma affine_rel_open:
  fixes S :: "'n::euclidean_space set"
  assumes "affine S"
  shows "rel_open S"
  unfolding rel_open_def
  using assms rel_interior_affine_hull[of S] affine_hull_eq[of S]
  by metis

lemma affine_closed:
  fixes S :: "'n::euclidean_space set"
  assumes "affine S"
  shows "closed S"
proof -
  {
    assume "S \<noteq> {}"
    then obtain L where L: "subspace L" "affine_parallel S L"
      using assms affine_parallel_subspace[of S] by auto
    then obtain a where a: "S = ((+) a ` L)"
      using affine_parallel_def[of L S] affine_parallel_commut by auto
    from L have "closed L" using closed_subspace by auto
    then have "closed S"
      using closed_translation a by auto
  }
  then show ?thesis by auto
qed

lemma closure_affine_hull:
  fixes S :: "'n::euclidean_space set"
  shows "closure S \<subseteq> affine hull S"
  by (intro closure_minimal hull_subset affine_closed affine_affine_hull)

lemma closure_same_affine_hull [simp]:
  fixes S :: "'n::euclidean_space set"
  shows "affine hull (closure S) = affine hull S"
proof -
  have "affine hull (closure S) \<subseteq> affine hull S"
    using hull_mono[of "closure S" "affine hull S" "affine"]
      closure_affine_hull[of S] hull_hull[of "affine" S]
    by auto
  moreover have "affine hull (closure S) \<supseteq> affine hull S"
    using hull_mono[of "S" "closure S" "affine"] closure_subset by auto
  ultimately show ?thesis by auto
qed

lemma closure_aff_dim [simp]:
  fixes S :: "'n::euclidean_space set"
  shows "aff_dim (closure S) = aff_dim S"
proof -
  have "aff_dim S \<le> aff_dim (closure S)"
    using aff_dim_subset closure_subset by auto
  moreover have "aff_dim (closure S) \<le> aff_dim (affine hull S)"
    using aff_dim_subset closure_affine_hull by blast
  moreover have "aff_dim (affine hull S) = aff_dim S"
    using aff_dim_affine_hull by auto
  ultimately show ?thesis by auto
qed

lemma rel_interior_closure_convex_shrink:
  fixes S :: "_::euclidean_space set"
  assumes "convex S"
    and "c \<in> rel_interior S"
    and "x \<in> closure S"
    and "e > 0"
    and "e \<le> 1"
  shows "x - e *\<^sub>R (x - c) \<in> rel_interior S"
proof -
  obtain d where "d > 0" and d: "ball c d \<inter> affine hull S \<subseteq> S"
    using assms(2) unfolding mem_rel_interior_ball by auto
  have "\<exists>y \<in> S. norm (y - x) * (1 - e) < e * d"
  proof (cases "x \<in> S")
    case True
    then show ?thesis using \<open>e > 0\<close> \<open>d > 0\<close>
      apply (rule_tac bexI[where x=x], auto)
      done
  next
    case False
    then have x: "x islimpt S"
      using assms(3)[unfolded closure_def] by auto
    show ?thesis
    proof (cases "e = 1")
      case True
      obtain y where "y \<in> S" "y \<noteq> x" "dist y x < 1"
        using x[unfolded islimpt_approachable,THEN spec[where x=1]] by auto
      then show ?thesis
        apply (rule_tac x=y in bexI)
        unfolding True
        using \<open>d > 0\<close>
        apply auto
        done
    next
      case False
      then have "0 < e * d / (1 - e)" and *: "1 - e > 0"
        using \<open>e \<le> 1\<close> \<open>e > 0\<close> \<open>d > 0\<close> by auto
      then obtain y where "y \<in> S" "y \<noteq> x" "dist y x < e * d / (1 - e)"
        using x[unfolded islimpt_approachable,THEN spec[where x="e*d / (1 - e)"]] by auto
      then show ?thesis
        apply (rule_tac x=y in bexI)
        unfolding dist_norm
        using pos_less_divide_eq[OF *]
        apply auto
        done
    qed
  qed
  then obtain y where "y \<in> S" and y: "norm (y - x) * (1 - e) < e * d"
    by auto
  define z where "z = c + ((1 - e) / e) *\<^sub>R (x - y)"
  have *: "x - e *\<^sub>R (x - c) = y - e *\<^sub>R (y - z)"
    unfolding z_def using \<open>e > 0\<close>
    by (auto simp: scaleR_right_diff_distrib scaleR_right_distrib scaleR_left_diff_distrib)
  have zball: "z \<in> ball c d"
    using mem_ball z_def dist_norm[of c]
    using y and assms(4,5)
    by (auto simp:field_simps norm_minus_commute)
  have "x \<in> affine hull S"
    using closure_affine_hull assms by auto
  moreover have "y \<in> affine hull S"
    using \<open>y \<in> S\<close> hull_subset[of S] by auto
  moreover have "c \<in> affine hull S"
    using assms rel_interior_subset hull_subset[of S] by auto
  ultimately have "z \<in> affine hull S"
    using z_def affine_affine_hull[of S]
      mem_affine_3_minus [of "affine hull S" c x y "(1 - e) / e"]
      assms
    by (auto simp: field_simps)
  then have "z \<in> S" using d zball by auto
  obtain d1 where "d1 > 0" and d1: "ball z d1 \<le> ball c d"
    using zball open_ball[of c d] openE[of "ball c d" z] by auto
  then have "ball z d1 \<inter> affine hull S \<subseteq> ball c d \<inter> affine hull S"
    by auto
  then have "ball z d1 \<inter> affine hull S \<subseteq> S"
    using d by auto
  then have "z \<in> rel_interior S"
    using mem_rel_interior_ball using \<open>d1 > 0\<close> \<open>z \<in> S\<close> by auto
  then have "y - e *\<^sub>R (y - z) \<in> rel_interior S"
    using rel_interior_convex_shrink[of S z y e] assms \<open>y \<in> S\<close> by auto
  then show ?thesis using * by auto
qed

lemma rel_interior_eq:
   "rel_interior s = s \<longleftrightarrow> openin(subtopology euclidean (affine hull s)) s"
using rel_open rel_open_def by blast

lemma rel_interior_openin:
   "openin(subtopology euclidean (affine hull s)) s \<Longrightarrow> rel_interior s = s"
by (simp add: rel_interior_eq)

lemma rel_interior_affine:
  fixes S :: "'n::euclidean_space set"
  shows  "affine S \<Longrightarrow> rel_interior S = S"
using affine_rel_open rel_open_def by auto

lemma rel_interior_eq_closure:
  fixes S :: "'n::euclidean_space set"
  shows "rel_interior S = closure S \<longleftrightarrow> affine S"
proof (cases "S = {}")
  case True
 then show ?thesis
    by auto
next
  case False show ?thesis
  proof
    assume eq: "rel_interior S = closure S"
    have "S = {} \<or> S = affine hull S"
      apply (rule connected_clopen [THEN iffD1, rule_format])
       apply (simp add: affine_imp_convex convex_connected)
      apply (rule conjI)
       apply (metis eq closure_subset openin_rel_interior rel_interior_subset subset_antisym)
      apply (metis closed_subset closure_subset_eq eq hull_subset rel_interior_subset)
      done
    with False have "affine hull S = S"
      by auto
    then show "affine S"
      by (metis affine_hull_eq)
  next
    assume "affine S"
    then show "rel_interior S = closure S"
      by (simp add: rel_interior_affine affine_closed)
  qed
qed


subsubsection%unimportant\<open>Relative interior preserves under linear transformations\<close>

lemma rel_interior_translation_aux:
  fixes a :: "'n::euclidean_space"
  shows "((\<lambda>x. a + x) ` rel_interior S) \<subseteq> rel_interior ((\<lambda>x. a + x) ` S)"
proof -
  {
    fix x
    assume x: "x \<in> rel_interior S"
    then obtain T where "open T" "x \<in> T \<inter> S" "T \<inter> affine hull S \<subseteq> S"
      using mem_rel_interior[of x S] by auto
    then have "open ((\<lambda>x. a + x) ` T)"
      and "a + x \<in> ((\<lambda>x. a + x) ` T) \<inter> ((\<lambda>x. a + x) ` S)"
      and "((\<lambda>x. a + x) ` T) \<inter> affine hull ((\<lambda>x. a + x) ` S) \<subseteq> (\<lambda>x. a + x) ` S"
      using affine_hull_translation[of a S] open_translation[of T a] x by auto
    then have "a + x \<in> rel_interior ((\<lambda>x. a + x) ` S)"
      using mem_rel_interior[of "a+x" "((\<lambda>x. a + x) ` S)"] by auto
  }
  then show ?thesis by auto
qed

lemma rel_interior_translation:
  fixes a :: "'n::euclidean_space"
  shows "rel_interior ((\<lambda>x. a + x) ` S) = (\<lambda>x. a + x) ` rel_interior S"
proof -
  have "(\<lambda>x. (-a) + x) ` rel_interior ((\<lambda>x. a + x) ` S) \<subseteq> rel_interior S"
    using rel_interior_translation_aux[of "-a" "(\<lambda>x. a + x) ` S"]
      translation_assoc[of "-a" "a"]
    by auto
  then have "((\<lambda>x. a + x) ` rel_interior S) \<supseteq> rel_interior ((\<lambda>x. a + x) ` S)"
    using translation_inverse_subset[of a "rel_interior ((+) a ` S)" "rel_interior S"]
    by auto
  then show ?thesis
    using rel_interior_translation_aux[of a S] by auto
qed


lemma affine_hull_linear_image:
  assumes "bounded_linear f"
  shows "f ` (affine hull s) = affine hull f ` s"
proof -
  interpret f: bounded_linear f by fact
  have "affine {x. f x \<in> affine hull f ` s}"
    unfolding affine_def
    by (auto simp: f.scaleR f.add affine_affine_hull[unfolded affine_def, rule_format])
  moreover have "affine {x. x \<in> f ` (affine hull s)}"
    using affine_affine_hull[unfolded affine_def, of s]
    unfolding affine_def by (auto simp: f.scaleR [symmetric] f.add [symmetric])
  ultimately show ?thesis
    by (auto simp: hull_inc elim!: hull_induct)
qed 


lemma rel_interior_injective_on_span_linear_image:
  fixes f :: "'m::euclidean_space \<Rightarrow> 'n::euclidean_space"
    and S :: "'m::euclidean_space set"
  assumes "bounded_linear f"
    and "inj_on f (span S)"
  shows "rel_interior (f ` S) = f ` (rel_interior S)"
proof -
  {
    fix z
    assume z: "z \<in> rel_interior (f ` S)"
    then have "z \<in> f ` S"
      using rel_interior_subset[of "f ` S"] by auto
    then obtain x where x: "x \<in> S" "f x = z" by auto
    obtain e2 where e2: "e2 > 0" "cball z e2 \<inter> affine hull (f ` S) \<subseteq> (f ` S)"
      using z rel_interior_cball[of "f ` S"] by auto
    obtain K where K: "K > 0" "\<And>x. norm (f x) \<le> norm x * K"
     using assms Real_Vector_Spaces.bounded_linear.pos_bounded[of f] by auto
    define e1 where "e1 = 1 / K"
    then have e1: "e1 > 0" "\<And>x. e1 * norm (f x) \<le> norm x"
      using K pos_le_divide_eq[of e1] by auto
    define e where "e = e1 * e2"
    then have "e > 0" using e1 e2 by auto
    {
      fix y
      assume y: "y \<in> cball x e \<inter> affine hull S"
      then have h1: "f y \<in> affine hull (f ` S)"
        using affine_hull_linear_image[of f S] assms by auto
      from y have "norm (x-y) \<le> e1 * e2"
        using cball_def[of x e] dist_norm[of x y] e_def by auto
      moreover have "f x - f y = f (x - y)"
        using assms linear_diff[of f x y] linear_conv_bounded_linear[of f] by auto
      moreover have "e1 * norm (f (x-y)) \<le> norm (x - y)"
        using e1 by auto
      ultimately have "e1 * norm ((f x)-(f y)) \<le> e1 * e2"
        by auto
      then have "f y \<in> cball z e2"
        using cball_def[of "f x" e2] dist_norm[of "f x" "f y"] e1 x by auto
      then have "f y \<in> f ` S"
        using y e2 h1 by auto
      then have "y \<in> S"
        using assms y hull_subset[of S] affine_hull_subset_span
          inj_on_image_mem_iff [OF \<open>inj_on f (span S)\<close>]
        by (metis Int_iff span_superset subsetCE)
    }
    then have "z \<in> f ` (rel_interior S)"
      using mem_rel_interior_cball[of x S] \<open>e > 0\<close> x by auto
  }
  moreover
  {
    fix x
    assume x: "x \<in> rel_interior S"
    then obtain e2 where e2: "e2 > 0" "cball x e2 \<inter> affine hull S \<subseteq> S"
      using rel_interior_cball[of S] by auto
    have "x \<in> S" using x rel_interior_subset by auto
    then have *: "f x \<in> f ` S" by auto
    have "\<forall>x\<in>span S. f x = 0 \<longrightarrow> x = 0"
      using assms subspace_span linear_conv_bounded_linear[of f]
        linear_injective_on_subspace_0[of f "span S"]
      by auto
    then obtain e1 where e1: "e1 > 0" "\<forall>x \<in> span S. e1 * norm x \<le> norm (f x)"
      using assms injective_imp_isometric[of "span S" f]
        subspace_span[of S] closed_subspace[of "span S"]
      by auto
    define e where "e = e1 * e2"
    hence "e > 0" using e1 e2 by auto
    {
      fix y
      assume y: "y \<in> cball (f x) e \<inter> affine hull (f ` S)"
      then have "y \<in> f ` (affine hull S)"
        using affine_hull_linear_image[of f S] assms by auto
      then obtain xy where xy: "xy \<in> affine hull S" "f xy = y" by auto
      with y have "norm (f x - f xy) \<le> e1 * e2"
        using cball_def[of "f x" e] dist_norm[of "f x" y] e_def by auto
      moreover have "f x - f xy = f (x - xy)"
        using assms linear_diff[of f x xy] linear_conv_bounded_linear[of f] by auto
      moreover have *: "x - xy \<in> span S"
        using subspace_diff[of "span S" x xy] subspace_span \<open>x \<in> S\<close> xy
          affine_hull_subset_span[of S] span_superset
        by auto
      moreover from * have "e1 * norm (x - xy) \<le> norm (f (x - xy))"
        using e1 by auto
      ultimately have "e1 * norm (x - xy) \<le> e1 * e2"
        by auto
      then have "xy \<in> cball x e2"
        using cball_def[of x e2] dist_norm[of x xy] e1 by auto
      then have "y \<in> f ` S"
        using xy e2 by auto
    }
    then have "f x \<in> rel_interior (f ` S)"
      using mem_rel_interior_cball[of "(f x)" "(f ` S)"] * \<open>e > 0\<close> by auto
  }
  ultimately show ?thesis by auto
qed

lemma rel_interior_injective_linear_image:
  fixes f :: "'m::euclidean_space \<Rightarrow> 'n::euclidean_space"
  assumes "bounded_linear f"
    and "inj f"
  shows "rel_interior (f ` S) = f ` (rel_interior S)"
  using assms rel_interior_injective_on_span_linear_image[of f S]
    subset_inj_on[of f "UNIV" "span S"]
  by auto


subsection%unimportant\<open>Some Properties of subset of standard basis\<close>

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


subsection%unimportant \<open>Openness and compactness are preserved by convex hull operation\<close>

lemma open_convex_hull[intro]:
  fixes S :: "'a::real_normed_vector set"
  assumes "open S"
  shows "open (convex hull S)"
proof (clarsimp simp: open_contains_cball convex_hull_explicit)
  fix T and u :: "'a\<Rightarrow>real"
  assume obt: "finite T" "T\<subseteq>S" "\<forall>x\<in>T. 0 \<le> u x" "sum u T = 1" 

  from assms[unfolded open_contains_cball] obtain b
    where b: "\<And>x. x\<in>S \<Longrightarrow> 0 < b x \<and> cball x (b x) \<subseteq> S" by metis
  have "b ` T \<noteq> {}"
    using obt by auto
  define i where "i = b ` T"
  let ?\<Phi> = "\<lambda>y. \<exists>F. finite F \<and> F \<subseteq> S \<and> (\<exists>u. (\<forall>x\<in>F. 0 \<le> u x) \<and> sum u F = 1 \<and> (\<Sum>v\<in>F. u v *\<^sub>R v) = y)"
  let ?a = "\<Sum>v\<in>T. u v *\<^sub>R v"
  show "\<exists>e > 0. cball ?a e \<subseteq> {y. ?\<Phi> y}"
  proof (intro exI subsetI conjI)
    show "0 < Min i"
      unfolding i_def and Min_gr_iff[OF finite_imageI[OF obt(1)] \<open>b ` T\<noteq>{}\<close>]
      using b \<open>T\<subseteq>S\<close> by auto
  next
    fix y
    assume "y \<in> cball ?a (Min i)"
    then have y: "norm (?a - y) \<le> Min i"
      unfolding dist_norm[symmetric] by auto
    { fix x
      assume "x \<in> T"
      then have "Min i \<le> b x"
        by (simp add: i_def obt(1))
      then have "x + (y - ?a) \<in> cball x (b x)"
        using y unfolding mem_cball dist_norm by auto
      moreover have "x \<in> S"
        using \<open>x\<in>T\<close> \<open>T\<subseteq>S\<close> by auto
      ultimately have "x + (y - ?a) \<in> S"
        using y b by blast
    }
    moreover
    have *: "inj_on (\<lambda>v. v + (y - ?a)) T"
      unfolding inj_on_def by auto
    have "(\<Sum>v\<in>(\<lambda>v. v + (y - ?a)) ` T. u (v - (y - ?a)) *\<^sub>R v) = y"
      unfolding sum.reindex[OF *] o_def using obt(4)
      by (simp add: sum.distrib sum_subtractf scaleR_left.sum[symmetric] scaleR_right_distrib)
    ultimately show "y \<in> {y. ?\<Phi> y}"
    proof (intro CollectI exI conjI)
      show "finite ((\<lambda>v. v + (y - ?a)) ` T)"
        by (simp add: obt(1))
      show "sum (\<lambda>v. u (v - (y - ?a))) ((\<lambda>v. v + (y - ?a)) ` T) = 1"
        unfolding sum.reindex[OF *] o_def using obt(4) by auto
    qed (use obt(1, 3) in auto)
  qed
qed

lemma compact_convex_combinations:
  fixes S T :: "'a::real_normed_vector set"
  assumes "compact S" "compact T"
  shows "compact { (1 - u) *\<^sub>R x + u *\<^sub>R y | x y u. 0 \<le> u \<and> u \<le> 1 \<and> x \<in> S \<and> y \<in> T}"
proof -
  let ?X = "{0..1} \<times> S \<times> T"
  let ?h = "(\<lambda>z. (1 - fst z) *\<^sub>R fst (snd z) + fst z *\<^sub>R snd (snd z))"
  have *: "{ (1 - u) *\<^sub>R x + u *\<^sub>R y | x y u. 0 \<le> u \<and> u \<le> 1 \<and> x \<in> S \<and> y \<in> T} = ?h ` ?X"
    by force
  have "continuous_on ?X (\<lambda>z. (1 - fst z) *\<^sub>R fst (snd z) + fst z *\<^sub>R snd (snd z))"
    unfolding continuous_on by (rule ballI) (intro tendsto_intros)
  with assms show ?thesis
    by (simp add: * compact_Times compact_continuous_image)
qed

lemma finite_imp_compact_convex_hull:
  fixes S :: "'a::real_normed_vector set"
  assumes "finite S"
  shows "compact (convex hull S)"
proof (cases "S = {}")
  case True
  then show ?thesis by simp
next
  case False
  with assms show ?thesis
  proof (induct rule: finite_ne_induct)
    case (singleton x)
    show ?case by simp
  next
    case (insert x A)
    let ?f = "\<lambda>(u, y::'a). u *\<^sub>R x + (1 - u) *\<^sub>R y"
    let ?T = "{0..1::real} \<times> (convex hull A)"
    have "continuous_on ?T ?f"
      unfolding split_def continuous_on by (intro ballI tendsto_intros)
    moreover have "compact ?T"
      by (intro compact_Times compact_Icc insert)
    ultimately have "compact (?f ` ?T)"
      by (rule compact_continuous_image)
    also have "?f ` ?T = convex hull (insert x A)"
      unfolding convex_hull_insert [OF \<open>A \<noteq> {}\<close>]
      apply safe
      apply (rule_tac x=a in exI, simp)
      apply (rule_tac x="1 - a" in exI, simp, fast)
      apply (rule_tac x="(u, b)" in image_eqI, simp_all)
      done
    finally show "compact (convex hull (insert x A))" .
  qed
qed

lemma compact_convex_hull:
  fixes S :: "'a::euclidean_space set"
  assumes "compact S"
  shows "compact (convex hull S)"
proof (cases "S = {}")
  case True
  then show ?thesis using compact_empty by simp
next
  case False
  then obtain w where "w \<in> S" by auto
  show ?thesis
    unfolding caratheodory[of S]
  proof (induct ("DIM('a) + 1"))
    case 0
    have *: "{x.\<exists>sa. finite sa \<and> sa \<subseteq> S \<and> card sa \<le> 0 \<and> x \<in> convex hull sa} = {}"
      using compact_empty by auto
    from 0 show ?case unfolding * by simp
  next
    case (Suc n)
    show ?case
    proof (cases "n = 0")
      case True
      have "{x. \<exists>T. finite T \<and> T \<subseteq> S \<and> card T \<le> Suc n \<and> x \<in> convex hull T} = S"
        unfolding set_eq_iff and mem_Collect_eq
      proof (rule, rule)
        fix x
        assume "\<exists>T. finite T \<and> T \<subseteq> S \<and> card T \<le> Suc n \<and> x \<in> convex hull T"
        then obtain T where T: "finite T" "T \<subseteq> S" "card T \<le> Suc n" "x \<in> convex hull T"
          by auto
        show "x \<in> S"
        proof (cases "card T = 0")
          case True
          then show ?thesis
            using T(4) unfolding card_0_eq[OF T(1)] by simp
        next
          case False
          then have "card T = Suc 0" using T(3) \<open>n=0\<close> by auto
          then obtain a where "T = {a}" unfolding card_Suc_eq by auto
          then show ?thesis using T(2,4) by simp
        qed
      next
        fix x assume "x\<in>S"
        then show "\<exists>T. finite T \<and> T \<subseteq> S \<and> card T \<le> Suc n \<and> x \<in> convex hull T"
          apply (rule_tac x="{x}" in exI)
          unfolding convex_hull_singleton
          apply auto
          done
      qed
      then show ?thesis using assms by simp
    next
      case False
      have "{x. \<exists>T. finite T \<and> T \<subseteq> S \<and> card T \<le> Suc n \<and> x \<in> convex hull T} =
        {(1 - u) *\<^sub>R x + u *\<^sub>R y | x y u.
          0 \<le> u \<and> u \<le> 1 \<and> x \<in> S \<and> y \<in> {x. \<exists>T. finite T \<and> T \<subseteq> S \<and> card T \<le> n \<and> x \<in> convex hull T}}"
        unfolding set_eq_iff and mem_Collect_eq
      proof (rule, rule)
        fix x
        assume "\<exists>u v c. x = (1 - c) *\<^sub>R u + c *\<^sub>R v \<and>
          0 \<le> c \<and> c \<le> 1 \<and> u \<in> S \<and> (\<exists>T. finite T \<and> T \<subseteq> S \<and> card T \<le> n \<and> v \<in> convex hull T)"
        then obtain u v c T where obt: "x = (1 - c) *\<^sub>R u + c *\<^sub>R v"
          "0 \<le> c \<and> c \<le> 1" "u \<in> S" "finite T" "T \<subseteq> S" "card T \<le> n"  "v \<in> convex hull T"
          by auto
        moreover have "(1 - c) *\<^sub>R u + c *\<^sub>R v \<in> convex hull insert u T"
          apply (rule convexD_alt)
          using obt(2) and convex_convex_hull and hull_subset[of "insert u T" convex]
          using obt(7) and hull_mono[of T "insert u T"]
          apply auto
          done
        ultimately show "\<exists>T. finite T \<and> T \<subseteq> S \<and> card T \<le> Suc n \<and> x \<in> convex hull T"
          apply (rule_tac x="insert u T" in exI)
          apply (auto simp: card_insert_if)
          done
      next
        fix x
        assume "\<exists>T. finite T \<and> T \<subseteq> S \<and> card T \<le> Suc n \<and> x \<in> convex hull T"
        then obtain T where T: "finite T" "T \<subseteq> S" "card T \<le> Suc n" "x \<in> convex hull T"
          by auto
        show "\<exists>u v c. x = (1 - c) *\<^sub>R u + c *\<^sub>R v \<and>
          0 \<le> c \<and> c \<le> 1 \<and> u \<in> S \<and> (\<exists>T. finite T \<and> T \<subseteq> S \<and> card T \<le> n \<and> v \<in> convex hull T)"
        proof (cases "card T = Suc n")
          case False
          then have "card T \<le> n" using T(3) by auto
          then show ?thesis
            apply (rule_tac x=w in exI, rule_tac x=x in exI, rule_tac x=1 in exI)
            using \<open>w\<in>S\<close> and T
            apply (auto intro!: exI[where x=T])
            done
        next
          case True
          then obtain a u where au: "T = insert a u" "a\<notin>u"
            apply (drule_tac card_eq_SucD, auto)
            done
          show ?thesis
          proof (cases "u = {}")
            case True
            then have "x = a" using T(4)[unfolded au] by auto
            show ?thesis unfolding \<open>x = a\<close>
              apply (rule_tac x=a in exI)
              apply (rule_tac x=a in exI)
              apply (rule_tac x=1 in exI)
              using T and \<open>n \<noteq> 0\<close>
              unfolding au
              apply (auto intro!: exI[where x="{a}"])
              done
          next
            case False
            obtain ux vx b where obt: "ux\<ge>0" "vx\<ge>0" "ux + vx = 1"
              "b \<in> convex hull u" "x = ux *\<^sub>R a + vx *\<^sub>R b"
              using T(4)[unfolded au convex_hull_insert[OF False]]
              by auto
            have *: "1 - vx = ux" using obt(3) by auto
            show ?thesis
              apply (rule_tac x=a in exI)
              apply (rule_tac x=b in exI)
              apply (rule_tac x=vx in exI)
              using obt and T(1-3)
              unfolding au and * using card_insert_disjoint[OF _ au(2)]
              apply (auto intro!: exI[where x=u])
              done
          qed
        qed
      qed
      then show ?thesis
        using compact_convex_combinations[OF assms Suc] by simp
    qed
  qed
qed


subsection%unimportant \<open>Extremal points of a simplex are some vertices\<close>

lemma dist_increases_online:
  fixes a b d :: "'a::real_inner"
  assumes "d \<noteq> 0"
  shows "dist a (b + d) > dist a b \<or> dist a (b - d) > dist a b"
proof (cases "inner a d - inner b d > 0")
  case True
  then have "0 < inner d d + (inner a d * 2 - inner b d * 2)"
    apply (rule_tac add_pos_pos)
    using assms
    apply auto
    done
  then show ?thesis
    apply (rule_tac disjI2)
    unfolding dist_norm and norm_eq_sqrt_inner and real_sqrt_less_iff
    apply  (simp add: algebra_simps inner_commute)
    done
next
  case False
  then have "0 < inner d d + (inner b d * 2 - inner a d * 2)"
    apply (rule_tac add_pos_nonneg)
    using assms
    apply auto
    done
  then show ?thesis
    apply (rule_tac disjI1)
    unfolding dist_norm and norm_eq_sqrt_inner and real_sqrt_less_iff
    apply (simp add: algebra_simps inner_commute)
    done
qed

lemma norm_increases_online:
  fixes d :: "'a::real_inner"
  shows "d \<noteq> 0 \<Longrightarrow> norm (a + d) > norm a \<or> norm(a - d) > norm a"
  using dist_increases_online[of d a 0] unfolding dist_norm by auto

lemma simplex_furthest_lt:
  fixes S :: "'a::real_inner set"
  assumes "finite S"
  shows "\<forall>x \<in> convex hull S.  x \<notin> S \<longrightarrow> (\<exists>y \<in> convex hull S. norm (x - a) < norm(y - a))"
  using assms
proof induct
  fix x S
  assume as: "finite S" "x\<notin>S" "\<forall>x\<in>convex hull S. x \<notin> S \<longrightarrow> (\<exists>y\<in>convex hull S. norm (x - a) < norm (y - a))"
  show "\<forall>xa\<in>convex hull insert x S. xa \<notin> insert x S \<longrightarrow>
    (\<exists>y\<in>convex hull insert x S. norm (xa - a) < norm (y - a))"
  proof (intro impI ballI, cases "S = {}")
    case False
    fix y
    assume y: "y \<in> convex hull insert x S" "y \<notin> insert x S"
    obtain u v b where obt: "u\<ge>0" "v\<ge>0" "u + v = 1" "b \<in> convex hull S" "y = u *\<^sub>R x + v *\<^sub>R b"
      using y(1)[unfolded convex_hull_insert[OF False]] by auto
    show "\<exists>z\<in>convex hull insert x S. norm (y - a) < norm (z - a)"
    proof (cases "y \<in> convex hull S")
      case True
      then obtain z where "z \<in> convex hull S" "norm (y - a) < norm (z - a)"
        using as(3)[THEN bspec[where x=y]] and y(2) by auto
      then show ?thesis
        apply (rule_tac x=z in bexI)
        unfolding convex_hull_insert[OF False]
        apply auto
        done
    next
      case False
      show ?thesis
        using obt(3)
      proof (cases "u = 0", case_tac[!] "v = 0")
        assume "u = 0" "v \<noteq> 0"
        then have "y = b" using obt by auto
        then show ?thesis using False and obt(4) by auto
      next
        assume "u \<noteq> 0" "v = 0"
        then have "y = x" using obt by auto
        then show ?thesis using y(2) by auto
      next
        assume "u \<noteq> 0" "v \<noteq> 0"
        then obtain w where w: "w>0" "w<u" "w<v"
          using field_lbound_gt_zero[of u v] and obt(1,2) by auto
        have "x \<noteq> b"
        proof
          assume "x = b"
          then have "y = b" unfolding obt(5)
            using obt(3) by (auto simp: scaleR_left_distrib[symmetric])
          then show False using obt(4) and False by simp
        qed
        then have *: "w *\<^sub>R (x - b) \<noteq> 0" using w(1) by auto
        show ?thesis
          using dist_increases_online[OF *, of a y]
        proof (elim disjE)
          assume "dist a y < dist a (y + w *\<^sub>R (x - b))"
          then have "norm (y - a) < norm ((u + w) *\<^sub>R x + (v - w) *\<^sub>R b - a)"
            unfolding dist_commute[of a]
            unfolding dist_norm obt(5)
            by (simp add: algebra_simps)
          moreover have "(u + w) *\<^sub>R x + (v - w) *\<^sub>R b \<in> convex hull insert x S"
            unfolding convex_hull_insert[OF \<open>S\<noteq>{}\<close>]
          proof (intro CollectI conjI exI)
            show "u + w \<ge> 0" "v - w \<ge> 0"
              using obt(1) w by auto
          qed (use obt in auto)
          ultimately show ?thesis by auto
        next
          assume "dist a y < dist a (y - w *\<^sub>R (x - b))"
          then have "norm (y - a) < norm ((u - w) *\<^sub>R x + (v + w) *\<^sub>R b - a)"
            unfolding dist_commute[of a]
            unfolding dist_norm obt(5)
            by (simp add: algebra_simps)
          moreover have "(u - w) *\<^sub>R x + (v + w) *\<^sub>R b \<in> convex hull insert x S"
            unfolding convex_hull_insert[OF \<open>S\<noteq>{}\<close>]
          proof (intro CollectI conjI exI)
            show "u - w \<ge> 0" "v + w \<ge> 0"
              using obt(1) w by auto
          qed (use obt in auto)
          ultimately show ?thesis by auto
        qed
      qed auto
    qed
  qed auto
qed (auto simp: assms)

lemma simplex_furthest_le:
  fixes S :: "'a::real_inner set"
  assumes "finite S"
    and "S \<noteq> {}"
  shows "\<exists>y\<in>S. \<forall>x\<in> convex hull S. norm (x - a) \<le> norm (y - a)"
proof -
  have "convex hull S \<noteq> {}"
    using hull_subset[of S convex] and assms(2) by auto
  then obtain x where x: "x \<in> convex hull S" "\<forall>y\<in>convex hull S. norm (y - a) \<le> norm (x - a)"
    using distance_attains_sup[OF finite_imp_compact_convex_hull[OF \<open>finite S\<close>], of a]
    unfolding dist_commute[of a]
    unfolding dist_norm
    by auto
  show ?thesis
  proof (cases "x \<in> S")
    case False
    then obtain y where "y \<in> convex hull S" "norm (x - a) < norm (y - a)"
      using simplex_furthest_lt[OF assms(1), THEN bspec[where x=x]] and x(1)
      by auto
    then show ?thesis
      using x(2)[THEN bspec[where x=y]] by auto
  next
    case True
    with x show ?thesis by auto
  qed
qed

lemma simplex_furthest_le_exists:
  fixes S :: "('a::real_inner) set"
  shows "finite S \<Longrightarrow> \<forall>x\<in>(convex hull S). \<exists>y\<in>S. norm (x - a) \<le> norm (y - a)"
  using simplex_furthest_le[of S] by (cases "S = {}") auto

lemma simplex_extremal_le:
  fixes S :: "'a::real_inner set"
  assumes "finite S"
    and "S \<noteq> {}"
  shows "\<exists>u\<in>S. \<exists>v\<in>S. \<forall>x\<in>convex hull S. \<forall>y \<in> convex hull S. norm (x - y) \<le> norm (u - v)"
proof -
  have "convex hull S \<noteq> {}"
    using hull_subset[of S convex] and assms(2) by auto
  then obtain u v where obt: "u \<in> convex hull S" "v \<in> convex hull S"
    "\<forall>x\<in>convex hull S. \<forall>y\<in>convex hull S. norm (x - y) \<le> norm (u - v)"
    using compact_sup_maxdistance[OF finite_imp_compact_convex_hull[OF assms(1)]]
    by (auto simp: dist_norm)
  then show ?thesis
  proof (cases "u\<notin>S \<or> v\<notin>S", elim disjE)
    assume "u \<notin> S"
    then obtain y where "y \<in> convex hull S" "norm (u - v) < norm (y - v)"
      using simplex_furthest_lt[OF assms(1), THEN bspec[where x=u]] and obt(1)
      by auto
    then show ?thesis
      using obt(3)[THEN bspec[where x=y], THEN bspec[where x=v]] and obt(2)
      by auto
  next
    assume "v \<notin> S"
    then obtain y where "y \<in> convex hull S" "norm (v - u) < norm (y - u)"
      using simplex_furthest_lt[OF assms(1), THEN bspec[where x=v]] and obt(2)
      by auto
    then show ?thesis
      using obt(3)[THEN bspec[where x=u], THEN bspec[where x=y]] and obt(1)
      by (auto simp: norm_minus_commute)
  qed auto
qed

lemma simplex_extremal_le_exists:
  fixes S :: "'a::real_inner set"
  shows "finite S \<Longrightarrow> x \<in> convex hull S \<Longrightarrow> y \<in> convex hull S \<Longrightarrow>
    \<exists>u\<in>S. \<exists>v\<in>S. norm (x - y) \<le> norm (u - v)"
  using convex_hull_empty simplex_extremal_le[of S]
  by(cases "S = {}") auto


subsection \<open>Closest point of a convex set is unique, with a continuous projection\<close>

definition%important closest_point :: "'a::{real_inner,heine_borel} set \<Rightarrow> 'a \<Rightarrow> 'a"
  where "closest_point S a = (SOME x. x \<in> S \<and> (\<forall>y\<in>S. dist a x \<le> dist a y))"

lemma closest_point_exists:
  assumes "closed S"
    and "S \<noteq> {}"
  shows "closest_point S a \<in> S"
    and "\<forall>y\<in>S. dist a (closest_point S a) \<le> dist a y"
  unfolding closest_point_def
  apply(rule_tac[!] someI2_ex)
  apply (auto intro: distance_attains_inf[OF assms(1,2), of a])
  done

lemma closest_point_in_set: "closed S \<Longrightarrow> S \<noteq> {} \<Longrightarrow> closest_point S a \<in> S"
  by (meson closest_point_exists)

lemma closest_point_le: "closed S \<Longrightarrow> x \<in> S \<Longrightarrow> dist a (closest_point S a) \<le> dist a x"
  using closest_point_exists[of S] by auto

lemma closest_point_self:
  assumes "x \<in> S"
  shows "closest_point S x = x"
  unfolding closest_point_def
  apply (rule some1_equality, rule ex1I[of _ x])
  using assms
  apply auto
  done

lemma closest_point_refl: "closed S \<Longrightarrow> S \<noteq> {} \<Longrightarrow> closest_point S x = x \<longleftrightarrow> x \<in> S"
  using closest_point_in_set[of S x] closest_point_self[of x S]
  by auto

lemma closer_points_lemma:
  assumes "inner y z > 0"
  shows "\<exists>u>0. \<forall>v>0. v \<le> u \<longrightarrow> norm(v *\<^sub>R z - y) < norm y"
proof -
  have z: "inner z z > 0"
    unfolding inner_gt_zero_iff using assms by auto
  have "norm (v *\<^sub>R z - y) < norm y"
    if "0 < v" and "v \<le> inner y z / inner z z" for v
    unfolding norm_lt using z assms that
    by (simp add: field_simps inner_diff inner_commute mult_strict_left_mono[OF _ \<open>0<v\<close>])
  then show ?thesis
    using assms z
    by (rule_tac x = "inner y z / inner z z" in exI) auto
qed

lemma closer_point_lemma:
  assumes "inner (y - x) (z - x) > 0"
  shows "\<exists>u>0. u \<le> 1 \<and> dist (x + u *\<^sub>R (z - x)) y < dist x y"
proof -
  obtain u where "u > 0"
    and u: "\<forall>v>0. v \<le> u \<longrightarrow> norm (v *\<^sub>R (z - x) - (y - x)) < norm (y - x)"
    using closer_points_lemma[OF assms] by auto
  show ?thesis
    apply (rule_tac x="min u 1" in exI)
    using u[THEN spec[where x="min u 1"]] and \<open>u > 0\<close>
    unfolding dist_norm by (auto simp: norm_minus_commute field_simps)
qed

lemma any_closest_point_dot:
  assumes "convex S" "closed S" "x \<in> S" "y \<in> S" "\<forall>z\<in>S. dist a x \<le> dist a z"
  shows "inner (a - x) (y - x) \<le> 0"
proof (rule ccontr)
  assume "\<not> ?thesis"
  then obtain u where u: "u>0" "u\<le>1" "dist (x + u *\<^sub>R (y - x)) a < dist x a"
    using closer_point_lemma[of a x y] by auto
  let ?z = "(1 - u) *\<^sub>R x + u *\<^sub>R y"
  have "?z \<in> S"
    using convexD_alt[OF assms(1,3,4), of u] using u by auto
  then show False
    using assms(5)[THEN bspec[where x="?z"]] and u(3)
    by (auto simp: dist_commute algebra_simps)
qed

lemma any_closest_point_unique:
  fixes x :: "'a::real_inner"
  assumes "convex S" "closed S" "x \<in> S" "y \<in> S"
    "\<forall>z\<in>S. dist a x \<le> dist a z" "\<forall>z\<in>S. dist a y \<le> dist a z"
  shows "x = y"
  using any_closest_point_dot[OF assms(1-4,5)] and any_closest_point_dot[OF assms(1-2,4,3,6)]
  unfolding norm_pths(1) and norm_le_square
  by (auto simp: algebra_simps)

lemma closest_point_unique:
  assumes "convex S" "closed S" "x \<in> S" "\<forall>z\<in>S. dist a x \<le> dist a z"
  shows "x = closest_point S a"
  using any_closest_point_unique[OF assms(1-3) _ assms(4), of "closest_point S a"]
  using closest_point_exists[OF assms(2)] and assms(3) by auto

lemma closest_point_dot:
  assumes "convex S" "closed S" "x \<in> S"
  shows "inner (a - closest_point S a) (x - closest_point S a) \<le> 0"
  apply (rule any_closest_point_dot[OF assms(1,2) _ assms(3)])
  using closest_point_exists[OF assms(2)] and assms(3)
  apply auto
  done

lemma closest_point_lt:
  assumes "convex S" "closed S" "x \<in> S" "x \<noteq> closest_point S a"
  shows "dist a (closest_point S a) < dist a x"
  apply (rule ccontr)
  apply (rule_tac notE[OF assms(4)])
  apply (rule closest_point_unique[OF assms(1-3), of a])
  using closest_point_le[OF assms(2), of _ a]
  apply fastforce
  done

lemma closest_point_lipschitz:
  assumes "convex S"
    and "closed S" "S \<noteq> {}"
  shows "dist (closest_point S x) (closest_point S y) \<le> dist x y"
proof -
  have "inner (x - closest_point S x) (closest_point S y - closest_point S x) \<le> 0"
    and "inner (y - closest_point S y) (closest_point S x - closest_point S y) \<le> 0"
    apply (rule_tac[!] any_closest_point_dot[OF assms(1-2)])
    using closest_point_exists[OF assms(2-3)]
    apply auto
    done
  then show ?thesis unfolding dist_norm and norm_le
    using inner_ge_zero[of "(x - closest_point S x) - (y - closest_point S y)"]
    by (simp add: inner_add inner_diff inner_commute)
qed

lemma continuous_at_closest_point:
  assumes "convex S"
    and "closed S"
    and "S \<noteq> {}"
  shows "continuous (at x) (closest_point S)"
  unfolding continuous_at_eps_delta
  using le_less_trans[OF closest_point_lipschitz[OF assms]] by auto

lemma continuous_on_closest_point:
  assumes "convex S"
    and "closed S"
    and "S \<noteq> {}"
  shows "continuous_on t (closest_point S)"
  by (metis continuous_at_imp_continuous_on continuous_at_closest_point[OF assms])

proposition closest_point_in_rel_interior:
  assumes "closed S" "S \<noteq> {}" and x: "x \<in> affine hull S"
    shows "closest_point S x \<in> rel_interior S \<longleftrightarrow> x \<in> rel_interior S"
proof (cases "x \<in> S")
  case True
  then show ?thesis
    by (simp add: closest_point_self)
next
  case False
  then have "False" if asm: "closest_point S x \<in> rel_interior S"
  proof -
    obtain e where "e > 0" and clox: "closest_point S x \<in> S"
               and e: "cball (closest_point S x) e \<inter> affine hull S \<subseteq> S"
      using asm mem_rel_interior_cball by blast
    then have clo_notx: "closest_point S x \<noteq> x"
      using \<open>x \<notin> S\<close> by auto
    define y where "y \<equiv> closest_point S x -
                        (min 1 (e / norm(closest_point S x - x))) *\<^sub>R (closest_point S x - x)"
    have "x - y = (1 - min 1 (e / norm (closest_point S x - x))) *\<^sub>R (x - closest_point S x)"
      by (simp add: y_def algebra_simps)
    then have "norm (x - y) = abs ((1 - min 1 (e / norm (closest_point S x - x)))) * norm(x - closest_point S x)"
      by simp
    also have "\<dots> < norm(x - closest_point S x)"
      using clo_notx \<open>e > 0\<close>
      by (auto simp: mult_less_cancel_right2 divide_simps)
    finally have no_less: "norm (x - y) < norm (x - closest_point S x)" .
    have "y \<in> affine hull S"
      unfolding y_def
      by (meson affine_affine_hull clox hull_subset mem_affine_3_minus2 subsetD x)
    moreover have "dist (closest_point S x) y \<le> e"
      using \<open>e > 0\<close> by (auto simp: y_def min_mult_distrib_right)
    ultimately have "y \<in> S"
      using subsetD [OF e] by simp
    then have "dist x (closest_point S x) \<le> dist x y"
      by (simp add: closest_point_le \<open>closed S\<close>)
    with no_less show False
      by (simp add: dist_norm)
  qed
  moreover have "x \<notin> rel_interior S"
    using rel_interior_subset False by blast
  ultimately show ?thesis by blast
qed


subsubsection%unimportant \<open>Various point-to-set separating/supporting hyperplane theorems\<close>

lemma supporting_hyperplane_closed_point:
  fixes z :: "'a::{real_inner,heine_borel}"
  assumes "convex S"
    and "closed S"
    and "S \<noteq> {}"
    and "z \<notin> S"
  shows "\<exists>a b. \<exists>y\<in>S. inner a z < b \<and> inner a y = b \<and> (\<forall>x\<in>S. inner a x \<ge> b)"
proof -
  obtain y where "y \<in> S" and y: "\<forall>x\<in>S. dist z y \<le> dist z x"
    by (metis distance_attains_inf[OF assms(2-3)])
  show ?thesis
  proof (intro exI bexI conjI ballI)
    show "(y - z) \<bullet> z < (y - z) \<bullet> y"
      by (metis \<open>y \<in> S\<close> assms(4) diff_gt_0_iff_gt inner_commute inner_diff_left inner_gt_zero_iff right_minus_eq)
    show "(y - z) \<bullet> y \<le> (y - z) \<bullet> x" if "x \<in> S" for x
    proof (rule ccontr)
      have *: "\<And>u. 0 \<le> u \<and> u \<le> 1 \<longrightarrow> dist z y \<le> dist z ((1 - u) *\<^sub>R y + u *\<^sub>R x)"
        using assms(1)[unfolded convex_alt] and y and \<open>x\<in>S\<close> and \<open>y\<in>S\<close> by auto
      assume "\<not> (y - z) \<bullet> y \<le> (y - z) \<bullet> x"
      then obtain v where "v > 0" "v \<le> 1" "dist (y + v *\<^sub>R (x - y)) z < dist y z"
        using closer_point_lemma[of z y x] by (auto simp: inner_diff)
      then show False
        using *[of v] by (auto simp: dist_commute algebra_simps)
    qed
  qed (use \<open>y \<in> S\<close> in auto)
qed

lemma separating_hyperplane_closed_point:
  fixes z :: "'a::{real_inner,heine_borel}"
  assumes "convex S"
    and "closed S"
    and "z \<notin> S"
  shows "\<exists>a b. inner a z < b \<and> (\<forall>x\<in>S. inner a x > b)"
proof (cases "S = {}")
  case True
  then show ?thesis
    by (simp add: gt_ex)
next
  case False
  obtain y where "y \<in> S" and y: "\<And>x. x \<in> S \<Longrightarrow> dist z y \<le> dist z x"
    by (metis distance_attains_inf[OF assms(2) False])
  show ?thesis
  proof (intro exI conjI ballI)
    show "(y - z) \<bullet> z < inner (y - z) z + (norm (y - z))\<^sup>2 / 2"
      using \<open>y\<in>S\<close> \<open>z\<notin>S\<close> by auto
  next
    fix x
    assume "x \<in> S"
    have "False" if *: "0 < inner (z - y) (x - y)"
    proof -
      obtain u where "u > 0" "u \<le> 1" "dist (y + u *\<^sub>R (x - y)) z < dist y z"
        using * closer_point_lemma by blast
      then show False using y[of "y + u *\<^sub>R (x - y)"] convexD_alt [OF \<open>convex S\<close>]
        using \<open>x\<in>S\<close> \<open>y\<in>S\<close> by (auto simp: dist_commute algebra_simps)
    qed
    moreover have "0 < (norm (y - z))\<^sup>2"
      using \<open>y\<in>S\<close> \<open>z\<notin>S\<close> by auto
    then have "0 < inner (y - z) (y - z)"
      unfolding power2_norm_eq_inner by simp
    ultimately show "(y - z) \<bullet> z + (norm (y - z))\<^sup>2 / 2 < (y - z) \<bullet> x"
      by (force simp: field_simps power2_norm_eq_inner inner_commute inner_diff)
  qed 
qed

lemma separating_hyperplane_closed_0:
  assumes "convex (S::('a::euclidean_space) set)"
    and "closed S"
    and "0 \<notin> S"
  shows "\<exists>a b. a \<noteq> 0 \<and> 0 < b \<and> (\<forall>x\<in>S. inner a x > b)"
proof (cases "S = {}")
  case True
  have "(SOME i. i\<in>Basis) \<noteq> (0::'a)"
    by (metis Basis_zero SOME_Basis)
  then show ?thesis
    using True zero_less_one by blast
next
  case False
  then show ?thesis
    using False using separating_hyperplane_closed_point[OF assms]
    by (metis all_not_in_conv inner_zero_left inner_zero_right less_eq_real_def not_le)
qed


subsubsection%unimportant \<open>Now set-to-set for closed/compact sets\<close>

lemma separating_hyperplane_closed_compact:
  fixes S :: "'a::euclidean_space set"
  assumes "convex S"
    and "closed S"
    and "convex T"
    and "compact T"
    and "T \<noteq> {}"
    and "S \<inter> T = {}"
  shows "\<exists>a b. (\<forall>x\<in>S. inner a x < b) \<and> (\<forall>x\<in>T. inner a x > b)"
proof (cases "S = {}")
  case True
  obtain b where b: "b > 0" "\<forall>x\<in>T. norm x \<le> b"
    using compact_imp_bounded[OF assms(4)] unfolding bounded_pos by auto
  obtain z :: 'a where z: "norm z = b + 1"
    using vector_choose_size[of "b + 1"] and b(1) by auto
  then have "z \<notin> T" using b(2)[THEN bspec[where x=z]] by auto
  then obtain a b where ab: "inner a z < b" "\<forall>x\<in>T. b < inner a x"
    using separating_hyperplane_closed_point[OF assms(3) compact_imp_closed[OF assms(4)], of z]
    by auto
  then show ?thesis
    using True by auto
next
  case False
  then obtain y where "y \<in> S" by auto
  obtain a b where "0 < b" "\<forall>x \<in> (\<Union>x\<in> S. \<Union>y \<in> T. {x - y}). b < inner a x"
    using separating_hyperplane_closed_point[OF convex_differences[OF assms(1,3)], of 0]
    using closed_compact_differences[OF assms(2,4)]
    using assms(6) by auto 
  then have ab: "\<forall>x\<in>S. \<forall>y\<in>T. b + inner a y < inner a x"
    apply -
    apply rule
    apply rule
    apply (erule_tac x="x - y" in ballE)
    apply (auto simp: inner_diff)
    done
  define k where "k = (SUP x:T. a \<bullet> x)"
  show ?thesis
    apply (rule_tac x="-a" in exI)
    apply (rule_tac x="-(k + b / 2)" in exI)
    apply (intro conjI ballI)
    unfolding inner_minus_left and neg_less_iff_less
  proof -
    fix x assume "x \<in> T"
    then have "inner a x - b / 2 < k"
      unfolding k_def
    proof (subst less_cSUP_iff)
      show "T \<noteq> {}" by fact
      show "bdd_above ((\<bullet>) a ` T)"
        using ab[rule_format, of y] \<open>y \<in> S\<close>
        by (intro bdd_aboveI2[where M="inner a y - b"]) (auto simp: field_simps intro: less_imp_le)
    qed (auto intro!: bexI[of _ x] \<open>0<b\<close>)
    then show "inner a x < k + b / 2"
      by auto
  next
    fix x
    assume "x \<in> S"
    then have "k \<le> inner a x - b"
      unfolding k_def
      apply (rule_tac cSUP_least)
      using assms(5)
      using ab[THEN bspec[where x=x]]
      apply auto
      done
    then show "k + b / 2 < inner a x"
      using \<open>0 < b\<close> by auto
  qed
qed

lemma separating_hyperplane_compact_closed:
  fixes S :: "'a::euclidean_space set"
  assumes "convex S"
    and "compact S"
    and "S \<noteq> {}"
    and "convex T"
    and "closed T"
    and "S \<inter> T = {}"
  shows "\<exists>a b. (\<forall>x\<in>S. inner a x < b) \<and> (\<forall>x\<in>T. inner a x > b)"
proof -
  obtain a b where "(\<forall>x\<in>T. inner a x < b) \<and> (\<forall>x\<in>S. b < inner a x)"
    using separating_hyperplane_closed_compact[OF assms(4-5,1-2,3)] and assms(6)
    by auto
  then show ?thesis
    apply (rule_tac x="-a" in exI)
    apply (rule_tac x="-b" in exI, auto)
    done
qed


subsubsection%unimportant \<open>General case without assuming closure and getting non-strict separation\<close>

lemma separating_hyperplane_set_0:
  assumes "convex S" "(0::'a::euclidean_space) \<notin> S"
  shows "\<exists>a. a \<noteq> 0 \<and> (\<forall>x\<in>S. 0 \<le> inner a x)"
proof -
  let ?k = "\<lambda>c. {x::'a. 0 \<le> inner c x}"
  have *: "frontier (cball 0 1) \<inter> \<Inter>f \<noteq> {}" if as: "f \<subseteq> ?k ` S" "finite f" for f
  proof -
    obtain c where c: "f = ?k ` c" "c \<subseteq> S" "finite c"
      using finite_subset_image[OF as(2,1)] by auto
    then obtain a b where ab: "a \<noteq> 0" "0 < b" "\<forall>x\<in>convex hull c. b < inner a x"
      using separating_hyperplane_closed_0[OF convex_convex_hull, of c]
      using finite_imp_compact_convex_hull[OF c(3), THEN compact_imp_closed] and assms(2)
      using subset_hull[of convex, OF assms(1), symmetric, of c]
      by force
    then have "\<exists>x. norm x = 1 \<and> (\<forall>y\<in>c. 0 \<le> inner y x)"
      apply (rule_tac x = "inverse(norm a) *\<^sub>R a" in exI)
      using hull_subset[of c convex]
      unfolding subset_eq and inner_scaleR
      by (auto simp: inner_commute del: ballE elim!: ballE)
    then show "frontier (cball 0 1) \<inter> \<Inter>f \<noteq> {}"
      unfolding c(1) frontier_cball sphere_def dist_norm by auto
  qed
  have "frontier (cball 0 1) \<inter> (\<Inter>(?k ` S)) \<noteq> {}"
    apply (rule compact_imp_fip)
    apply (rule compact_frontier[OF compact_cball])
    using * closed_halfspace_ge
    by auto
  then obtain x where "norm x = 1" "\<forall>y\<in>S. x\<in>?k y"
    unfolding frontier_cball dist_norm sphere_def by auto
  then show ?thesis
    by (metis inner_commute mem_Collect_eq norm_eq_zero zero_neq_one)
qed

lemma separating_hyperplane_sets:
  fixes S T :: "'a::euclidean_space set"
  assumes "convex S"
    and "convex T"
    and "S \<noteq> {}"
    and "T \<noteq> {}"
    and "S \<inter> T = {}"
  shows "\<exists>a b. a \<noteq> 0 \<and> (\<forall>x\<in>S. inner a x \<le> b) \<and> (\<forall>x\<in>T. inner a x \<ge> b)"
proof -
  from separating_hyperplane_set_0[OF convex_differences[OF assms(2,1)]]
  obtain a where "a \<noteq> 0" "\<forall>x\<in>{x - y |x y. x \<in> T \<and> y \<in> S}. 0 \<le> inner a x"
    using assms(3-5) by force
  then have *: "\<And>x y. x \<in> T \<Longrightarrow> y \<in> S \<Longrightarrow> inner a y \<le> inner a x"
    by (force simp: inner_diff)
  then have bdd: "bdd_above (((\<bullet>) a)`S)"
    using \<open>T \<noteq> {}\<close> by (auto intro: bdd_aboveI2[OF *])
  show ?thesis
    using \<open>a\<noteq>0\<close>
    by (intro exI[of _ a] exI[of _ "SUP x:S. a \<bullet> x"])
       (auto intro!: cSUP_upper bdd cSUP_least \<open>a \<noteq> 0\<close> \<open>S \<noteq> {}\<close> *)
qed


subsection%unimportant \<open>More convexity generalities\<close>

lemma convex_closure [intro,simp]:
  fixes S :: "'a::real_normed_vector set"
  assumes "convex S"
  shows "convex (closure S)"
  apply (rule convexI)
  apply (unfold closure_sequential, elim exE)
  apply (rule_tac x="\<lambda>n. u *\<^sub>R xa n + v *\<^sub>R xb n" in exI)
  apply (rule,rule)
  apply (rule convexD [OF assms])
  apply (auto del: tendsto_const intro!: tendsto_intros)
  done

lemma convex_interior [intro,simp]:
  fixes S :: "'a::real_normed_vector set"
  assumes "convex S"
  shows "convex (interior S)"
  unfolding convex_alt Ball_def mem_interior
proof clarify
  fix x y u
  assume u: "0 \<le> u" "u \<le> (1::real)"
  fix e d
  assume ed: "ball x e \<subseteq> S" "ball y d \<subseteq> S" "0<d" "0<e"
  show "\<exists>e>0. ball ((1 - u) *\<^sub>R x + u *\<^sub>R y) e \<subseteq> S"
  proof (intro exI conjI subsetI)
    fix z
    assume "z \<in> ball ((1 - u) *\<^sub>R x + u *\<^sub>R y) (min d e)"
    then have "(1- u) *\<^sub>R (z - u *\<^sub>R (y - x)) + u *\<^sub>R (z + (1 - u) *\<^sub>R (y - x)) \<in> S"
      apply (rule_tac assms[unfolded convex_alt, rule_format])
      using ed(1,2) and u
      unfolding subset_eq mem_ball Ball_def dist_norm
      apply (auto simp: algebra_simps)
      done
    then show "z \<in> S"
      using u by (auto simp: algebra_simps)
  qed(insert u ed(3-4), auto)
qed

lemma convex_hull_eq_empty[simp]: "convex hull S = {} \<longleftrightarrow> S = {}"
  using hull_subset[of S convex] convex_hull_empty by auto


subsection%unimportant \<open>Moving and scaling convex hulls\<close>

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


subsection%unimportant \<open>Convexity of cone hulls\<close>

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

subsection%unimportant \<open>Convex set as intersection of halfspaces\<close>

lemma convex_halfspace_intersection:
  fixes s :: "('a::euclidean_space) set"
  assumes "closed s" "convex s"
  shows "s = \<Inter>{h. s \<subseteq> h \<and> (\<exists>a b. h = {x. inner a x \<le> b})}"
  apply (rule set_eqI, rule)
  unfolding Inter_iff Ball_def mem_Collect_eq
  apply (rule,rule,erule conjE)
proof -
  fix x
  assume "\<forall>xa. s \<subseteq> xa \<and> (\<exists>a b. xa = {x. inner a x \<le> b}) \<longrightarrow> x \<in> xa"
  then have "\<forall>a b. s \<subseteq> {x. inner a x \<le> b} \<longrightarrow> x \<in> {x. inner a x \<le> b}"
    by blast
  then show "x \<in> s"
    apply (rule_tac ccontr)
    apply (drule separating_hyperplane_closed_point[OF assms(2,1)])
    apply (erule exE)+
    apply (erule_tac x="-a" in allE)
    apply (erule_tac x="-b" in allE, auto)
    done
qed auto


subsection \<open>Radon's theorem (from Lars Schewe)\<close>

lemma radon_ex_lemma:
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

lemma radon_s_lemma:
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

lemma radon_v_lemma:
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

lemma radon_partition:
  assumes "finite c" "affine_dependent c"
  shows "\<exists>m p. m \<inter> p = {} \<and> m \<union> p = c \<and> (convex hull m) \<inter> (convex hull p) \<noteq> {}"
proof -
  obtain u v where uv: "sum u c = 0" "v\<in>c" "u v \<noteq> 0"  "(\<Sum>v\<in>c. u v *\<^sub>R v) = 0"
    using radon_ex_lemma[OF assms] by auto
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

theorem radon:
  assumes "affine_dependent c"
  obtains m p where "m \<subseteq> c" "p \<subseteq> c" "m \<inter> p = {}" "(convex hull m) \<inter> (convex hull p) \<noteq> {}"
proof -
  from assms[unfolded affine_dependent_explicit]
  obtain s u where
      "finite s" "s \<subseteq> c" "sum u s = 0" "\<exists>v\<in>s. u v \<noteq> 0" "(\<Sum>v\<in>s. u v *\<^sub>R v) = 0"
    by blast
  then have *: "finite s" "affine_dependent s" and s: "s \<subseteq> c"
    unfolding affine_dependent_explicit by auto
  from radon_partition[OF *]
  obtain m p where "m \<inter> p = {}" "m \<union> p = s" "convex hull m \<inter> convex hull p \<noteq> {}"
    by blast
  then show ?thesis
    apply (rule_tac that[of p m])
    using s
    apply auto
    done
qed


subsection \<open>Helly's theorem\<close>

lemma helly_induct:
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
        using radon_partition[of "X ` f"] and affine_dependent_biggerset[of "X ` f"]
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

theorem helly:
  fixes f :: "'a::euclidean_space set set"
  assumes "card f \<ge> DIM('a) + 1" "\<forall>s\<in>f. convex s"
    and "\<And>t. \<lbrakk>t\<subseteq>f; card t = DIM('a) + 1\<rbrakk> \<Longrightarrow> \<Inter>t \<noteq> {}"
  shows "\<Inter>f \<noteq> {}"
  apply (rule helly_induct)
  using assms
  apply auto
  done


subsection \<open>Epigraphs of convex functions\<close>

definition%important "epigraph S (f :: _ \<Rightarrow> real) = {xy. fst xy \<in> S \<and> f (fst xy) \<le> snd xy}"

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


subsubsection%unimportant \<open>Use this to derive general bound property of convex function\<close>

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


subsection%unimportant \<open>Convexity of general and special intervals\<close>

lemma is_interval_convex:
  fixes S :: "'a::euclidean_space set"
  assumes "is_interval S"
  shows "convex S"
proof (rule convexI)
  fix x y and u v :: real
  assume as: "x \<in> S" "y \<in> S" "0 \<le> u" "0 \<le> v" "u + v = 1"
  then have *: "u = 1 - v" "1 - v \<ge> 0" and **: "v = 1 - u" "1 - u \<ge> 0"
    by auto
  {
    fix a b
    assume "\<not> b \<le> u * a + v * b"
    then have "u * a < (1 - v) * b"
      unfolding not_le using as(4) by (auto simp: field_simps)
    then have "a < b"
      unfolding * using as(4) *(2)
      apply (rule_tac mult_left_less_imp_less[of "1 - v"])
      apply (auto simp: field_simps)
      done
    then have "a \<le> u * a + v * b"
      unfolding * using as(4)
      by (auto simp: field_simps intro!:mult_right_mono)
  }
  moreover
  {
    fix a b
    assume "\<not> u * a + v * b \<le> a"
    then have "v * b > (1 - u) * a"
      unfolding not_le using as(4) by (auto simp: field_simps)
    then have "a < b"
      unfolding * using as(4)
      apply (rule_tac mult_left_less_imp_less)
      apply (auto simp: field_simps)
      done
    then have "u * a + v * b \<le> b"
      unfolding **
      using **(2) as(3)
      by (auto simp: field_simps intro!:mult_right_mono)
  }
  ultimately show "u *\<^sub>R x + v *\<^sub>R y \<in> S"
    apply -
    apply (rule assms[unfolded is_interval_def, rule_format, OF as(1,2)])
    using as(3-) DIM_positive[where 'a='a]
    apply (auto simp: inner_simps)
    done
qed

lemma is_interval_connected:
  fixes S :: "'a::euclidean_space set"
  shows "is_interval S \<Longrightarrow> connected S"
  using is_interval_convex convex_connected by auto

lemma convex_box [simp]: "convex (cbox a b)" "convex (box a (b::'a::euclidean_space))"
  apply (rule_tac[!] is_interval_convex)+
  using is_interval_box is_interval_cbox
  apply auto
  done

text\<open>A non-singleton connected set is perfect (i.e. has no isolated points). \<close>
lemma connected_imp_perfect:
  fixes a :: "'a::metric_space"
  assumes "connected S" "a \<in> S" and S: "\<And>x. S \<noteq> {x}"
  shows "a islimpt S"
proof -
  have False if "a \<in> T" "open T" "\<And>y. \<lbrakk>y \<in> S; y \<in> T\<rbrakk> \<Longrightarrow> y = a" for T
  proof -
    obtain e where "e > 0" and e: "cball a e \<subseteq> T"
      using \<open>open T\<close> \<open>a \<in> T\<close> by (auto simp: open_contains_cball)
    have "openin (subtopology euclidean S) {a}"
      unfolding openin_open using that \<open>a \<in> S\<close> by blast
    moreover have "closedin (subtopology euclidean S) {a}"
      by (simp add: assms)
    ultimately show "False"
      using \<open>connected S\<close> connected_clopen S by blast
  qed
  then show ?thesis
    unfolding islimpt_def by blast
qed

lemma connected_imp_perfect_aff_dim:
     "\<lbrakk>connected S; aff_dim S \<noteq> 0; a \<in> S\<rbrakk> \<Longrightarrow> a islimpt S"
  using aff_dim_sing connected_imp_perfect by blast

subsection%unimportant \<open>On \<open>real\<close>, \<open>is_interval\<close>, \<open>convex\<close> and \<open>connected\<close> are all equivalent\<close>

lemma mem_is_interval_1_I:
  fixes a b c::real
  assumes "is_interval S"
  assumes "a \<in> S" "c \<in> S"
  assumes "a \<le> b" "b \<le> c"
  shows "b \<in> S"
  using assms is_interval_1 by blast

lemma is_interval_connected_1:
  fixes s :: "real set"
  shows "is_interval s \<longleftrightarrow> connected s"
  apply rule
  apply (rule is_interval_connected, assumption)
  unfolding is_interval_1
  apply rule
  apply rule
  apply rule
  apply rule
  apply (erule conjE)
  apply (rule ccontr)       
proof -
  fix a b x
  assume as: "connected s" "a \<in> s" "b \<in> s" "a \<le> x" "x \<le> b" "x \<notin> s"
  then have *: "a < x" "x < b"
    unfolding not_le [symmetric] by auto
  let ?halfl = "{..<x} "
  let ?halfr = "{x<..}"
  {
    fix y
    assume "y \<in> s"
    with \<open>x \<notin> s\<close> have "x \<noteq> y" by auto
    then have "y \<in> ?halfr \<union> ?halfl" by auto
  }
  moreover have "a \<in> ?halfl" "b \<in> ?halfr" using * by auto
  then have "?halfl \<inter> s \<noteq> {}" "?halfr \<inter> s \<noteq> {}"
    using as(2-3) by auto
  ultimately show False
    apply (rule_tac notE[OF as(1)[unfolded connected_def]])
    apply (rule_tac x = ?halfl in exI)
    apply (rule_tac x = ?halfr in exI, rule)
    apply (rule open_lessThan, rule)
    apply (rule open_greaterThan, auto)
    done
qed

lemma is_interval_convex_1:
  fixes s :: "real set"
  shows "is_interval s \<longleftrightarrow> convex s"
  by (metis is_interval_convex convex_connected is_interval_connected_1)

lemma is_interval_ball_real: "is_interval (ball a b)" for a b::real
  by (metis connected_ball is_interval_connected_1)

lemma connected_compact_interval_1:
     "connected S \<and> compact S \<longleftrightarrow> (\<exists>a b. S = {a..b::real})"
  by (auto simp: is_interval_connected_1 [symmetric] is_interval_compact)

lemma connected_convex_1:
  fixes s :: "real set"
  shows "connected s \<longleftrightarrow> convex s"
  by (metis is_interval_convex convex_connected is_interval_connected_1)

lemma connected_convex_1_gen:
  fixes s :: "'a :: euclidean_space set"
  assumes "DIM('a) = 1"
  shows "connected s \<longleftrightarrow> convex s"
proof -
  obtain f:: "'a \<Rightarrow> real" where linf: "linear f" and "inj f"
    using subspace_isomorphism[OF subspace_UNIV subspace_UNIV,
        where 'a='a and 'b=real]
    unfolding Euclidean_Space.dim_UNIV
    by (auto simp: assms)
  then have "f -` (f ` s) = s"
    by (simp add: inj_vimage_image_eq)
  then show ?thesis
    by (metis connected_convex_1 convex_linear_vimage linf convex_connected connected_linear_image)
qed

lemma is_interval_cball_1[intro, simp]: "is_interval (cball a b)" for a b::real
  by (simp add: is_interval_convex_1)


subsection%unimportant \<open>Another intermediate value theorem formulation\<close>

lemma ivt_increasing_component_on_1:
  fixes f :: "real \<Rightarrow> 'a::euclidean_space"
  assumes "a \<le> b"
    and "continuous_on {a..b} f"
    and "(f a)\<bullet>k \<le> y" "y \<le> (f b)\<bullet>k"
  shows "\<exists>x\<in>{a..b}. (f x)\<bullet>k = y"
proof -
  have "f a \<in> f ` cbox a b" "f b \<in> f ` cbox a b"
    apply (rule_tac[!] imageI)
    using assms(1)
    apply auto
    done
  then show ?thesis
    using connected_ivt_component[of "f ` cbox a b" "f a" "f b" k y]
    by (simp add: connected_continuous_image assms)
qed

lemma ivt_increasing_component_1:
  fixes f :: "real \<Rightarrow> 'a::euclidean_space"
  shows "a \<le> b \<Longrightarrow> \<forall>x\<in>{a..b}. continuous (at x) f \<Longrightarrow>
    f a\<bullet>k \<le> y \<Longrightarrow> y \<le> f b\<bullet>k \<Longrightarrow> \<exists>x\<in>{a..b}. (f x)\<bullet>k = y"
  by (rule ivt_increasing_component_on_1) (auto simp: continuous_at_imp_continuous_on)

lemma ivt_decreasing_component_on_1:
  fixes f :: "real \<Rightarrow> 'a::euclidean_space"
  assumes "a \<le> b"
    and "continuous_on {a..b} f"
    and "(f b)\<bullet>k \<le> y"
    and "y \<le> (f a)\<bullet>k"
  shows "\<exists>x\<in>{a..b}. (f x)\<bullet>k = y"
  apply (subst neg_equal_iff_equal[symmetric])
  using ivt_increasing_component_on_1[of a b "\<lambda>x. - f x" k "- y"]
  using assms using continuous_on_minus
  apply auto
  done

lemma ivt_decreasing_component_1:
  fixes f :: "real \<Rightarrow> 'a::euclidean_space"
  shows "a \<le> b \<Longrightarrow> \<forall>x\<in>{a..b}. continuous (at x) f \<Longrightarrow>
    f b\<bullet>k \<le> y \<Longrightarrow> y \<le> f a\<bullet>k \<Longrightarrow> \<exists>x\<in>{a..b}. (f x)\<bullet>k = y"
  by (rule ivt_decreasing_component_on_1) (auto simp: continuous_at_imp_continuous_on)


subsection%unimportant \<open>A bound within a convex hull, and so an interval\<close>

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

lemma convex_hull_eq_real_cbox:
  fixes x y :: real assumes "x \<le> y"
  shows "convex hull {x, y} = cbox x y"
proof (rule hull_unique)
  show "{x, y} \<subseteq> cbox x y" using \<open>x \<le> y\<close> by auto
  show "convex (cbox x y)"
    by (rule convex_box)
next
  fix S assume "{x, y} \<subseteq> S" and "convex S"
  then show "cbox x y \<subseteq> S"
    unfolding is_interval_convex_1 [symmetric] is_interval_def Basis_real_def
    by - (clarify, simp (no_asm_use), fast)
qed

lemma unit_interval_convex_hull:
  "cbox (0::'a::euclidean_space) One = convex hull {x. \<forall>i\<in>Basis. (x\<bullet>i = 0) \<or> (x\<bullet>i = 1)}"
  (is "?int = convex hull ?points")
proof -
  have One[simp]: "\<And>i. i \<in> Basis \<Longrightarrow> One \<bullet> i = 1"
    by (simp add: inner_sum_left sum.If_cases inner_Basis)
  have "?int = {x. \<forall>i\<in>Basis. x \<bullet> i \<in> cbox 0 1}"
    by (auto simp: cbox_def)
  also have "\<dots> = (\<Sum>i\<in>Basis. (\<lambda>x. x *\<^sub>R i) ` cbox 0 1)"
    by (simp only: box_eq_set_sum_Basis)
  also have "\<dots> = (\<Sum>i\<in>Basis. (\<lambda>x. x *\<^sub>R i) ` (convex hull {0, 1}))"
    by (simp only: convex_hull_eq_real_cbox zero_le_one)
  also have "\<dots> = (\<Sum>i\<in>Basis. convex hull ((\<lambda>x. x *\<^sub>R i) ` {0, 1}))"
    by (simp add: convex_hull_linear_image)
  also have "\<dots> = convex hull (\<Sum>i\<in>Basis. (\<lambda>x. x *\<^sub>R i) ` {0, 1})"
    by (simp only: convex_hull_set_sum)
  also have "\<dots> = convex hull {x. \<forall>i\<in>Basis. x\<bullet>i \<in> {0, 1}}"
    by (simp only: box_eq_set_sum_Basis)
  also have "convex hull {x. \<forall>i\<in>Basis. x\<bullet>i \<in> {0, 1}} = convex hull ?points"
    by simp
  finally show ?thesis .
qed

text \<open>And this is a finite set of vertices.\<close>

lemma unit_cube_convex_hull:
  obtains S :: "'a::euclidean_space set"
  where "finite S" and "cbox 0 (\<Sum>Basis) = convex hull S"
proof
  show "finite {x::'a. \<forall>i\<in>Basis. x \<bullet> i = 0 \<or> x \<bullet> i = 1}"
  proof (rule finite_subset, clarify)
    show "finite ((\<lambda>S. \<Sum>i\<in>Basis. (if i \<in> S then 1 else 0) *\<^sub>R i) ` Pow Basis)"
      using finite_Basis by blast
    fix x :: 'a
    assume as: "\<forall>i\<in>Basis. x \<bullet> i = 0 \<or> x \<bullet> i = 1"
    show "x \<in> (\<lambda>S. \<Sum>i\<in>Basis. (if i\<in>S then 1 else 0) *\<^sub>R i) ` Pow Basis"
      apply (rule image_eqI[where x="{i. i\<in>Basis \<and> x\<bullet>i = 1}"])
      using as
       apply (subst euclidean_eq_iff, auto)
      done
  qed
  show "cbox 0 One = convex hull {x. \<forall>i\<in>Basis. x \<bullet> i = 0 \<or> x \<bullet> i = 1}"
    using unit_interval_convex_hull by blast
qed 

text \<open>Hence any cube (could do any nonempty interval).\<close>

lemma cube_convex_hull:
  assumes "d > 0"
  obtains S :: "'a::euclidean_space set" where
    "finite S" and "cbox (x - (\<Sum>i\<in>Basis. d*\<^sub>Ri)) (x + (\<Sum>i\<in>Basis. d*\<^sub>Ri)) = convex hull S"
proof -
  let ?d = "(\<Sum>i\<in>Basis. d *\<^sub>R i)::'a"
  have *: "cbox (x - ?d) (x + ?d) = (\<lambda>y. x - ?d + (2 * d) *\<^sub>R y) ` cbox 0 (\<Sum>Basis)"
  proof (intro set_eqI iffI)
    fix y
    assume "y \<in> cbox (x - ?d) (x + ?d)"
    then have "inverse (2 * d) *\<^sub>R (y - (x - ?d)) \<in> cbox 0 (\<Sum>Basis)"
      using assms by (simp add: mem_box field_simps inner_simps)
    with \<open>0 < d\<close> show "y \<in> (\<lambda>y. x - sum ((*\<^sub>R) d) Basis + (2 * d) *\<^sub>R y) ` cbox 0 One"
      by (auto intro: image_eqI[where x= "inverse (2 * d) *\<^sub>R (y - (x - ?d))"])
  next
    fix y
    assume "y \<in> (\<lambda>y. x - ?d + (2 * d) *\<^sub>R y) ` cbox 0 One"
    then obtain z where z: "z \<in> cbox 0 One" "y = x - ?d + (2*d) *\<^sub>R z"
      by auto
    then show "y \<in> cbox (x - ?d) (x + ?d)"
      using z assms by (auto simp: mem_box inner_simps)
  qed
  obtain S where "finite S" "cbox 0 (\<Sum>Basis::'a) = convex hull S"
    using unit_cube_convex_hull by auto
  then show ?thesis
    by (rule_tac that[of "(\<lambda>y. x - ?d + (2 * d) *\<^sub>R y)` S"]) (auto simp: convex_hull_affinity *)
qed

subsection%unimportant\<open>Representation of any interval as a finite convex hull\<close>

lemma image_stretch_interval:
  "(\<lambda>x. \<Sum>k\<in>Basis. (m k * (x\<bullet>k)) *\<^sub>R k) ` cbox a (b::'a::euclidean_space) =
  (if (cbox a b) = {} then {} else
    cbox (\<Sum>k\<in>Basis. (min (m k * (a\<bullet>k)) (m k * (b\<bullet>k))) *\<^sub>R k::'a)
     (\<Sum>k\<in>Basis. (max (m k * (a\<bullet>k)) (m k * (b\<bullet>k))) *\<^sub>R k))"
proof cases
  assume *: "cbox a b \<noteq> {}"
  show ?thesis
    unfolding box_ne_empty if_not_P[OF *]
    apply (simp add: cbox_def image_Collect set_eq_iff euclidean_eq_iff[where 'a='a] ball_conj_distrib[symmetric])
    apply (subst choice_Basis_iff[symmetric])
  proof (intro allI ball_cong refl)
    fix x i :: 'a assume "i \<in> Basis"
    with * have a_le_b: "a \<bullet> i \<le> b \<bullet> i"
      unfolding box_ne_empty by auto
    show "(\<exists>xa. x \<bullet> i = m i * xa \<and> a \<bullet> i \<le> xa \<and> xa \<le> b \<bullet> i) \<longleftrightarrow>
        min (m i * (a \<bullet> i)) (m i * (b \<bullet> i)) \<le> x \<bullet> i \<and> x \<bullet> i \<le> max (m i * (a \<bullet> i)) (m i * (b \<bullet> i))"
    proof (cases "m i = 0")
      case True
      with a_le_b show ?thesis by auto
    next
      case False
      then have *: "\<And>a b. a = m i * b \<longleftrightarrow> b = a / m i"
        by (auto simp: field_simps)
      from False have
          "min (m i * (a \<bullet> i)) (m i * (b \<bullet> i)) = (if 0 < m i then m i * (a \<bullet> i) else m i * (b \<bullet> i))"
          "max (m i * (a \<bullet> i)) (m i * (b \<bullet> i)) = (if 0 < m i then m i * (b \<bullet> i) else m i * (a \<bullet> i))"
        using a_le_b by (auto simp: min_def max_def mult_le_cancel_left)
      with False show ?thesis using a_le_b
        unfolding * by (auto simp: le_divide_eq divide_le_eq ac_simps)
    qed
  qed
qed simp

lemma interval_image_stretch_interval:
  "\<exists>u v. (\<lambda>x. \<Sum>k\<in>Basis. (m k * (x\<bullet>k))*\<^sub>R k) ` cbox a (b::'a::euclidean_space) = cbox u (v::'a::euclidean_space)"
  unfolding image_stretch_interval by auto

lemma cbox_translation: "cbox (c + a) (c + b) = image (\<lambda>x. c + x) (cbox a b)"
  using image_affinity_cbox [of 1 c a b]
  using box_ne_empty [of "a+c" "b+c"]  box_ne_empty [of a b]
  by (auto simp: inner_left_distrib add.commute)

lemma cbox_image_unit_interval:
  fixes a :: "'a::euclidean_space"
  assumes "cbox a b \<noteq> {}"
    shows "cbox a b =
           (+) a ` (\<lambda>x. \<Sum>k\<in>Basis. ((b \<bullet> k - a \<bullet> k) * (x \<bullet> k)) *\<^sub>R k) ` cbox 0 One"
using assms
apply (simp add: box_ne_empty image_stretch_interval cbox_translation [symmetric])
apply (simp add: min_def max_def algebra_simps sum_subtractf euclidean_representation)
done

lemma closed_interval_as_convex_hull:
  fixes a :: "'a::euclidean_space"
  obtains S where "finite S" "cbox a b = convex hull S"
proof (cases "cbox a b = {}")
  case True with convex_hull_empty that show ?thesis
    by blast
next
  case False
  obtain S::"'a set" where "finite S" and eq: "cbox 0 One = convex hull S"
    by (blast intro: unit_cube_convex_hull)
  have lin: "linear (\<lambda>x. \<Sum>k\<in>Basis. ((b \<bullet> k - a \<bullet> k) * (x \<bullet> k)) *\<^sub>R k)"
    by (rule linear_compose_sum) (auto simp: algebra_simps linearI)
  have "finite ((+) a ` (\<lambda>x. \<Sum>k\<in>Basis. ((b \<bullet> k - a \<bullet> k) * (x \<bullet> k)) *\<^sub>R k) ` S)"
    by (rule finite_imageI \<open>finite S\<close>)+
  then show ?thesis
    apply (rule that)
    apply (simp add: convex_hull_translation convex_hull_linear_image [OF lin, symmetric])
    apply (simp add: eq [symmetric] cbox_image_unit_interval [OF False])
    done
qed


subsection%unimportant \<open>Bounded convex function on open set is continuous\<close>

lemma convex_on_bounded_continuous:
  fixes S :: "('a::real_normed_vector) set"
  assumes "open S"
    and "convex_on S f"
    and "\<forall>x\<in>S. \<bar>f x\<bar> \<le> b"
  shows "continuous_on S f"
  apply (rule continuous_at_imp_continuous_on)
  unfolding continuous_at_real_range
proof (rule,rule,rule)
  fix x and e :: real
  assume "x \<in> S" "e > 0"
  define B where "B = \<bar>b\<bar> + 1"
  then have B:  "0 < B""\<And>x. x\<in>S \<Longrightarrow> \<bar>f x\<bar> \<le> B"
    using assms(3) by auto 
  obtain k where "k > 0" and k: "cball x k \<subseteq> S"
    using \<open>x \<in> S\<close> assms(1) open_contains_cball_eq by blast
  show "\<exists>d>0. \<forall>x'. norm (x' - x) < d \<longrightarrow> \<bar>f x' - f x\<bar> < e"
  proof (intro exI conjI allI impI)
    fix y
    assume as: "norm (y - x) < min (k / 2) (e / (2 * B) * k)"
    show "\<bar>f y - f x\<bar> < e"
    proof (cases "y = x")
      case False
      define t where "t = k / norm (y - x)"
      have "2 < t" "0<t"
        unfolding t_def using as False and \<open>k>0\<close>
        by (auto simp:field_simps)
      have "y \<in> S"
        apply (rule k[THEN subsetD])
        unfolding mem_cball dist_norm
        apply (rule order_trans[of _ "2 * norm (x - y)"])
        using as
        by (auto simp: field_simps norm_minus_commute)
      {
        define w where "w = x + t *\<^sub>R (y - x)"
        have "w \<in> S"
          using \<open>k>0\<close> by (auto simp: dist_norm t_def w_def k[THEN subsetD])
        have "(1 / t) *\<^sub>R x + - x + ((t - 1) / t) *\<^sub>R x = (1 / t - 1 + (t - 1) / t) *\<^sub>R x"
          by (auto simp: algebra_simps)
        also have "\<dots> = 0"
          using \<open>t > 0\<close> by (auto simp:field_simps)
        finally have w: "(1 / t) *\<^sub>R w + ((t - 1) / t) *\<^sub>R x = y"
          unfolding w_def using False and \<open>t > 0\<close>
          by (auto simp: algebra_simps)
        have 2: "2 * B < e * t"
          unfolding t_def using \<open>0 < e\<close> \<open>0 < k\<close> \<open>B > 0\<close> and as and False
          by (auto simp:field_simps)
        have "f y - f x \<le> (f w - f x) / t"
          using assms(2)[unfolded convex_on_def,rule_format,of w x "1/t" "(t - 1)/t", unfolded w]
          using \<open>0 < t\<close> \<open>2 < t\<close> and \<open>x \<in> S\<close> \<open>w \<in> S\<close>
          by (auto simp:field_simps)
        also have "... < e"
          using B(2)[OF \<open>w\<in>S\<close>] and B(2)[OF \<open>x\<in>S\<close>] 2 \<open>t > 0\<close> by (auto simp: field_simps)
        finally have th1: "f y - f x < e" .
      }
      moreover
      {
        define w where "w = x - t *\<^sub>R (y - x)"
        have "w \<in> S"
          using \<open>k > 0\<close> by (auto simp: dist_norm t_def w_def k[THEN subsetD])
        have "(1 / (1 + t)) *\<^sub>R x + (t / (1 + t)) *\<^sub>R x = (1 / (1 + t) + t / (1 + t)) *\<^sub>R x"
          by (auto simp: algebra_simps)
        also have "\<dots> = x"
          using \<open>t > 0\<close> by (auto simp:field_simps)
        finally have w: "(1 / (1+t)) *\<^sub>R w + (t / (1 + t)) *\<^sub>R y = x"
          unfolding w_def using False and \<open>t > 0\<close>
          by (auto simp: algebra_simps)
        have "2 * B < e * t"
          unfolding t_def
          using \<open>0 < e\<close> \<open>0 < k\<close> \<open>B > 0\<close> and as and False
          by (auto simp:field_simps)
        then have *: "(f w - f y) / t < e"
          using B(2)[OF \<open>w\<in>S\<close>] and B(2)[OF \<open>y\<in>S\<close>]
          using \<open>t > 0\<close>
          by (auto simp:field_simps)
        have "f x \<le> 1 / (1 + t) * f w + (t / (1 + t)) * f y"
          using assms(2)[unfolded convex_on_def,rule_format,of w y "1/(1+t)" "t / (1+t)",unfolded w]
          using \<open>0 < t\<close> \<open>2 < t\<close> and \<open>y \<in> S\<close> \<open>w \<in> S\<close>
          by (auto simp:field_simps)
        also have "\<dots> = (f w + t * f y) / (1 + t)"
          using \<open>t > 0\<close> by (auto simp: divide_simps)
        also have "\<dots> < e + f y"
          using \<open>t > 0\<close> * \<open>e > 0\<close> by (auto simp: field_simps)
        finally have "f x - f y < e" by auto
      }
      ultimately show ?thesis by auto
    qed (insert \<open>0<e\<close>, auto)
  qed (insert \<open>0<e\<close> \<open>0<k\<close> \<open>0<B\<close>, auto simp: field_simps)
qed


subsection%unimportant \<open>Upper bound on a ball implies upper and lower bounds\<close>

lemma convex_bounds_lemma:
  fixes x :: "'a::real_normed_vector"
  assumes "convex_on (cball x e) f"
    and "\<forall>y \<in> cball x e. f y \<le> b"
  shows "\<forall>y \<in> cball x e. \<bar>f y\<bar> \<le> b + 2 * \<bar>f x\<bar>"
  apply rule
proof (cases "0 \<le> e")
  case True
  fix y
  assume y: "y \<in> cball x e"
  define z where "z = 2 *\<^sub>R x - y"
  have *: "x - (2 *\<^sub>R x - y) = y - x"
    by (simp add: scaleR_2)
  have z: "z \<in> cball x e"
    using y unfolding z_def mem_cball dist_norm * by (auto simp: norm_minus_commute)
  have "(1 / 2) *\<^sub>R y + (1 / 2) *\<^sub>R z = x"
    unfolding z_def by (auto simp: algebra_simps)
  then show "\<bar>f y\<bar> \<le> b + 2 * \<bar>f x\<bar>"
    using assms(1)[unfolded convex_on_def,rule_format, OF y z, of "1/2" "1/2"]
    using assms(2)[rule_format,OF y] assms(2)[rule_format,OF z]
    by (auto simp:field_simps)
next
  case False
  fix y
  assume "y \<in> cball x e"
  then have "dist x y < 0"
    using False unfolding mem_cball not_le by (auto simp del: dist_not_less_zero)
  then show "\<bar>f y\<bar> \<le> b + 2 * \<bar>f x\<bar>"
    using zero_le_dist[of x y] by auto
qed


subsubsection%unimportant \<open>Hence a convex function on an open set is continuous\<close>

lemma real_of_nat_ge_one_iff: "1 \<le> real (n::nat) \<longleftrightarrow> 1 \<le> n"
  by auto

lemma convex_on_continuous:
  assumes "open (s::('a::euclidean_space) set)" "convex_on s f"
  shows "continuous_on s f"
  unfolding continuous_on_eq_continuous_at[OF assms(1)]
proof
  note dimge1 = DIM_positive[where 'a='a]
  fix x
  assume "x \<in> s"
  then obtain e where e: "cball x e \<subseteq> s" "e > 0"
    using assms(1) unfolding open_contains_cball by auto
  define d where "d = e / real DIM('a)"
  have "0 < d"
    unfolding d_def using \<open>e > 0\<close> dimge1 by auto
  let ?d = "(\<Sum>i\<in>Basis. d *\<^sub>R i)::'a"
  obtain c
    where c: "finite c"
    and c1: "convex hull c \<subseteq> cball x e"
    and c2: "cball x d \<subseteq> convex hull c"
  proof
    define c where "c = (\<Sum>i\<in>Basis. (\<lambda>a. a *\<^sub>R i) ` {x\<bullet>i - d, x\<bullet>i + d})"
    show "finite c"
      unfolding c_def by (simp add: finite_set_sum)
    have 1: "convex hull c = {a. \<forall>i\<in>Basis. a \<bullet> i \<in> cbox (x \<bullet> i - d) (x \<bullet> i + d)}"
      unfolding box_eq_set_sum_Basis
      unfolding c_def convex_hull_set_sum
      apply (subst convex_hull_linear_image [symmetric])
      apply (simp add: linear_iff scaleR_add_left)
      apply (rule sum.cong [OF refl])
      apply (rule image_cong [OF _ refl])
      apply (rule convex_hull_eq_real_cbox)
      apply (cut_tac \<open>0 < d\<close>, simp)
      done
    then have 2: "convex hull c = {a. \<forall>i\<in>Basis. a \<bullet> i \<in> cball (x \<bullet> i) d}"
      by (simp add: dist_norm abs_le_iff algebra_simps)
    show "cball x d \<subseteq> convex hull c"
      unfolding 2
      by (clarsimp simp: dist_norm) (metis inner_commute inner_diff_right norm_bound_Basis_le)
    have e': "e = (\<Sum>(i::'a)\<in>Basis. d)"
      by (simp add: d_def DIM_positive)
    show "convex hull c \<subseteq> cball x e"
      unfolding 2
      apply clarsimp
      apply (subst euclidean_dist_l2)
      apply (rule order_trans [OF L2_set_le_sum])
      apply (rule zero_le_dist)
      unfolding e'
      apply (rule sum_mono, simp)
      done
  qed
  define k where "k = Max (f ` c)"
  have "convex_on (convex hull c) f"
    apply(rule convex_on_subset[OF assms(2)])
    apply(rule subset_trans[OF c1 e(1)])
    done
  then have k: "\<forall>y\<in>convex hull c. f y \<le> k"
    apply (rule_tac convex_on_convex_hull_bound, assumption)
    by (simp add: k_def c)
  have "e \<le> e * real DIM('a)"
    using e(2) real_of_nat_ge_one_iff by auto
  then have "d \<le> e"
    by (simp add: d_def divide_simps)
  then have dsube: "cball x d \<subseteq> cball x e"
    by (rule subset_cball)
  have conv: "convex_on (cball x d) f"
    using \<open>convex_on (convex hull c) f\<close> c2 convex_on_subset by blast
  then have "\<forall>y\<in>cball x d. \<bar>f y\<bar> \<le> k + 2 * \<bar>f x\<bar>"
    by (rule convex_bounds_lemma) (use c2 k in blast)
  then have "continuous_on (ball x d) f"
    apply (rule_tac convex_on_bounded_continuous)
    apply (rule open_ball, rule convex_on_subset[OF conv])
    apply (rule ball_subset_cball, force)
    done
  then show "continuous (at x) f"
    unfolding continuous_on_eq_continuous_at[OF open_ball]
    using \<open>d > 0\<close> by auto
qed

end
