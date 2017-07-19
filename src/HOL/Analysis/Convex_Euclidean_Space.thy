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
  Topology_Euclidean_Space
  "~~/src/HOL/Library/Set_Algebras"
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

lemma dim_image_eq:
  fixes f :: "'n::euclidean_space \<Rightarrow> 'm::euclidean_space"
  assumes lf: "linear f"
    and fi: "inj_on f (span S)"
  shows "dim (f ` S) = dim (S::'n::euclidean_space set)"
proof -
  obtain B where B: "B \<subseteq> S" "independent B" "S \<subseteq> span B" "card B = dim S"
    using basis_exists[of S] by auto
  then have "span S = span B"
    using span_mono[of B S] span_mono[of S "span B"] span_span[of B] by auto
  then have "independent (f ` B)"
    using independent_inj_on_image[of B f] B assms by auto
  moreover have "card (f ` B) = card B"
    using assms card_image[of f B] subset_inj_on[of f "span S" B] B span_inc by auto
  moreover have "(f ` B) \<subseteq> (f ` S)"
    using B by auto
  ultimately have "dim (f ` S) \<ge> dim S"
    using independent_card_le_dim[of "f ` B" "f ` S"] B by auto
  then show ?thesis
    using dim_image_le[of f S] assms by auto
qed

lemma linear_injective_on_subspace_0:
  assumes lf: "linear f"
    and "subspace S"
  shows "inj_on f S \<longleftrightarrow> (\<forall>x \<in> S. f x = 0 \<longrightarrow> x = 0)"
proof -
  have "inj_on f S \<longleftrightarrow> (\<forall>x \<in> S. \<forall>y \<in> S. f x = f y \<longrightarrow> x = y)"
    by (simp add: inj_on_def)
  also have "\<dots> \<longleftrightarrow> (\<forall>x \<in> S. \<forall>y \<in> S. f x - f y = 0 \<longrightarrow> x - y = 0)"
    by simp
  also have "\<dots> \<longleftrightarrow> (\<forall>x \<in> S. \<forall>y \<in> S. f (x - y) = 0 \<longrightarrow> x - y = 0)"
    by (simp add: linear_diff[OF lf])
  also have "\<dots> \<longleftrightarrow> (\<forall>x \<in> S. f x = 0 \<longrightarrow> x = 0)"
    using \<open>subspace S\<close> subspace_def[of S] subspace_diff[of S] by auto
  finally show ?thesis .
qed

lemma subspace_Inter: "\<forall>s \<in> f. subspace s \<Longrightarrow> subspace (\<Inter>f)"
  unfolding subspace_def by auto

lemma span_eq[simp]: "span s = s \<longleftrightarrow> subspace s"
  unfolding span_def by (rule hull_eq) (rule subspace_Inter)

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
      using span_mul[of y "cball 0 e" "norm x/e"] span_inc[of "cball 0 e"]
      by (simp add: span_superset)
  }
  then have "span (cball 0 e) = (UNIV :: 'n::euclidean_space set)"
    by auto
  then show ?thesis
    using dim_span[of "cball (0 :: 'n::euclidean_space) e"] by (auto simp add: dim_UNIV)
qed

lemma indep_card_eq_dim_span:
  fixes B :: "'n::euclidean_space set"
  assumes "independent B"
  shows "finite B \<and> card B = dim (span B)"
  using assms basis_card_eq_dim[of B "span B"] span_inc by auto

lemma sum_not_0: "sum f A \<noteq> 0 \<Longrightarrow> \<exists>a \<in> A. f a \<noteq> 0"
  by (rule ccontr) auto

lemma subset_translation_eq [simp]:
    fixes a :: "'a::real_vector" shows "op + a ` s \<subseteq> op + a ` t \<longleftrightarrow> s \<subseteq> t"
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
      apply (rule exI[of _ "x-a"])
      apply simp
      done
    then have "x \<in> ((\<lambda>x. a+x) ` S)" by auto
  }
  then show ?thesis by auto
qed

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

definition convex_on :: "'a::real_vector set \<Rightarrow> ('a \<Rightarrow> real) \<Rightarrow> bool"
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
  have "(\<lambda>x. a + c *\<^sub>R x) ` S = op + a ` op *\<^sub>R c ` S"
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


subsection \<open>Convexity of real functions\<close>

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

lemma basis_to_basis_subspace_isomorphism:
  assumes s: "subspace (S:: ('n::euclidean_space) set)"
    and t: "subspace (T :: ('m::euclidean_space) set)"
    and d: "dim S = dim T"
    and B: "B \<subseteq> S" "independent B" "S \<subseteq> span B" "card B = dim S"
    and C: "C \<subseteq> T" "independent C" "T \<subseteq> span C" "card C = dim T"
  shows "\<exists>f. linear f \<and> f ` B = C \<and> f ` S = T \<and> inj_on f S"
proof -
  from B independent_bound have fB: "finite B"
    by blast
  from C independent_bound have fC: "finite C"
    by blast
  from B(4) C(4) card_le_inj[of B C] d obtain f where
    f: "f ` B \<subseteq> C" "inj_on f B" using \<open>finite B\<close> \<open>finite C\<close> by auto
  from linear_independent_extend[OF B(2)] obtain g where
    g: "linear g" "\<forall>x \<in> B. g x = f x" by blast
  from inj_on_iff_eq_card[OF fB, of f] f(2)
  have "card (f ` B) = card B" by simp
  with B(4) C(4) have ceq: "card (f ` B) = card C" using d
    by simp
  have "g ` B = f ` B" using g(2)
    by (auto simp add: image_iff)
  also have "\<dots> = C" using card_subset_eq[OF fC f(1) ceq] .
  finally have gBC: "g ` B = C" .
  have gi: "inj_on g B" using f(2) g(2)
    by (auto simp add: inj_on_def)
  note g0 = linear_indep_image_lemma[OF g(1) fB, unfolded gBC, OF C(2) gi]
  {
    fix x y
    assume x: "x \<in> S" and y: "y \<in> S" and gxy: "g x = g y"
    from B(3) x y have x': "x \<in> span B" and y': "y \<in> span B"
      by blast+
    from gxy have th0: "g (x - y) = 0"
      by (simp add: linear_diff[OF g(1)])
    have th1: "x - y \<in> span B" using x' y'
      by (metis span_diff)
    have "x = y" using g0[OF th1 th0] by simp
  }
  then have giS: "inj_on g S" unfolding inj_on_def by blast
  from span_subspace[OF B(1,3) s]
  have "g ` S = span (g ` B)"
    by (simp add: span_linear_image[OF g(1)])
  also have "\<dots> = span C"
    unfolding gBC ..
  also have "\<dots> = T"
    using span_subspace[OF C(1,3) t] .
  finally have gS: "g ` S = T" .
  from g(1) gS giS gBC show ?thesis
    by blast
qed

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
  have [simp]: "{x \<in> range f. g x \<in> S} = f ` S"
    using g by (simp add: o_def id_def image_def) metis
  show ?thesis
    apply (rule closedin_closed_trans [of "range f"])
    apply (rule continuous_closedin_preimage [OF confg cgf, simplified])
    apply (rule closed_injective_image_subspace)
    using f
    apply (auto simp: linear_linear linear_injective_0)
    done
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
  shows "(op *\<^sub>R c) ` (closure S) = closure ((op *\<^sub>R c) ` S)"
proof
  show "(op *\<^sub>R c) ` (closure S) \<subseteq> closure ((op *\<^sub>R c) ` S)"
    using bounded_linear_scaleR_right
    by (rule closure_bounded_linear_image_subset)
  show "closure ((op *\<^sub>R c) ` S) \<subseteq> (op *\<^sub>R c) ` (closure S)"
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
    by (auto simp add:norm_minus_commute)
qed


subsection \<open>Affine set and affine hull\<close>

definition affine :: "'a::real_vector set \<Rightarrow> bool"
  where "affine s \<longleftrightarrow> (\<forall>x\<in>s. \<forall>y\<in>s. \<forall>u v. u + v = 1 \<longrightarrow> u *\<^sub>R x + v *\<^sub>R y \<in> s)"

lemma affine_alt: "affine s \<longleftrightarrow> (\<forall>x\<in>s. \<forall>y\<in>s. \<forall>u::real. (1 - u) *\<^sub>R x + u *\<^sub>R y \<in> s)"
  unfolding affine_def by (metis eq_diff_eq')

lemma affine_empty [iff]: "affine {}"
  unfolding affine_def by auto

lemma affine_sing [iff]: "affine {x}"
  unfolding affine_alt by (auto simp add: scaleR_left_distrib [symmetric])

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


subsubsection \<open>Some explicit formulations (from Lars Schewe)\<close>

lemma affine:
  fixes V::"'a::real_vector set"
  shows "affine V \<longleftrightarrow>
    (\<forall>s u. finite s \<and> s \<noteq> {} \<and> s \<subseteq> V \<and> sum u s = 1 \<longrightarrow> (sum (\<lambda>x. (u x) *\<^sub>R x)) s \<in> V)"
  unfolding affine_def
  apply rule
  apply(rule, rule, rule)
  apply(erule conjE)+
  defer
  apply (rule, rule, rule, rule, rule)
proof -
  fix x y u v
  assume as: "x \<in> V" "y \<in> V" "u + v = (1::real)"
    "\<forall>s u. finite s \<and> s \<noteq> {} \<and> s \<subseteq> V \<and> sum u s = 1 \<longrightarrow> (\<Sum>x\<in>s. u x *\<^sub>R x) \<in> V"
  then show "u *\<^sub>R x + v *\<^sub>R y \<in> V"
    apply (cases "x = y")
    using as(4)[THEN spec[where x="{x,y}"], THEN spec[where x="\<lambda>w. if w = x then u else v"]]
      and as(1-3)
    apply (auto simp add: scaleR_left_distrib[symmetric])
    done
next
  fix s u
  assume as: "\<forall>x\<in>V. \<forall>y\<in>V. \<forall>u v. u + v = 1 \<longrightarrow> u *\<^sub>R x + v *\<^sub>R y \<in> V"
    "finite s" "s \<noteq> {}" "s \<subseteq> V" "sum u s = (1::real)"
  define n where "n = card s"
  have "card s = 0 \<or> card s = 1 \<or> card s = 2 \<or> card s > 2" by auto
  then show "(\<Sum>x\<in>s. u x *\<^sub>R x) \<in> V"
  proof (auto simp only: disjE)
    assume "card s = 2"
    then have "card s = Suc (Suc 0)"
      by auto
    then obtain a b where "s = {a, b}"
      unfolding card_Suc_eq by auto
    then show ?thesis
      using as(1)[THEN bspec[where x=a], THEN bspec[where x=b]] using as(4,5)
      by (auto simp add: sum_clauses(2))
  next
    assume "card s > 2"
    then show ?thesis using as and n_def
    proof (induct n arbitrary: u s)
      case 0
      then show ?case by auto
    next
      case (Suc n)
      fix s :: "'a set" and u :: "'a \<Rightarrow> real"
      assume IA:
        "\<And>u s.  \<lbrakk>2 < card s; \<forall>x\<in>V. \<forall>y\<in>V. \<forall>u v. u + v = 1 \<longrightarrow> u *\<^sub>R x + v *\<^sub>R y \<in> V; finite s;
          s \<noteq> {}; s \<subseteq> V; sum u s = 1; n = card s \<rbrakk> \<Longrightarrow> (\<Sum>x\<in>s. u x *\<^sub>R x) \<in> V"
        and as:
          "Suc n = card s" "2 < card s" "\<forall>x\<in>V. \<forall>y\<in>V. \<forall>u v. u + v = 1 \<longrightarrow> u *\<^sub>R x + v *\<^sub>R y \<in> V"
           "finite s" "s \<noteq> {}" "s \<subseteq> V" "sum u s = 1"
      have "\<exists>x\<in>s. u x \<noteq> 1"
      proof (rule ccontr)
        assume "\<not> ?thesis"
        then have "sum u s = real_of_nat (card s)"
          unfolding card_eq_sum by auto
        then show False
          using as(7) and \<open>card s > 2\<close>
          by (metis One_nat_def less_Suc0 Zero_not_Suc of_nat_1 of_nat_eq_iff numeral_2_eq_2)
      qed
      then obtain x where x:"x \<in> s" "u x \<noteq> 1" by auto

      have c: "card (s - {x}) = card s - 1"
        apply (rule card_Diff_singleton)
        using \<open>x\<in>s\<close> as(4)
        apply auto
        done
      have *: "s = insert x (s - {x})" "finite (s - {x})"
        using \<open>x\<in>s\<close> and as(4) by auto
      have **: "sum u (s - {x}) = 1 - u x"
        using sum_clauses(2)[OF *(2), of u x, unfolded *(1)[symmetric] as(7)] by auto
      have ***: "inverse (1 - u x) * sum u (s - {x}) = 1"
        unfolding ** using \<open>u x \<noteq> 1\<close> by auto
      have "(\<Sum>xa\<in>s - {x}. (inverse (1 - u x) * u xa) *\<^sub>R xa) \<in> V"
      proof (cases "card (s - {x}) > 2")
        case True
        then have "s - {x} \<noteq> {}" "card (s - {x}) = n"
          unfolding c and as(1)[symmetric]
        proof (rule_tac ccontr)
          assume "\<not> s - {x} \<noteq> {}"
          then have "card (s - {x}) = 0" unfolding card_0_eq[OF *(2)] by simp
          then show False using True by auto
        qed auto
        then show ?thesis
          apply (rule_tac IA[of "s - {x}" "\<lambda>y. (inverse (1 - u x) * u y)"])
          unfolding sum_distrib_left[symmetric]
          using as and *** and True
          apply auto
          done
      next
        case False
        then have "card (s - {x}) = Suc (Suc 0)"
          using as(2) and c by auto
        then obtain a b where "(s - {x}) = {a, b}" "a\<noteq>b"
          unfolding card_Suc_eq by auto
        then show ?thesis
          using as(3)[THEN bspec[where x=a], THEN bspec[where x=b]]
          using *** *(2) and \<open>s \<subseteq> V\<close>
          unfolding sum_distrib_left
          by (auto simp add: sum_clauses(2))
      qed
      then have "u x + (1 - u x) = 1 \<Longrightarrow>
          u x *\<^sub>R x + (1 - u x) *\<^sub>R ((\<Sum>xa\<in>s - {x}. u xa *\<^sub>R xa) /\<^sub>R (1 - u x)) \<in> V"
        apply -
        apply (rule as(3)[rule_format])
        unfolding  Real_Vector_Spaces.scaleR_right.sum
        using x(1) as(6)
        apply auto
        done
      then show "(\<Sum>x\<in>s. u x *\<^sub>R x) \<in> V"
        unfolding scaleR_scaleR[symmetric] and scaleR_right.sum [symmetric]
        apply (subst *)
        unfolding sum_clauses(2)[OF *(2)]
        using \<open>u x \<noteq> 1\<close>
        apply auto
        done
    qed
  next
    assume "card s = 1"
    then obtain a where "s={a}"
      by (auto simp add: card_Suc_eq)
    then show ?thesis
      using as(4,5) by simp
  qed (insert \<open>s\<noteq>{}\<close> \<open>finite s\<close>, auto)
qed

lemma affine_hull_explicit:
  "affine hull p =
    {y. \<exists>s u. finite s \<and> s \<noteq> {} \<and> s \<subseteq> p \<and> sum u s = 1 \<and> sum (\<lambda>v. (u v) *\<^sub>R v) s = y}"
  apply (rule hull_unique)
  apply (subst subset_eq)
  prefer 3
  apply rule
  unfolding mem_Collect_eq
  apply (erule exE)+
  apply (erule conjE)+
  prefer 2
  apply rule
proof -
  fix x
  assume "x\<in>p"
  then show "\<exists>s u. finite s \<and> s \<noteq> {} \<and> s \<subseteq> p \<and> sum u s = 1 \<and> (\<Sum>v\<in>s. u v *\<^sub>R v) = x"
    apply (rule_tac x="{x}" in exI)
    apply (rule_tac x="\<lambda>x. 1" in exI)
    apply auto
    done
next
  fix t x s u
  assume as: "p \<subseteq> t" "affine t" "finite s" "s \<noteq> {}"
    "s \<subseteq> p" "sum u s = 1" "(\<Sum>v\<in>s. u v *\<^sub>R v) = x"
  then show "x \<in> t"
    using as(2)[unfolded affine, THEN spec[where x=s], THEN spec[where x=u]]
    by auto
next
  show "affine {y. \<exists>s u. finite s \<and> s \<noteq> {} \<and> s \<subseteq> p \<and> sum u s = 1 \<and> (\<Sum>v\<in>s. u v *\<^sub>R v) = y}"
    unfolding affine_def
    apply (rule, rule, rule, rule, rule)
    unfolding mem_Collect_eq
  proof -
    fix u v :: real
    assume uv: "u + v = 1"
    fix x
    assume "\<exists>s u. finite s \<and> s \<noteq> {} \<and> s \<subseteq> p \<and> sum u s = 1 \<and> (\<Sum>v\<in>s. u v *\<^sub>R v) = x"
    then obtain sx ux where
      x: "finite sx" "sx \<noteq> {}" "sx \<subseteq> p" "sum ux sx = 1" "(\<Sum>v\<in>sx. ux v *\<^sub>R v) = x"
      by auto
    fix y
    assume "\<exists>s u. finite s \<and> s \<noteq> {} \<and> s \<subseteq> p \<and> sum u s = 1 \<and> (\<Sum>v\<in>s. u v *\<^sub>R v) = y"
    then obtain sy uy where
      y: "finite sy" "sy \<noteq> {}" "sy \<subseteq> p" "sum uy sy = 1" "(\<Sum>v\<in>sy. uy v *\<^sub>R v) = y" by auto
    have xy: "finite (sx \<union> sy)"
      using x(1) y(1) by auto
    have **: "(sx \<union> sy) \<inter> sx = sx" "(sx \<union> sy) \<inter> sy = sy"
      by auto
    show "\<exists>s ua. finite s \<and> s \<noteq> {} \<and> s \<subseteq> p \<and>
        sum ua s = 1 \<and> (\<Sum>v\<in>s. ua v *\<^sub>R v) = u *\<^sub>R x + v *\<^sub>R y"
      apply (rule_tac x="sx \<union> sy" in exI)
      apply (rule_tac x="\<lambda>a. (if a\<in>sx then u * ux a else 0) + (if a\<in>sy then v * uy a else 0)" in exI)
      unfolding scaleR_left_distrib sum.distrib if_smult scaleR_zero_left
        ** sum.inter_restrict[OF xy, symmetric]
      unfolding scaleR_scaleR[symmetric] Real_Vector_Spaces.scaleR_right.sum [symmetric]
        and sum_distrib_left[symmetric]
      unfolding x y
      using x(1-3) y(1-3) uv
      apply simp
      done
  qed
qed

lemma affine_hull_finite:
  assumes "finite s"
  shows "affine hull s = {y. \<exists>u. sum u s = 1 \<and> sum (\<lambda>v. u v *\<^sub>R v) s = y}"
  unfolding affine_hull_explicit and set_eq_iff and mem_Collect_eq
  apply (rule, rule)
  apply (erule exE)+
  apply (erule conjE)+
  defer
  apply (erule exE)
  apply (erule conjE)
proof -
  fix x u
  assume "sum u s = 1" "(\<Sum>v\<in>s. u v *\<^sub>R v) = x"
  then show "\<exists>sa u. finite sa \<and>
      \<not> (\<forall>x. (x \<in> sa) = (x \<in> {})) \<and> sa \<subseteq> s \<and> sum u sa = 1 \<and> (\<Sum>v\<in>sa. u v *\<^sub>R v) = x"
    apply (rule_tac x=s in exI, rule_tac x=u in exI)
    using assms
    apply auto
    done
next
  fix x t u
  assume "t \<subseteq> s"
  then have *: "s \<inter> t = t"
    by auto
  assume "finite t" "\<not> (\<forall>x. (x \<in> t) = (x \<in> {}))" "sum u t = 1" "(\<Sum>v\<in>t. u v *\<^sub>R v) = x"
  then show "\<exists>u. sum u s = 1 \<and> (\<Sum>v\<in>s. u v *\<^sub>R v) = x"
    apply (rule_tac x="\<lambda>x. if x\<in>t then u x else 0" in exI)
    unfolding if_smult scaleR_zero_left and sum.inter_restrict[OF assms, symmetric] and *
    apply auto
    done
qed


subsubsection \<open>Stepping theorems and hence small special cases\<close>

lemma affine_hull_empty[simp]: "affine hull {} = {}"
  by (rule hull_unique) auto

(*could delete: it simply rewrites sum expressions, but it's used twice*)
lemma affine_hull_finite_step:
  fixes y :: "'a::real_vector"
  shows
    "(\<exists>u. sum u {} = w \<and> sum (\<lambda>x. u x *\<^sub>R x) {} = y) \<longleftrightarrow> w = 0 \<and> y = 0" (is ?th1)
    and
    "finite s \<Longrightarrow>
      (\<exists>u. sum u (insert a s) = w \<and> sum (\<lambda>x. u x *\<^sub>R x) (insert a s) = y) \<longleftrightarrow>
      (\<exists>v u. sum u s = w - v \<and> sum (\<lambda>x. u x *\<^sub>R x) s = y - v *\<^sub>R a)" (is "_ \<Longrightarrow> ?lhs = ?rhs")
proof -
  show ?th1 by simp
  assume fin: "finite s"
  show "?lhs = ?rhs"
  proof
    assume ?lhs
    then obtain u where u: "sum u (insert a s) = w \<and> (\<Sum>x\<in>insert a s. u x *\<^sub>R x) = y"
      by auto
    show ?rhs
    proof (cases "a \<in> s")
      case True
      then have *: "insert a s = s" by auto
      show ?thesis
        using u[unfolded *]
        apply(rule_tac x=0 in exI)
        apply auto
        done
    next
      case False
      then show ?thesis
        apply (rule_tac x="u a" in exI)
        using u and fin
        apply auto
        done
    qed
  next
    assume ?rhs
    then obtain v u where vu: "sum u s = w - v"  "(\<Sum>x\<in>s. u x *\<^sub>R x) = y - v *\<^sub>R a"
      by auto
    have *: "\<And>x M. (if x = a then v else M) *\<^sub>R x = (if x = a then v *\<^sub>R x else M *\<^sub>R x)"
      by auto
    show ?lhs
    proof (cases "a \<in> s")
      case True
      then show ?thesis
        apply (rule_tac x="\<lambda>x. (if x=a then v else 0) + u x" in exI)
        unfolding sum_clauses(2)[OF fin]
        apply simp
        unfolding scaleR_left_distrib and sum.distrib
        unfolding vu and * and scaleR_zero_left
        apply (auto simp add: sum.delta[OF fin])
        done
    next
      case False
      then have **:
        "\<And>x. x \<in> s \<Longrightarrow> u x = (if x = a then v else u x)"
        "\<And>x. x \<in> s \<Longrightarrow> u x *\<^sub>R x = (if x = a then v *\<^sub>R x else u x *\<^sub>R x)" by auto
      from False show ?thesis
        apply (rule_tac x="\<lambda>x. if x=a then v else u x" in exI)
        unfolding sum_clauses(2)[OF fin] and * using vu
        using sum.cong [of s _ "\<lambda>x. u x *\<^sub>R x" "\<lambda>x. if x = a then v *\<^sub>R x else u x *\<^sub>R x", OF _ **(2)]
        using sum.cong [of s _ u "\<lambda>x. if x = a then v else u x", OF _ **(1)]
        apply auto
        done
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
    by (simp add: affine_hull_finite_step(2)[of "{b}" a])
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
    apply auto
    apply (rule_tac x=v in exI)
    apply (rule_tac x=va in exI)
    apply auto
    apply (rule_tac x=u in exI)
    apply force
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


subsubsection \<open>Some relations between affine hull and subspaces\<close>

lemma affine_hull_insert_subset_span:
  "affine hull (insert a s) \<subseteq> {a + v| v . v \<in> span {x - a | x . x \<in> s}}"
  unfolding subset_eq Ball_def
  unfolding affine_hull_explicit span_explicit mem_Collect_eq
  apply (rule, rule)
  apply (erule exE)+
  apply (erule conjE)+
proof -
  fix x t u
  assume as: "finite t" "t \<noteq> {}" "t \<subseteq> insert a s" "sum u t = 1" "(\<Sum>v\<in>t. u v *\<^sub>R v) = x"
  have "(\<lambda>x. x - a) ` (t - {a}) \<subseteq> {x - a |x. x \<in> s}"
    using as(3) by auto
  then show "\<exists>v. x = a + v \<and> (\<exists>S u. finite S \<and> S \<subseteq> {x - a |x. x \<in> s} \<and> (\<Sum>v\<in>S. u v *\<^sub>R v) = v)"
    apply (rule_tac x="x - a" in exI)
    apply (rule conjI, simp)
    apply (rule_tac x="(\<lambda>x. x - a) ` (t - {a})" in exI)
    apply (rule_tac x="\<lambda>x. u (x + a)" in exI)
    apply (rule conjI) using as(1) apply simp
    apply (erule conjI)
    using as(1)
    apply (simp add: sum.reindex[unfolded inj_on_def] scaleR_right_diff_distrib
      sum_subtractf scaleR_left.sum[symmetric] sum_diff1 scaleR_left_diff_distrib)
    unfolding as
    apply simp
    done
qed

lemma affine_hull_insert_span:
  assumes "a \<notin> s"
  shows "affine hull (insert a s) = {a + v | v . v \<in> span {x - a | x.  x \<in> s}}"
  apply (rule, rule affine_hull_insert_subset_span)
  unfolding subset_eq Ball_def
  unfolding affine_hull_explicit and mem_Collect_eq
proof (rule, rule, erule exE, erule conjE)
  fix y v
  assume "y = a + v" "v \<in> span {x - a |x. x \<in> s}"
  then obtain t u where obt: "finite t" "t \<subseteq> {x - a |x. x \<in> s}" "a + (\<Sum>v\<in>t. u v *\<^sub>R v) = y"
    unfolding span_explicit by auto
  define f where "f = (\<lambda>x. x + a) ` t"
  have f: "finite f" "f \<subseteq> s" "(\<Sum>v\<in>f. u (v - a) *\<^sub>R (v - a)) = y - a"
    unfolding f_def using obt by (auto simp add: sum.reindex[unfolded inj_on_def])
  have *: "f \<inter> {a} = {}" "f \<inter> - {a} = f"
    using f(2) assms by auto
  show "\<exists>sa u. finite sa \<and> sa \<noteq> {} \<and> sa \<subseteq> insert a s \<and> sum u sa = 1 \<and> (\<Sum>v\<in>sa. u v *\<^sub>R v) = y"
    apply (rule_tac x = "insert a f" in exI)
    apply (rule_tac x = "\<lambda>x. if x=a then 1 - sum (\<lambda>x. u (x - a)) f else u (x - a)" in exI)
    using assms and f
    unfolding sum_clauses(2)[OF f(1)] and if_smult
    unfolding sum.If_cases[OF f(1), of "\<lambda>x. x = a"]
    apply (auto simp add: sum_subtractf scaleR_left.sum algebra_simps *)
    done
qed

lemma affine_hull_span:
  assumes "a \<in> s"
  shows "affine hull s = {a + v | v. v \<in> span {x - a | x. x \<in> s - {a}}}"
  using affine_hull_insert_span[of a "s - {a}", unfolded insert_Diff[OF assms]] by auto


subsubsection \<open>Parallel affine sets\<close>

definition affine_parallel :: "'a::real_vector set \<Rightarrow> 'a::real_vector set \<Rightarrow> bool"
  where "affine_parallel S T \<longleftrightarrow> (\<exists>a. T = (\<lambda>x. a + x) ` S)"

lemma affine_parallel_expl_aux:
  fixes S T :: "'a::real_vector set"
  assumes "\<forall>x. x \<in> S \<longleftrightarrow> a + x \<in> T"
  shows "T = (\<lambda>x. a + x) ` S"
proof -
  {
    fix x
    assume "x \<in> T"
    then have "( - a) + x \<in> S"
      using assms by auto
    then have "x \<in> ((\<lambda>x. a + x) ` S)"
      using imageI[of "-a+x" S "(\<lambda>x. a+x)"] by auto
  }
  moreover have "T \<ge> (\<lambda>x. a + x) ` S"
    using assms by auto
  ultimately show ?thesis by auto
qed

lemma affine_parallel_expl: "affine_parallel S T \<longleftrightarrow> (\<exists>a. \<forall>x. x \<in> S \<longleftrightarrow> a + x \<in> T)"
  unfolding affine_parallel_def
  using affine_parallel_expl_aux[of S _ T] by auto

lemma affine_parallel_reflex: "affine_parallel S S"
  unfolding affine_parallel_def
  apply (rule exI[of _ "0"])
  apply auto
  done

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
    then have "u *\<^sub>R x + v *\<^sub>R y : S" by auto
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


subsubsection \<open>Subspace parallel to an affine set\<close>

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
  moreover have "0 : ((\<lambda>x. (-a)+x) ` S)"
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

definition cone :: "'a::real_vector set \<Rightarrow> bool"
  where "cone s \<longleftrightarrow> (\<forall>x\<in>s. \<forall>c\<ge>0. c *\<^sub>R x \<in> s)"

lemma cone_empty[intro, simp]: "cone {}"
  unfolding cone_def by auto

lemma cone_univ[intro, simp]: "cone UNIV"
  unfolding cone_def by auto

lemma cone_Inter[intro]: "\<forall>s\<in>f. cone s \<Longrightarrow> cone (\<Inter>f)"
  unfolding cone_def by auto

lemma subspace_imp_cone: "subspace S \<Longrightarrow> cone S"
  by (simp add: cone_def subspace_mul)


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
  shows "c *\<^sub>R x : S"
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
  shows "cone S \<longleftrightarrow> 0 \<in> S \<and> (\<forall>c. c > 0 \<longrightarrow> (op *\<^sub>R c) ` S = S)"
proof -
  {
    assume "cone S"
    {
      fix c :: real
      assume "c > 0"
      {
        fix x
        assume "x \<in> S"
        then have "x \<in> (op *\<^sub>R c) ` S"
          unfolding image_def
          using \<open>cone S\<close> \<open>c>0\<close> mem_cone[of S x "1/c"]
            exI[of "(\<lambda>t. t \<in> S \<and> x = c *\<^sub>R t)" "(1 / c) *\<^sub>R x"]
          by auto
      }
      moreover
      {
        fix x
        assume "x \<in> (op *\<^sub>R c) ` S"
        then have "x \<in> S"
          using \<open>cone S\<close> \<open>c > 0\<close>
          unfolding cone_def image_def \<open>c > 0\<close> by auto
      }
      ultimately have "(op *\<^sub>R c) ` S = S" by auto
    }
    then have "0 \<in> S \<and> (\<forall>c. c > 0 \<longrightarrow> (op *\<^sub>R c) ` S = S)"
      using \<open>cone S\<close> cone_contains_0[of S] assms by auto
  }
  moreover
  {
    assume a: "0 \<in> S \<and> (\<forall>c. c > 0 \<longrightarrow> (op *\<^sub>R c) ` S = S)"
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

lemma cone_hull_expl: "cone hull S = {c *\<^sub>R x | c x. c \<ge> 0 \<and> x \<in> S}"
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
      apply (rule_tac x = 1 in exI)
      apply auto
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
  then have "0 \<in> S \<and> (\<forall>c. c > 0 \<longrightarrow> op *\<^sub>R c ` S = S)"
    using cone_iff[of S] assms by auto
  then have "0 \<in> closure S \<and> (\<forall>c. c > 0 \<longrightarrow> op *\<^sub>R c ` closure S = closure S)"
    using closure_subset by (auto simp add: closure_scaleR)
  then show ?thesis
    using False cone_iff[of "closure S"] by auto
qed


subsection \<open>Affine dependence and consequential theorems (from Lars Schewe)\<close>

definition affine_dependent :: "'a::real_vector set \<Rightarrow> bool"
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

lemma affine_dependent_explicit:
  "affine_dependent p \<longleftrightarrow>
    (\<exists>s u. finite s \<and> s \<subseteq> p \<and> sum u s = 0 \<and>
      (\<exists>v\<in>s. u v \<noteq> 0) \<and> sum (\<lambda>v. u v *\<^sub>R v) s = 0)"
  unfolding affine_dependent_def affine_hull_explicit mem_Collect_eq
  apply rule
  apply (erule bexE, erule exE, erule exE)
  apply (erule conjE)+
  defer
  apply (erule exE, erule exE)
  apply (erule conjE)+
  apply (erule bexE)
proof -
  fix x s u
  assume as: "x \<in> p" "finite s" "s \<noteq> {}" "s \<subseteq> p - {x}" "sum u s = 1" "(\<Sum>v\<in>s. u v *\<^sub>R v) = x"
  have "x \<notin> s" using as(1,4) by auto
  show "\<exists>s u. finite s \<and> s \<subseteq> p \<and> sum u s = 0 \<and> (\<exists>v\<in>s. u v \<noteq> 0) \<and> (\<Sum>v\<in>s. u v *\<^sub>R v) = 0"
    apply (rule_tac x="insert x s" in exI, rule_tac x="\<lambda>v. if v = x then - 1 else u v" in exI)
    unfolding if_smult and sum_clauses(2)[OF as(2)] and sum_delta_notmem[OF \<open>x\<notin>s\<close>] and as
    using as
    apply auto
    done
next
  fix s u v
  assume as: "finite s" "s \<subseteq> p" "sum u s = 0" "(\<Sum>v\<in>s. u v *\<^sub>R v) = 0" "v \<in> s" "u v \<noteq> 0"
  have "s \<noteq> {v}"
    using as(3,6) by auto
  then show "\<exists>x\<in>p. \<exists>s u. finite s \<and> s \<noteq> {} \<and> s \<subseteq> p - {x} \<and> sum u s = 1 \<and> (\<Sum>v\<in>s. u v *\<^sub>R v) = x"
    apply (rule_tac x=v in bexI)
    apply (rule_tac x="s - {v}" in exI)
    apply (rule_tac x="\<lambda>x. - (1 / u v) * u x" in exI)
    unfolding scaleR_scaleR[symmetric] and scaleR_right.sum [symmetric]
    unfolding sum_distrib_left[symmetric] and sum_diff1[OF as(1)]
    using as
    apply auto
    done
qed

lemma affine_dependent_explicit_finite:
  fixes s :: "'a::real_vector set"
  assumes "finite s"
  shows "affine_dependent s \<longleftrightarrow>
    (\<exists>u. sum u s = 0 \<and> (\<exists>v\<in>s. u v \<noteq> 0) \<and> sum (\<lambda>v. u v *\<^sub>R v) s = 0)"
  (is "?lhs = ?rhs")
proof
  have *: "\<And>vt u v. (if vt then u v else 0) *\<^sub>R v = (if vt then (u v) *\<^sub>R v else 0::'a)"
    by auto
  assume ?lhs
  then obtain t u v where
    "finite t" "t \<subseteq> s" "sum u t = 0" "v\<in>t" "u v \<noteq> 0"  "(\<Sum>v\<in>t. u v *\<^sub>R v) = 0"
    unfolding affine_dependent_explicit by auto
  then show ?rhs
    apply (rule_tac x="\<lambda>x. if x\<in>t then u x else 0" in exI)
    apply auto unfolding * and sum.inter_restrict[OF assms, symmetric]
    unfolding Int_absorb1[OF \<open>t\<subseteq>s\<close>]
    apply auto
    done
next
  assume ?rhs
  then obtain u v where "sum u s = 0"  "v\<in>s" "u v \<noteq> 0" "(\<Sum>v\<in>s. u v *\<^sub>R v) = 0"
    by auto
  then show ?lhs unfolding affine_dependent_explicit
    using assms by auto
qed


subsection \<open>Connectedness of convex sets\<close>

lemma connectedD:
  "connected S \<Longrightarrow> open A \<Longrightarrow> open B \<Longrightarrow> S \<subseteq> A \<union> B \<Longrightarrow> A \<inter> B \<inter> S = {} \<Longrightarrow> A \<inter> S = {} \<or> B \<inter> S = {}"
  by (rule Topological_Spaces.topological_space_class.connectedD)

lemma convex_connected:
  fixes s :: "'a::real_normed_vector set"
  assumes "convex s"
  shows "connected s"
proof (rule connectedI)
  fix A B
  assume "open A" "open B" "A \<inter> B \<inter> s = {}" "s \<subseteq> A \<union> B"
  moreover
  assume "A \<inter> s \<noteq> {}" "B \<inter> s \<noteq> {}"
  then obtain a b where a: "a \<in> A" "a \<in> s" and b: "b \<in> B" "b \<in> s" by auto
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
  moreover have "f ` {0 .. 1} \<subseteq> s"
    using \<open>convex s\<close> a b unfolding convex_def f_def by auto
  ultimately show False by auto
qed

corollary connected_UNIV[intro]: "connected (UNIV :: 'a::real_normed_vector set)"
  by(simp add: convex_connected)

proposition clopen:
  fixes s :: "'a :: real_normed_vector set"
  shows "closed s \<and> open s \<longleftrightarrow> s = {} \<or> s = UNIV"
apply (rule iffI)
 apply (rule connected_UNIV [unfolded connected_clopen, rule_format])
 apply (force simp add: closed_closedin, force)
done

corollary compact_open:
  fixes s :: "'a :: euclidean_space set"
  shows "compact s \<and> open s \<longleftrightarrow> s = {}"
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
    using real_lbound_gt_zero[of 1 "e / dist x y"] xy \<open>e>0\<close> by auto
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
proof (auto simp add: convex_def)
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
  then show ?thesis by (auto simp add: convex_def Ball_def)
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


subsubsection \<open>Convex hull is "preserved" by a linear function\<close>

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
  have "\<forall>x\<in>convex hull s. \<forall>y\<in>convex hull t. (x, y) \<in> convex hull (s \<times> t)"
  proof (intro hull_induct)
    fix x y assume "x \<in> s" and "y \<in> t"
    then show "(x, y) \<in> convex hull (s \<times> t)"
      by (simp add: hull_inc)
  next
    fix x let ?S = "((\<lambda>y. (0, y)) -` (\<lambda>p. (- x, 0) + p) ` (convex hull s \<times> t))"
    have "convex ?S"
      by (intro convex_linear_vimage convex_translation convex_convex_hull,
        simp add: linear_iff)
    also have "?S = {y. (x, y) \<in> convex hull (s \<times> t)}"
      by (auto simp add: image_def Bex_def)
    finally show "convex {y. (x, y) \<in> convex hull (s \<times> t)}" .
  next
    show "convex {x. \<forall>y\<in>convex hull t. (x, y) \<in> convex hull (s \<times> t)}"
    proof (unfold Collect_ball_eq, rule convex_INT [rule_format])
      fix y let ?S = "((\<lambda>x. (x, 0)) -` (\<lambda>p. (0, - y) + p) ` (convex hull s \<times> t))"
      have "convex ?S"
      by (intro convex_linear_vimage convex_translation convex_convex_hull,
        simp add: linear_iff)
      also have "?S = {x. (x, y) \<in> convex hull (s \<times> t)}"
        by (auto simp add: image_def Bex_def)
      finally show "convex {x. (x, y) \<in> convex hull (s \<times> t)}" .
    qed
  qed
  then show "(convex hull s) \<times> (convex hull t) \<subseteq> convex hull (s \<times> t)"
    unfolding subset_eq split_paired_Ball_Sigma .
qed


subsubsection \<open>Stepping theorems for convex hulls of finite sets\<close>

lemma convex_hull_empty[simp]: "convex hull {} = {}"
  by (rule hull_unique) auto

lemma convex_hull_singleton[simp]: "convex hull {a} = {a}"
  by (rule hull_unique) auto

lemma convex_hull_insert:
  fixes s :: "'a::real_vector set"
  assumes "s \<noteq> {}"
  shows "convex hull (insert a s) =
    {x. \<exists>u\<ge>0. \<exists>v\<ge>0. \<exists>b. (u + v = 1) \<and> b \<in> (convex hull s) \<and> (x = u *\<^sub>R a + v *\<^sub>R b)}"
  (is "_ = ?hull")
  apply (rule, rule hull_minimal, rule)
  unfolding insert_iff
  prefer 3
  apply rule
proof -
  fix x
  assume x: "x = a \<or> x \<in> s"
  then show "x \<in> ?hull"
    apply rule
    unfolding mem_Collect_eq
    apply (rule_tac x=1 in exI)
    defer
    apply (rule_tac x=0 in exI)
    using assms hull_subset[of s convex]
    apply auto
    done
next
  fix x
  assume "x \<in> ?hull"
  then obtain u v b where obt: "u\<ge>0" "v\<ge>0" "u + v = 1" "b \<in> convex hull s" "x = u *\<^sub>R a + v *\<^sub>R b"
    by auto
  have "a \<in> convex hull insert a s" "b \<in> convex hull insert a s"
    using hull_mono[of s "insert a s" convex] hull_mono[of "{a}" "insert a s" convex] and obt(4)
    by auto
  then show "x \<in> convex hull insert a s"
    unfolding obt(5) using obt(1-3)
    by (rule convexD [OF convex_convex_hull])
next
  show "convex ?hull"
  proof (rule convexI)
    fix x y u v
    assume as: "(0::real) \<le> u" "0 \<le> v" "u + v = 1" "x\<in>?hull" "y\<in>?hull"
    from as(4) obtain u1 v1 b1 where
      obt1: "u1\<ge>0" "v1\<ge>0" "u1 + v1 = 1" "b1 \<in> convex hull s" "x = u1 *\<^sub>R a + v1 *\<^sub>R b1"
      by auto
    from as(5) obtain u2 v2 b2 where
      obt2: "u2\<ge>0" "v2\<ge>0" "u2 + v2 = 1" "b2 \<in> convex hull s" "y = u2 *\<^sub>R a + v2 *\<^sub>R b2"
      by auto
    have *: "\<And>(x::'a) s1 s2. x - s1 *\<^sub>R x - s2 *\<^sub>R x = ((1::real) - (s1 + s2)) *\<^sub>R x"
      by (auto simp add: algebra_simps)
    have **: "\<exists>b \<in> convex hull s. u *\<^sub>R x + v *\<^sub>R y =
      (u * u1) *\<^sub>R a + (v * u2) *\<^sub>R a + (b - (u * u1) *\<^sub>R b - (v * u2) *\<^sub>R b)"
    proof (cases "u * v1 + v * v2 = 0")
      case True
      have *: "\<And>(x::'a) s1 s2. x - s1 *\<^sub>R x - s2 *\<^sub>R x = ((1::real) - (s1 + s2)) *\<^sub>R x"
        by (auto simp add: algebra_simps)
      from True have ***: "u * v1 = 0" "v * v2 = 0"
        using mult_nonneg_nonneg[OF \<open>u\<ge>0\<close> \<open>v1\<ge>0\<close>] mult_nonneg_nonneg[OF \<open>v\<ge>0\<close> \<open>v2\<ge>0\<close>]
        by arith+
      then have "u * u1 + v * u2 = 1"
        using as(3) obt1(3) obt2(3) by auto
      then show ?thesis
        unfolding obt1(5) obt2(5) *
        using assms hull_subset[of s convex]
        by (auto simp add: *** scaleR_right_distrib)
    next
      case False
      have "1 - (u * u1 + v * u2) = (u + v) - (u * u1 + v * u2)"
        using as(3) obt1(3) obt2(3) by (auto simp add: field_simps)
      also have "\<dots> = u * (v1 + u1 - u1) + v * (v2 + u2 - u2)"
        using as(3) obt1(3) obt2(3) by (auto simp add: field_simps)
      also have "\<dots> = u * v1 + v * v2"
        by simp
      finally have **:"1 - (u * u1 + v * u2) = u * v1 + v * v2" by auto
      have "0 \<le> u * v1 + v * v2" "0 \<le> u * v1" "0 \<le> u * v1 + v * v2" "0 \<le> v * v2"
        using as(1,2) obt1(1,2) obt2(1,2) by auto
      then show ?thesis
        unfolding obt1(5) obt2(5)
        unfolding * and **
        using False
        apply (rule_tac
          x = "((u * v1) / (u * v1 + v * v2)) *\<^sub>R b1 + ((v * v2) / (u * v1 + v * v2)) *\<^sub>R b2" in bexI)
        defer
        apply (rule convexD [OF convex_convex_hull])
        using obt1(4) obt2(4)
        unfolding add_divide_distrib[symmetric] and zero_le_divide_iff
        apply (auto simp add: scaleR_left_distrib scaleR_right_distrib)
        done
    qed
    have u1: "u1 \<le> 1"
      unfolding obt1(3)[symmetric] and not_le using obt1(2) by auto
    have u2: "u2 \<le> 1"
      unfolding obt2(3)[symmetric] and not_le using obt2(2) by auto
    have "u1 * u + u2 * v \<le> max u1 u2 * u + max u1 u2 * v"
      apply (rule add_mono)
      apply (rule_tac [!] mult_right_mono)
      using as(1,2) obt1(1,2) obt2(1,2)
      apply auto
      done
    also have "\<dots> \<le> 1"
      unfolding distrib_left[symmetric] and as(3) using u1 u2 by auto
    finally show "u *\<^sub>R x + v *\<^sub>R y \<in> ?hull"
      unfolding mem_Collect_eq
      apply (rule_tac x="u * u1 + v * u2" in exI)
      apply (rule conjI)
      defer
      apply (rule_tac x="1 - u * u1 - v * u2" in exI)
      unfolding Bex_def
      using as(1,2) obt1(1,2) obt2(1,2) **
      apply (auto simp add: algebra_simps)
      done
  qed
qed

lemma convex_hull_insert_alt:
   "convex hull (insert a S) =
      (if S = {} then {a}
      else {(1 - u) *\<^sub>R a + u *\<^sub>R x |x u. 0 \<le> u \<and> u \<le> 1 \<and> x \<in> convex hull S})"
  apply (auto simp: convex_hull_insert)
  using diff_eq_eq apply fastforce
  by (metis add.group_left_neutral add_le_imp_le_diff diff_add_cancel)

subsubsection \<open>Explicit expression for convex hull\<close>

lemma convex_hull_indexed:
  fixes s :: "'a::real_vector set"
  shows "convex hull s =
    {y. \<exists>k u x.
      (\<forall>i\<in>{1::nat .. k}. 0 \<le> u i \<and> x i \<in> s) \<and>
      (sum u {1..k} = 1) \<and> (sum (\<lambda>i. u i *\<^sub>R x i) {1..k} = y)}"
  (is "?xyz = ?hull")
  apply (rule hull_unique)
  apply rule
  defer
  apply (rule convexI)
proof -
  fix x
  assume "x\<in>s"
  then show "x \<in> ?hull"
    unfolding mem_Collect_eq
    apply (rule_tac x=1 in exI, rule_tac x="\<lambda>x. 1" in exI)
    apply auto
    done
next
  fix t
  assume as: "s \<subseteq> t" "convex t"
  show "?hull \<subseteq> t"
    apply rule
    unfolding mem_Collect_eq
    apply (elim exE conjE)
  proof -
    fix x k u y
    assume assm:
      "\<forall>i\<in>{1::nat..k}. 0 \<le> u i \<and> y i \<in> s"
      "sum u {1..k} = 1" "(\<Sum>i = 1..k. u i *\<^sub>R y i) = x"
    show "x\<in>t"
      unfolding assm(3) [symmetric]
      apply (rule as(2)[unfolded convex, rule_format])
      using assm(1,2) as(1) apply auto
      done
  qed
next
  fix x y u v
  assume uv: "0 \<le> u" "0 \<le> v" "u + v = (1::real)"
  assume xy: "x \<in> ?hull" "y \<in> ?hull"
  from xy obtain k1 u1 x1 where
    x: "\<forall>i\<in>{1::nat..k1}. 0\<le>u1 i \<and> x1 i \<in> s" "sum u1 {Suc 0..k1} = 1" "(\<Sum>i = Suc 0..k1. u1 i *\<^sub>R x1 i) = x"
    by auto
  from xy obtain k2 u2 x2 where
    y: "\<forall>i\<in>{1::nat..k2}. 0\<le>u2 i \<and> x2 i \<in> s" "sum u2 {Suc 0..k2} = 1" "(\<Sum>i = Suc 0..k2. u2 i *\<^sub>R x2 i) = y"
    by auto
  have *: "\<And>P (x1::'a) x2 s1 s2 i.
    (if P i then s1 else s2) *\<^sub>R (if P i then x1 else x2) = (if P i then s1 *\<^sub>R x1 else s2 *\<^sub>R x2)"
    "{1..k1 + k2} \<inter> {1..k1} = {1..k1}" "{1..k1 + k2} \<inter> - {1..k1} = (\<lambda>i. i + k1) ` {1..k2}"
    prefer 3
    apply (rule, rule)
    unfolding image_iff
    apply (rule_tac x = "x - k1" in bexI)
    apply (auto simp add: not_le)
    done
  have inj: "inj_on (\<lambda>i. i + k1) {1..k2}"
    unfolding inj_on_def by auto
  show "u *\<^sub>R x + v *\<^sub>R y \<in> ?hull"
    apply rule
    apply (rule_tac x="k1 + k2" in exI)
    apply (rule_tac x="\<lambda>i. if i \<in> {1..k1} then u * u1 i else v * u2 (i - k1)" in exI)
    apply (rule_tac x="\<lambda>i. if i \<in> {1..k1} then x1 i else x2 (i - k1)" in exI)
    apply (rule, rule)
    defer
    apply rule
    unfolding * and sum.If_cases[OF finite_atLeastAtMost[of 1 "k1 + k2"]] and
      sum.reindex[OF inj] and o_def Collect_mem_eq
    unfolding scaleR_scaleR[symmetric] scaleR_right.sum [symmetric] sum_distrib_left[symmetric]
  proof -
    fix i
    assume i: "i \<in> {1..k1+k2}"
    show "0 \<le> (if i \<in> {1..k1} then u * u1 i else v * u2 (i - k1)) \<and>
      (if i \<in> {1..k1} then x1 i else x2 (i - k1)) \<in> s"
    proof (cases "i\<in>{1..k1}")
      case True
      then show ?thesis
        using uv(1) x(1)[THEN bspec[where x=i]] by auto
    next
      case False
      define j where "j = i - k1"
      from i False have "j \<in> {1..k2}"
        unfolding j_def by auto
      then show ?thesis
        using False uv(2) y(1)[THEN bspec[where x=j]]
        by (auto simp: j_def[symmetric])
    qed
  qed (auto simp add: not_le x(2,3) y(2,3) uv(3))
qed

lemma convex_hull_finite:
  fixes s :: "'a::real_vector set"
  assumes "finite s"
  shows "convex hull s = {y. \<exists>u. (\<forall>x\<in>s. 0 \<le> u x) \<and>
    sum u s = 1 \<and> sum (\<lambda>x. u x *\<^sub>R x) s = y}"
  (is "?HULL = ?set")
proof (rule hull_unique, auto simp add: convex_def[of ?set])
  fix x
  assume "x \<in> s"
  then show "\<exists>u. (\<forall>x\<in>s. 0 \<le> u x) \<and> sum u s = 1 \<and> (\<Sum>x\<in>s. u x *\<^sub>R x) = x"
    apply (rule_tac x="\<lambda>y. if x=y then 1 else 0" in exI)
    apply auto
    unfolding sum.delta'[OF assms] and sum_delta''[OF assms]
    apply auto
    done
next
  fix u v :: real
  assume uv: "0 \<le> u" "0 \<le> v" "u + v = 1"
  fix ux assume ux: "\<forall>x\<in>s. 0 \<le> ux x" "sum ux s = (1::real)"
  fix uy assume uy: "\<forall>x\<in>s. 0 \<le> uy x" "sum uy s = (1::real)"
  {
    fix x
    assume "x\<in>s"
    then have "0 \<le> u * ux x + v * uy x"
      using ux(1)[THEN bspec[where x=x]] uy(1)[THEN bspec[where x=x]] and uv(1,2)
      by auto
  }
  moreover
  have "(\<Sum>x\<in>s. u * ux x + v * uy x) = 1"
    unfolding sum.distrib and sum_distrib_left[symmetric] and ux(2) uy(2)
    using uv(3) by auto
  moreover
  have "(\<Sum>x\<in>s. (u * ux x + v * uy x) *\<^sub>R x) = u *\<^sub>R (\<Sum>x\<in>s. ux x *\<^sub>R x) + v *\<^sub>R (\<Sum>x\<in>s. uy x *\<^sub>R x)"
    unfolding scaleR_left_distrib and sum.distrib and scaleR_scaleR[symmetric]
      and scaleR_right.sum [symmetric]
    by auto
  ultimately
  show "\<exists>uc. (\<forall>x\<in>s. 0 \<le> uc x) \<and> sum uc s = 1 \<and>
      (\<Sum>x\<in>s. uc x *\<^sub>R x) = u *\<^sub>R (\<Sum>x\<in>s. ux x *\<^sub>R x) + v *\<^sub>R (\<Sum>x\<in>s. uy x *\<^sub>R x)"
    apply (rule_tac x="\<lambda>x. u * ux x + v * uy x" in exI)
    apply auto
    done
next
  fix t
  assume t: "s \<subseteq> t" "convex t"
  fix u
  assume u: "\<forall>x\<in>s. 0 \<le> u x" "sum u s = (1::real)"
  then show "(\<Sum>x\<in>s. u x *\<^sub>R x) \<in> t"
    using t(2)[unfolded convex_explicit, THEN spec[where x=s], THEN spec[where x=u]]
    using assms and t(1) by auto
qed


subsubsection \<open>Another formulation from Lars Schewe\<close>

lemma convex_hull_explicit:
  fixes p :: "'a::real_vector set"
  shows "convex hull p =
    {y. \<exists>s u. finite s \<and> s \<subseteq> p \<and> (\<forall>x\<in>s. 0 \<le> u x) \<and> sum u s = 1 \<and> sum (\<lambda>v. u v *\<^sub>R v) s = y}"
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
    have "\<exists>s u. finite s \<and> s \<subseteq> p \<and> (\<forall>x\<in>s. 0 \<le> u x) \<and> sum u s = 1 \<and> (\<Sum>v\<in>s. u v *\<^sub>R v) = x"
      apply (rule_tac x="y ` {1..k}" in exI)
      apply (rule_tac x="\<lambda>v. sum u {i\<in>{1..k}. y i = v}" in exI)
      apply auto
      done
    then have "x\<in>?rhs" by auto
  }
  moreover
  {
    fix y
    assume "y\<in>?rhs"
    then obtain s u where
      obt: "finite s" "s \<subseteq> p" "\<forall>x\<in>s. 0 \<le> u x" "sum u s = 1" "(\<Sum>v\<in>s. u v *\<^sub>R v) = y"
      by auto

    obtain f where f: "inj_on f {1..card s}" "f ` {1..card s} = s"
      using ex_bij_betw_nat_finite_1[OF obt(1)] unfolding bij_betw_def by auto

    {
      fix i :: nat
      assume "i\<in>{1..card s}"
      then have "f i \<in> s"
        apply (subst f(2)[symmetric])
        apply auto
        done
      then have "0 \<le> u (f i)" "f i \<in> p" using obt(2,3) by auto
    }
    moreover have *: "finite {1..card s}" by auto
    {
      fix y
      assume "y\<in>s"
      then obtain i where "i\<in>{1..card s}" "f i = y"
        using f using image_iff[of y f "{1..card s}"]
        by auto
      then have "{x. Suc 0 \<le> x \<and> x \<le> card s \<and> f x = y} = {i}"
        apply auto
        using f(1)[unfolded inj_on_def]
        apply(erule_tac x=x in ballE)
        apply auto
        done
      then have "card {x. Suc 0 \<le> x \<and> x \<le> card s \<and> f x = y} = 1" by auto
      then have "(\<Sum>x\<in>{x \<in> {1..card s}. f x = y}. u (f x)) = u y"
          "(\<Sum>x\<in>{x \<in> {1..card s}. f x = y}. u (f x) *\<^sub>R f x) = u y *\<^sub>R y"
        by (auto simp add: sum_constant_scaleR)
    }
    then have "(\<Sum>x = 1..card s. u (f x)) = 1" "(\<Sum>i = 1..card s. u (f i) *\<^sub>R f i) = y"
      unfolding sum_image_gen[OF *(1), of "\<lambda>x. u (f x) *\<^sub>R f x" f]
        and sum_image_gen[OF *(1), of "\<lambda>x. u (f x)" f]
      unfolding f
      using sum.cong [of s s "\<lambda>y. (\<Sum>x\<in>{x \<in> {1..card s}. f x = y}. u (f x) *\<^sub>R f x)" "\<lambda>v. u v *\<^sub>R v"]
      using sum.cong [of s s "\<lambda>y. (\<Sum>x\<in>{x \<in> {1..card s}. f x = y}. u (f x))" u]
      unfolding obt(4,5)
      by auto
    ultimately
    have "\<exists>k u x. (\<forall>i\<in>{1..k}. 0 \<le> u i \<and> x i \<in> p) \<and> sum u {1..k} = 1 \<and>
        (\<Sum>i::nat = 1..k. u i *\<^sub>R x i) = y"
      apply (rule_tac x="card s" in exI)
      apply (rule_tac x="u \<circ> f" in exI)
      apply (rule_tac x=f in exI)
      apply fastforce
      done
    then have "y \<in> ?lhs"
      unfolding convex_hull_indexed by auto
  }
  ultimately show ?thesis
    unfolding set_eq_iff by blast
qed


subsubsection \<open>A stepping theorem for that expansion\<close>

lemma convex_hull_finite_step:
  fixes s :: "'a::real_vector set"
  assumes "finite s"
  shows
    "(\<exists>u. (\<forall>x\<in>insert a s. 0 \<le> u x) \<and> sum u (insert a s) = w \<and> sum (\<lambda>x. u x *\<^sub>R x) (insert a s) = y)
      \<longleftrightarrow> (\<exists>v\<ge>0. \<exists>u. (\<forall>x\<in>s. 0 \<le> u x) \<and> sum u s = w - v \<and> sum (\<lambda>x. u x *\<^sub>R x) s = y - v *\<^sub>R a)"
  (is "?lhs = ?rhs")
proof (rule, case_tac[!] "a\<in>s")
  assume "a \<in> s"
  then have *: "insert a s = s" by auto
  assume ?lhs
  then show ?rhs
    unfolding *
    apply (rule_tac x=0 in exI)
    apply auto
    done
next
  assume ?lhs
  then obtain u where
      u: "\<forall>x\<in>insert a s. 0 \<le> u x" "sum u (insert a s) = w" "(\<Sum>x\<in>insert a s. u x *\<^sub>R x) = y"
    by auto
  assume "a \<notin> s"
  then show ?rhs
    apply (rule_tac x="u a" in exI)
    using u(1)[THEN bspec[where x=a]]
    apply simp
    apply (rule_tac x=u in exI)
    using u[unfolded sum_clauses(2)[OF assms]] and \<open>a\<notin>s\<close>
    apply auto
    done
next
  assume "a \<in> s"
  then have *: "insert a s = s" by auto
  have fin: "finite (insert a s)" using assms by auto
  assume ?rhs
  then obtain v u where uv: "v\<ge>0" "\<forall>x\<in>s. 0 \<le> u x" "sum u s = w - v" "(\<Sum>x\<in>s. u x *\<^sub>R x) = y - v *\<^sub>R a"
    by auto
  show ?lhs
    apply (rule_tac x = "\<lambda>x. (if a = x then v else 0) + u x" in exI)
    unfolding scaleR_left_distrib and sum.distrib and sum_delta''[OF fin] and sum.delta'[OF fin]
    unfolding sum_clauses(2)[OF assms]
    using uv and uv(2)[THEN bspec[where x=a]] and \<open>a\<in>s\<close>
    apply auto
    done
next
  assume ?rhs
  then obtain v u where
    uv: "v\<ge>0" "\<forall>x\<in>s. 0 \<le> u x" "sum u s = w - v" "(\<Sum>x\<in>s. u x *\<^sub>R x) = y - v *\<^sub>R a"
    by auto
  moreover
  assume "a \<notin> s"
  moreover
  have "(\<Sum>x\<in>s. if a = x then v else u x) = sum u s"
    and "(\<Sum>x\<in>s. (if a = x then v else u x) *\<^sub>R x) = (\<Sum>x\<in>s. u x *\<^sub>R x)"
    apply (rule_tac sum.cong) apply rule
    defer
    apply (rule_tac sum.cong) apply rule
    using \<open>a \<notin> s\<close>
    apply auto
    done
  ultimately show ?lhs
    apply (rule_tac x="\<lambda>x. if a = x then v else u x" in exI)
    unfolding sum_clauses(2)[OF assms]
    apply auto
    done
qed


subsubsection \<open>Hence some special cases\<close>

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
    apply (rule_tac x="1 - v" in exI)
    apply simp
    apply (rule_tac x=u in exI)
    apply simp
    apply (rule_tac x="\<lambda>x. v" in exI)
    apply simp
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
    apply (auto simp add: algebra_simps)
    done
qed

lemma convex_hull_3:
  "convex hull {a,b,c} = { u *\<^sub>R a + v *\<^sub>R b + w *\<^sub>R c | u v w. 0 \<le> u \<and> 0 \<le> v \<and> 0 \<le> w \<and> u + v + w = 1}"
proof -
  have fin: "finite {a,b,c}" "finite {b,c}" "finite {c}"
    by auto
  have *: "\<And>x y z ::real. x + y + z = 1 \<longleftrightarrow> x = 1 - y - z"
    by (auto simp add: field_simps)
  show ?thesis
    unfolding convex_hull_finite[OF fin(1)] and convex_hull_finite_step[OF fin(2)] and *
    unfolding convex_hull_finite_step[OF fin(3)]
    apply (rule Collect_cong)
    apply simp
    apply auto
    apply (rule_tac x=va in exI)
    apply (rule_tac x="u c" in exI)
    apply simp
    apply (rule_tac x="1 - v - w" in exI)
    apply simp
    apply (rule_tac x=v in exI)
    apply simp
    apply (rule_tac x="\<lambda>x. w" in exI)
    apply simp
    done
qed

lemma convex_hull_3_alt:
  "convex hull {a,b,c} = {a + u *\<^sub>R (b - a) + v *\<^sub>R (c - a) | u v.  0 \<le> u \<and> 0 \<le> v \<and> u + v \<le> 1}"
proof -
  have *: "\<And>x y z ::real. x + y + z = 1 \<longleftrightarrow> x = 1 - y - z"
    by auto
  show ?thesis
    unfolding convex_hull_3
    apply (auto simp add: *)
    apply (rule_tac x=v in exI)
    apply (rule_tac x=w in exI)
    apply (simp add: algebra_simps)
    apply (rule_tac x=u in exI)
    apply (rule_tac x=v in exI)
    apply (simp add: algebra_simps)
    done
qed


subsection \<open>Relations among closure notions and corresponding hulls\<close>

lemma affine_imp_convex: "affine s \<Longrightarrow> convex s"
  unfolding affine_def convex_def by auto

lemma convex_affine_hull [simp]: "convex (affine hull S)"
  by (simp add: affine_imp_convex)

lemma subspace_imp_convex: "subspace s \<Longrightarrow> convex s"
  using subspace_imp_affine affine_imp_convex by auto

lemma affine_hull_subset_span: "(affine hull s) \<subseteq> (span s)"
  by (metis hull_minimal span_inc subspace_imp_affine subspace_span)

lemma convex_hull_subset_span: "(convex hull s) \<subseteq> (span s)"
  by (metis hull_minimal span_inc subspace_imp_convex subspace_span)

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
    unfolding sum_clauses(2)[OF fin]
    using \<open>a\<notin>s\<close> \<open>t\<subseteq>s\<close>
    apply auto
    unfolding *
    apply auto
    done
  moreover have "\<exists>v\<in>insert a t. (if v = a then - (\<Sum>x\<in>t. u (x - a)) else u (v - a)) \<noteq> 0"
    apply (rule_tac x="v + a" in bexI)
    using obt(3,4) and \<open>0\<notin>S\<close>
    unfolding t_def
    apply auto
    done
  moreover have *: "\<And>P Q. (\<Sum>x\<in>t. (if x = a then P x else Q x) *\<^sub>R x) = (\<Sum>x\<in>t. Q x *\<^sub>R x)"
    apply (rule sum.cong)
    using \<open>a\<notin>s\<close> \<open>t\<subseteq>s\<close>
    apply auto
    done
  have "(\<Sum>x\<in>t. u (x - a)) *\<^sub>R a = (\<Sum>v\<in>t. u (v - a) *\<^sub>R v)"
    unfolding scaleR_left.sum
    unfolding t_def and sum.reindex[OF inj] and o_def
    using obt(5)
    by (auto simp add: sum.distrib scaleR_right_distrib)
  then have "(\<Sum>v\<in>insert a t. (if v = a then - (\<Sum>x\<in>t. u (x - a)) else u (v - a)) *\<^sub>R v) = 0"
    unfolding sum_clauses(2)[OF fin]
    using \<open>a\<notin>s\<close> \<open>t\<subseteq>s\<close>
    by (auto simp add: *)
  ultimately show ?thesis
    unfolding affine_dependent_explicit
    apply (rule_tac x="insert a t" in exI)
    apply auto
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
      apply (erule_tac x="1/2" in allE)
      apply simp
      apply (erule_tac x="1/2" in allE)
      apply auto
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
    unfolding *
    apply (rule card_image)
    unfolding inj_on_def
    apply auto
    done
  also have "\<dots> > DIM('a)" using assms(2)
    unfolding card_Diff_singleton[OF assms(1) \<open>a\<in>s\<close>] by auto
  finally show ?thesis
    apply (subst insert_Diff[OF \<open>a\<in>s\<close>, symmetric])
    apply (rule dependent_imp_affine_dependent)
    apply (rule dependent_biggerset)
    apply auto
    done
qed

lemma affine_dependent_biggerset_general:
  assumes "finite (s :: 'a::euclidean_space set)"
    and "card s \<ge> dim s + 2"
  shows "affine_dependent s"
proof -
  from assms(2) have "s \<noteq> {}" by auto
  then obtain a where "a\<in>s" by auto
  have *: "{x - a |x. x \<in> s - {a}} = (\<lambda>x. x - a) ` (s - {a})"
    by auto
  have **: "card {x - a |x. x \<in> s - {a}} = card (s - {a})"
    unfolding *
    apply (rule card_image)
    unfolding inj_on_def
    apply auto
    done
  have "dim {x - a |x. x \<in> s - {a}} \<le> dim s"
    apply (rule subset_le_dim)
    unfolding subset_eq
    using \<open>a\<in>s\<close>
    apply (auto simp add:span_superset span_diff)
    done
  also have "\<dots> < dim s + 1" by auto
  also have "\<dots> \<le> card (s - {a})"
    using assms
    using card_Diff_singleton[OF assms(1) \<open>a\<in>s\<close>]
    by auto
  finally show ?thesis
    apply (subst insert_Diff[OF \<open>a\<in>s\<close>, symmetric])
    apply (rule dependent_imp_affine_dependent)
    apply (rule dependent_biggerset_general)
    unfolding **
    apply auto
    done
qed


subsection \<open>Some Properties of Affine Dependent Sets\<close>

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
  have "op + a ` (S - {x}) = op + a ` S - {a + x}"
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
  have "(op + (- a) ` S) = {x - a| x . x : S}" by auto
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
      using span_insert_0[of "op + (- a) ` (s - {a})"] by (auto simp del: uminus_add_conv_diff)
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
  then obtain B where B:
    "(\<lambda>x. -a+x) ` (S - {a}) \<subseteq> B \<and> B \<subseteq> (\<lambda>x. -a+x) ` V \<and> independent B \<and> (\<lambda>x. -a+x) ` V \<subseteq> span B"
     using maximal_independent_subset_extend[of "(\<lambda>x. -a+x) ` (S-{a})" "(\<lambda>x. -a + x) ` V"] assms
     by blast
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

definition aff_dim :: "('a::euclidean_space) set \<Rightarrow> int"
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
    apply (rule exI[of _ "B"])
    apply auto
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
       apply (rule card_image)
       using translate_inj_on
       apply (auto simp del: uminus_add_conv_diff)
       done
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

lemma independent_finite:
  fixes B :: "'n::euclidean_space set"
  assumes "independent B"
  shows "finite B"
  using affine_dependent_imp_dependent[of B] aff_independent_finite[of B] assms
  by auto

lemma subspace_dim_equal:
  assumes "subspace (S :: ('n::euclidean_space) set)"
    and "subspace T"
    and "S \<subseteq> T"
    and "dim S \<ge> dim T"
  shows "S = T"
proof -
  obtain B where B: "B \<le> S" "independent B \<and> S \<subseteq> span B" "card B = dim S"
    using basis_exists[of S] by auto
  then have "span B \<subseteq> S"
    using span_mono[of B S] span_eq[of S] assms by metis
  then have "span B = S"
    using B by auto
  have "dim S = dim T"
    using assms dim_subset[of S T] by auto
  then have "T \<subseteq> span B"
    using card_eq_dim[of B T] B independent_finite assms by auto
  then show ?thesis
    using assms \<open>span B = S\<close> by auto
qed

corollary dim_eq_span:
  fixes S :: "'a::euclidean_space set"
  shows "\<lbrakk>S \<subseteq> T; dim T \<le> dim S\<rbrakk> \<Longrightarrow> span S = span T"
by (simp add: span_mono subspace_dim_equal subspace_span)

lemma dim_eq_full:
    fixes S :: "'a :: euclidean_space set"
    shows "dim S = DIM('a) \<longleftrightarrow> span S = UNIV"
apply (rule iffI)
 apply (metis dim_eq_span dim_subset_UNIV span_Basis span_span subset_UNIV)
by (metis dim_UNIV dim_span)

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
    using span_mono[of d "?B"] span_eq[of "?B"] by blast
  moreover have *: "card d \<le> dim (span d)"
    using independent_card_le_dim[of d "span d"] independent_substdbasis[OF assms] span_inc[of d]
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
    using dim_unique[of B B "card B"] assms span_inc[of B] by auto
  have "dim B \<le> card (Basis :: 'a set)"
    using dim_subset_UNIV[of B] by simp
  from ex_card[OF this] obtain d :: "'a set" where d: "d \<subseteq> Basis" and t: "card d = dim B"
    by auto
  let ?t = "{x::'a::euclidean_space. \<forall>i\<in>Basis. i \<notin> d \<longrightarrow> x\<bullet>i = 0}"
  have "\<exists>f. linear f \<and> f ` B = d \<and> f ` span B = ?t \<and> inj_on f (span B)"
    apply (rule basis_to_basis_subspace_isomorphism[of "span B" ?t B "d"])
    apply (rule subspace_span)
    apply (rule subspace_substandard)
    defer
    apply (rule span_inc)
    apply (rule assms)
    defer
    unfolding dim_span[of B]
    apply(rule B)
    unfolding span_substd_basis[OF d, symmetric]
    apply (rule span_inc)
    apply (rule independent_substdbasis[OF d])
    apply rule
    apply assumption
    unfolding t[symmetric] span_substd_basis[OF d] dim_substandard[OF d]
    apply auto
    done
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
  also have "... = 1"
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

lemma affine_independent_card_dim_diffs:
  fixes S :: "'a :: euclidean_space set"
  assumes "~ affine_dependent S" "a \<in> S"
    shows "card S = dim {x - a|x. x \<in> S} + 1"
proof -
  have 1: "{b - a|b. b \<in> (S - {a})} \<subseteq> {x - a|x. x \<in> S}" by auto
  have 2: "x - a \<in> span {b - a |b. b \<in> S - {a}}" if "x \<in> S" for x
  proof (cases "x = a")
    case True then show ?thesis by simp
  next
    case False then show ?thesis
      using assms by (blast intro: span_superset that)
  qed
  have "\<not> affine_dependent (insert a S)"
    by (simp add: assms insert_absorb)
  then have 3: "independent {b - a |b. b \<in> S - {a}}"
      using dependent_imp_affine_dependent by fastforce
  have "{b - a |b. b \<in> S - {a}} = (\<lambda>b. b-a) ` (S - {a})"
    by blast
  then have "card {b - a |b. b \<in> S - {a}} = card ((\<lambda>b. b-a) ` (S - {a}))"
    by simp
  also have "... = card (S - {a})"
    by (metis (no_types, lifting) card_image diff_add_cancel inj_onI)
  also have "... = card S - 1"
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
          aff_dim_subset[of "op + a ` cball 0 e" "cball a e"]
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


subsection \<open>Caratheodory's theorem.\<close>

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
    apply (rule_tac ex_least_nat_le)
    apply auto
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
        apply (rule_tac sum_nonneg)
        apply auto
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
      apply (auto simp add: * scaleR_left_distrib)
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
    apply (subst convex_hull_caratheodory_aff_dim)
    apply clarify
    apply (rule_tac x="s" in exI)
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
    by (auto simp add: convex_hull_explicit)
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

definition "rel_interior S =
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
  by (auto simp add: rel_interior)

lemma mem_rel_interior_ball:
  "x \<in> rel_interior S \<longleftrightarrow> x \<in> S \<and> (\<exists>e. e > 0 \<and> ball x e \<inter> affine hull S \<subseteq> S)"
  apply (simp add: rel_interior, safe)
  apply (force simp add: open_contains_ball)
  apply (rule_tac x = "ball x e" in exI)
  apply simp
  done

lemma rel_interior_ball:
  "rel_interior S = {x \<in> S. \<exists>e. e > 0 \<and> ball x e \<inter> affine hull S \<subseteq> S}"
  using mem_rel_interior_ball [of _ S] by auto

lemma mem_rel_interior_cball:
  "x \<in> rel_interior S \<longleftrightarrow> x \<in> S \<and> (\<exists>e. e > 0 \<and> cball x e \<inter> affine hull S \<subseteq> S)"
  apply (simp add: rel_interior, safe)
  apply (force simp add: open_contains_cball)
  apply (rule_tac x = "ball x e" in exI)
  apply (simp add: subset_trans [OF ball_subset_cball])
  apply auto
  done

lemma rel_interior_cball:
  "rel_interior S = {x \<in> S. \<exists>e. e > 0 \<and> cball x e \<inter> affine hull S \<subseteq> S}"
  using mem_rel_interior_cball [of _ S] by auto

lemma rel_interior_empty [simp]: "rel_interior {} = {}"
   by (auto simp add: rel_interior_def)

lemma affine_hull_sing [simp]: "affine hull {a :: 'n::euclidean_space} = {a}"
  by (metis affine_hull_eq affine_sing)

lemma rel_interior_sing [simp]:
    fixes a :: "'n::euclidean_space"  shows "rel_interior {a} = {a}"
  apply (auto simp: rel_interior_ball)
  apply (rule_tac x=1 in exI)
  apply force
  done

lemma subset_rel_interior:
  fixes S T :: "'n::euclidean_space set"
  assumes "S \<subseteq> T"
    and "affine hull S = affine hull T"
  shows "rel_interior S \<subseteq> rel_interior T"
  using assms by (auto simp add: rel_interior_def)

lemma rel_interior_subset: "rel_interior S \<subseteq> S"
  by (auto simp add: rel_interior_def)

lemma rel_interior_subset_closure: "rel_interior S \<subseteq> closure S"
  using rel_interior_subset by (auto simp add: closure_def)

lemma interior_subset_rel_interior: "interior S \<subseteq> rel_interior S"
  by (auto simp add: rel_interior interior_def)

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
      using \<open>e > 0\<close> by (auto simp add: scaleR_left_diff_distrib scaleR_right_diff_distrib)
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
      apply (auto simp add: euclidean_eq_iff[where 'a='a] field_simps inner_simps)
      done
    also have "\<dots> = \<bar>1/e\<bar> * norm (x - e *\<^sub>R (x - c) - y)"
      by (auto intro!:arg_cong[where f=norm] simp add: algebra_simps)
    also have "\<dots> < d"
      using as[unfolded dist_norm] and \<open>e > 0\<close>
      by (auto simp add:pos_divide_less_eq[OF \<open>e > 0\<close>] mult.commute)
    finally have "y \<in> S"
      apply (subst *)
      apply (rule assms(1)[unfolded convex_alt,rule_format])
      apply (rule d[unfolded subset_eq,rule_format])
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
      apply (auto simp add: dist_norm)
      done
  }
  moreover
  {
    fix y
    assume "y \<in> interior {a..}"
    then obtain e where e: "e > 0" "cball y e \<subseteq> {a..}"
      using mem_interior_cball[of y "{a..}"] by auto
    moreover from e have "y - e \<in> cball y e"
      by (auto simp add: cball_def dist_norm)
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
      apply (auto simp add: dist_norm)
      done
  }
  moreover
  {
    fix y
    assume "y \<in> interior {..a}"
    then obtain e where e: "e > 0" "cball y e \<subseteq> {..a}"
      using mem_interior_cball[of y "{..a}"] by auto
    moreover from e have "y + e \<in> cball y e"
      by (auto simp add: cball_def dist_norm)
    ultimately have "a \<ge> y + e" by auto
    then have "a > y" using e by auto
  }
  ultimately show ?thesis by auto
qed

lemma interior_atLeastAtMost_real [simp]: "interior {a..b} = {a<..<b :: real}"
proof-
  have "{a..b} = {a..} \<inter> {..b}" by auto
  also have "interior ... = {a<..} \<inter> {..<b}"
    by (simp add: interior_real_semiline interior_real_semiline')
  also have "... = {a<..<b}" by auto
  finally show ?thesis .
qed

lemma interior_greaterThanLessThan_real [simp]: "interior {a<..<b} = {a<..<b :: real}"
  by (metis interior_atLeastAtMost_real interior_interior)

lemma frontier_real_Iic [simp]:
  fixes a :: real
  shows "frontier {..a} = {a}"
  unfolding frontier_def by (auto simp add: interior_real_semiline')

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

definition "rel_open S \<longleftrightarrow> rel_interior S = S"

lemma rel_open: "rel_open S \<longleftrightarrow> openin (subtopology euclidean (affine hull S)) S"
  unfolding rel_open_def rel_interior_def
  apply auto
  using openin_subopen[of "subtopology euclidean (affine hull S)" S]
  apply auto
  done

lemma openin_rel_interior: "openin (subtopology euclidean (affine hull S)) (rel_interior S)"
  apply (simp add: rel_interior_def)
  apply (subst openin_subopen)
  apply blast
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
    then obtain a where a: "S = (op + a ` L)"
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
      apply (rule_tac bexI[where x=x])
      apply (auto)
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
        using \<open>e \<le> 1\<close> \<open>e > 0\<close> \<open>d > 0\<close> by (auto)
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
    by (auto simp add: scaleR_right_diff_distrib scaleR_right_distrib scaleR_left_diff_distrib)
  have zball: "z \<in> ball c d"
    using mem_ball z_def dist_norm[of c]
    using y and assms(4,5)
    by (auto simp add:field_simps norm_minus_commute)
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
    by (auto simp add: field_simps)
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


subsubsection\<open>Relative interior preserves under linear transformations\<close>

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
    using translation_inverse_subset[of a "rel_interior (op + a ` S)" "rel_interior S"]
    by auto
  then show ?thesis
    using rel_interior_translation_aux[of a S] by auto
qed


lemma affine_hull_linear_image:
  assumes "bounded_linear f"
  shows "f ` (affine hull s) = affine hull f ` s"
  apply rule
  unfolding subset_eq ball_simps
  apply (rule_tac[!] hull_induct, rule hull_inc)
  prefer 3
  apply (erule imageE)
  apply (rule_tac x=xa in image_eqI)
  apply assumption
  apply (rule hull_subset[unfolded subset_eq, rule_format])
  apply assumption
proof -
  interpret f: bounded_linear f by fact
  show "affine {x. f x \<in> affine hull f ` s}"
    unfolding affine_def
    by (auto simp add: f.scaleR f.add affine_affine_hull[unfolded affine_def, rule_format])
  show "affine {x. x \<in> f ` (affine hull s)}"
    using affine_affine_hull[unfolded affine_def, of s]
    unfolding affine_def by (auto simp add: f.scaleR [symmetric] f.add [symmetric])
qed auto


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
        by (metis Int_iff span_inc subsetCE)
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
          affine_hull_subset_span[of S] span_inc
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


subsection\<open>Some Properties of subset of standard basis\<close>

lemma affine_hull_substd_basis:
  assumes "d \<subseteq> Basis"
  shows "affine hull (insert 0 d) = {x::'a::euclidean_space. \<forall>i\<in>Basis. i \<notin> d \<longrightarrow> x\<bullet>i = 0}"
  (is "affine hull (insert 0 ?A) = ?B")
proof -
  have *: "\<And>A. op + (0::'a) ` A = A" "\<And>A. op + (- (0::'a)) ` A = A"
    by auto
  show ?thesis
    unfolding affine_hull_insert_span_gen span_substd_basis[OF assms,symmetric] * ..
qed

lemma affine_hull_convex_hull [simp]: "affine hull (convex hull S) = affine hull S"
  by (metis Int_absorb1 Int_absorb2 convex_hull_subset_affine_hull hull_hull hull_mono hull_subset)


subsection \<open>Openness and compactness are preserved by convex hull operation.\<close>

lemma open_convex_hull[intro]:
  fixes s :: "'a::real_normed_vector set"
  assumes "open s"
  shows "open (convex hull s)"
  unfolding open_contains_cball convex_hull_explicit
  unfolding mem_Collect_eq ball_simps(8)
proof (rule, rule)
  fix a
  assume "\<exists>sa u. finite sa \<and> sa \<subseteq> s \<and> (\<forall>x\<in>sa. 0 \<le> u x) \<and> sum u sa = 1 \<and> (\<Sum>v\<in>sa. u v *\<^sub>R v) = a"
  then obtain t u where obt: "finite t" "t\<subseteq>s" "\<forall>x\<in>t. 0 \<le> u x" "sum u t = 1" "(\<Sum>v\<in>t. u v *\<^sub>R v) = a"
    by auto

  from assms[unfolded open_contains_cball] obtain b
    where b: "\<forall>x\<in>s. 0 < b x \<and> cball x (b x) \<subseteq> s"
    using bchoice[of s "\<lambda>x e. e > 0 \<and> cball x e \<subseteq> s"] by auto
  have "b ` t \<noteq> {}"
    using obt by auto
  define i where "i = b ` t"

  show "\<exists>e > 0.
    cball a e \<subseteq> {y. \<exists>sa u. finite sa \<and> sa \<subseteq> s \<and> (\<forall>x\<in>sa. 0 \<le> u x) \<and> sum u sa = 1 \<and> (\<Sum>v\<in>sa. u v *\<^sub>R v) = y}"
    apply (rule_tac x = "Min i" in exI)
    unfolding subset_eq
    apply rule
    defer
    apply rule
    unfolding mem_Collect_eq
  proof -
    show "0 < Min i"
      unfolding i_def and Min_gr_iff[OF finite_imageI[OF obt(1)] \<open>b ` t\<noteq>{}\<close>]
      using b
      apply simp
      apply rule
      apply (erule_tac x=x in ballE)
      using \<open>t\<subseteq>s\<close>
      apply auto
      done
  next
    fix y
    assume "y \<in> cball a (Min i)"
    then have y: "norm (a - y) \<le> Min i"
      unfolding dist_norm[symmetric] by auto
    {
      fix x
      assume "x \<in> t"
      then have "Min i \<le> b x"
        unfolding i_def
        apply (rule_tac Min_le)
        using obt(1)
        apply auto
        done
      then have "x + (y - a) \<in> cball x (b x)"
        using y unfolding mem_cball dist_norm by auto
      moreover from \<open>x\<in>t\<close> have "x \<in> s"
        using obt(2) by auto
      ultimately have "x + (y - a) \<in> s"
        using y and b[THEN bspec[where x=x]] unfolding subset_eq by fast
    }
    moreover
    have *: "inj_on (\<lambda>v. v + (y - a)) t"
      unfolding inj_on_def by auto
    have "(\<Sum>v\<in>(\<lambda>v. v + (y - a)) ` t. u (v - (y - a))) = 1"
      unfolding sum.reindex[OF *] o_def using obt(4) by auto
    moreover have "(\<Sum>v\<in>(\<lambda>v. v + (y - a)) ` t. u (v - (y - a)) *\<^sub>R v) = y"
      unfolding sum.reindex[OF *] o_def using obt(4,5)
      by (simp add: sum.distrib sum_subtractf scaleR_left.sum[symmetric] scaleR_right_distrib)
    ultimately
    show "\<exists>sa u. finite sa \<and> (\<forall>x\<in>sa. x \<in> s) \<and> (\<forall>x\<in>sa. 0 \<le> u x) \<and> sum u sa = 1 \<and> (\<Sum>v\<in>sa. u v *\<^sub>R v) = y"
      apply (rule_tac x="(\<lambda>v. v + (y - a)) ` t" in exI)
      apply (rule_tac x="\<lambda>v. u (v - (y - a))" in exI)
      using obt(1, 3)
      apply auto
      done
  qed
qed

lemma compact_convex_combinations:
  fixes s t :: "'a::real_normed_vector set"
  assumes "compact s" "compact t"
  shows "compact { (1 - u) *\<^sub>R x + u *\<^sub>R y | x y u. 0 \<le> u \<and> u \<le> 1 \<and> x \<in> s \<and> y \<in> t}"
proof -
  let ?X = "{0..1} \<times> s \<times> t"
  let ?h = "(\<lambda>z. (1 - fst z) *\<^sub>R fst (snd z) + fst z *\<^sub>R snd (snd z))"
  have *: "{ (1 - u) *\<^sub>R x + u *\<^sub>R y | x y u. 0 \<le> u \<and> u \<le> 1 \<and> x \<in> s \<and> y \<in> t} = ?h ` ?X"
    apply (rule set_eqI)
    unfolding image_iff mem_Collect_eq
    apply rule
    apply auto
    apply (rule_tac x=u in rev_bexI)
    apply simp
    apply (erule rev_bexI)
    apply (erule rev_bexI)
    apply simp
    apply auto
    done
  have "continuous_on ?X (\<lambda>z. (1 - fst z) *\<^sub>R fst (snd z) + fst z *\<^sub>R snd (snd z))"
    unfolding continuous_on by (rule ballI) (intro tendsto_intros)
  then show ?thesis
    unfolding *
    apply (rule compact_continuous_image)
    apply (intro compact_Times compact_Icc assms)
    done
qed

lemma finite_imp_compact_convex_hull:
  fixes s :: "'a::real_normed_vector set"
  assumes "finite s"
  shows "compact (convex hull s)"
proof (cases "s = {}")
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
      apply (rule_tac x="1 - a" in exI, simp)
      apply fast
      apply (rule_tac x="(u, b)" in image_eqI, simp_all)
      done
    finally show "compact (convex hull (insert x A))" .
  qed
qed

lemma compact_convex_hull:
  fixes s :: "'a::euclidean_space set"
  assumes "compact s"
  shows "compact (convex hull s)"
proof (cases "s = {}")
  case True
  then show ?thesis using compact_empty by simp
next
  case False
  then obtain w where "w \<in> s" by auto
  show ?thesis
    unfolding caratheodory[of s]
  proof (induct ("DIM('a) + 1"))
    case 0
    have *: "{x.\<exists>sa. finite sa \<and> sa \<subseteq> s \<and> card sa \<le> 0 \<and> x \<in> convex hull sa} = {}"
      using compact_empty by auto
    from 0 show ?case unfolding * by simp
  next
    case (Suc n)
    show ?case
    proof (cases "n = 0")
      case True
      have "{x. \<exists>t. finite t \<and> t \<subseteq> s \<and> card t \<le> Suc n \<and> x \<in> convex hull t} = s"
        unfolding set_eq_iff and mem_Collect_eq
      proof (rule, rule)
        fix x
        assume "\<exists>t. finite t \<and> t \<subseteq> s \<and> card t \<le> Suc n \<and> x \<in> convex hull t"
        then obtain t where t: "finite t" "t \<subseteq> s" "card t \<le> Suc n" "x \<in> convex hull t"
          by auto
        show "x \<in> s"
        proof (cases "card t = 0")
          case True
          then show ?thesis
            using t(4) unfolding card_0_eq[OF t(1)] by simp
        next
          case False
          then have "card t = Suc 0" using t(3) \<open>n=0\<close> by auto
          then obtain a where "t = {a}" unfolding card_Suc_eq by auto
          then show ?thesis using t(2,4) by simp
        qed
      next
        fix x assume "x\<in>s"
        then show "\<exists>t. finite t \<and> t \<subseteq> s \<and> card t \<le> Suc n \<and> x \<in> convex hull t"
          apply (rule_tac x="{x}" in exI)
          unfolding convex_hull_singleton
          apply auto
          done
      qed
      then show ?thesis using assms by simp
    next
      case False
      have "{x. \<exists>t. finite t \<and> t \<subseteq> s \<and> card t \<le> Suc n \<and> x \<in> convex hull t} =
        {(1 - u) *\<^sub>R x + u *\<^sub>R y | x y u.
          0 \<le> u \<and> u \<le> 1 \<and> x \<in> s \<and> y \<in> {x. \<exists>t. finite t \<and> t \<subseteq> s \<and> card t \<le> n \<and> x \<in> convex hull t}}"
        unfolding set_eq_iff and mem_Collect_eq
      proof (rule, rule)
        fix x
        assume "\<exists>u v c. x = (1 - c) *\<^sub>R u + c *\<^sub>R v \<and>
          0 \<le> c \<and> c \<le> 1 \<and> u \<in> s \<and> (\<exists>t. finite t \<and> t \<subseteq> s \<and> card t \<le> n \<and> v \<in> convex hull t)"
        then obtain u v c t where obt: "x = (1 - c) *\<^sub>R u + c *\<^sub>R v"
          "0 \<le> c \<and> c \<le> 1" "u \<in> s" "finite t" "t \<subseteq> s" "card t \<le> n"  "v \<in> convex hull t"
          by auto
        moreover have "(1 - c) *\<^sub>R u + c *\<^sub>R v \<in> convex hull insert u t"
          apply (rule convexD_alt)
          using obt(2) and convex_convex_hull and hull_subset[of "insert u t" convex]
          using obt(7) and hull_mono[of t "insert u t"]
          apply auto
          done
        ultimately show "\<exists>t. finite t \<and> t \<subseteq> s \<and> card t \<le> Suc n \<and> x \<in> convex hull t"
          apply (rule_tac x="insert u t" in exI)
          apply (auto simp add: card_insert_if)
          done
      next
        fix x
        assume "\<exists>t. finite t \<and> t \<subseteq> s \<and> card t \<le> Suc n \<and> x \<in> convex hull t"
        then obtain t where t: "finite t" "t \<subseteq> s" "card t \<le> Suc n" "x \<in> convex hull t"
          by auto
        show "\<exists>u v c. x = (1 - c) *\<^sub>R u + c *\<^sub>R v \<and>
          0 \<le> c \<and> c \<le> 1 \<and> u \<in> s \<and> (\<exists>t. finite t \<and> t \<subseteq> s \<and> card t \<le> n \<and> v \<in> convex hull t)"
        proof (cases "card t = Suc n")
          case False
          then have "card t \<le> n" using t(3) by auto
          then show ?thesis
            apply (rule_tac x=w in exI, rule_tac x=x in exI, rule_tac x=1 in exI)
            using \<open>w\<in>s\<close> and t
            apply (auto intro!: exI[where x=t])
            done
        next
          case True
          then obtain a u where au: "t = insert a u" "a\<notin>u"
            apply (drule_tac card_eq_SucD)
            apply auto
            done
          show ?thesis
          proof (cases "u = {}")
            case True
            then have "x = a" using t(4)[unfolded au] by auto
            show ?thesis unfolding \<open>x = a\<close>
              apply (rule_tac x=a in exI)
              apply (rule_tac x=a in exI)
              apply (rule_tac x=1 in exI)
              using t and \<open>n \<noteq> 0\<close>
              unfolding au
              apply (auto intro!: exI[where x="{a}"])
              done
          next
            case False
            obtain ux vx b where obt: "ux\<ge>0" "vx\<ge>0" "ux + vx = 1"
              "b \<in> convex hull u" "x = ux *\<^sub>R a + vx *\<^sub>R b"
              using t(4)[unfolded au convex_hull_insert[OF False]]
              by auto
            have *: "1 - vx = ux" using obt(3) by auto
            show ?thesis
              apply (rule_tac x=a in exI)
              apply (rule_tac x=b in exI)
              apply (rule_tac x=vx in exI)
              using obt and t(1-3)
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


subsection \<open>Extremal points of a simplex are some vertices.\<close>

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
  fixes s :: "'a::real_inner set"
  assumes "finite s"
  shows "\<forall>x \<in> convex hull s.  x \<notin> s \<longrightarrow> (\<exists>y \<in> convex hull s. norm (x - a) < norm(y - a))"
  using assms
proof induct
  fix x s
  assume as: "finite s" "x\<notin>s" "\<forall>x\<in>convex hull s. x \<notin> s \<longrightarrow> (\<exists>y\<in>convex hull s. norm (x - a) < norm (y - a))"
  show "\<forall>xa\<in>convex hull insert x s. xa \<notin> insert x s \<longrightarrow>
    (\<exists>y\<in>convex hull insert x s. norm (xa - a) < norm (y - a))"
  proof (rule, rule, cases "s = {}")
    case False
    fix y
    assume y: "y \<in> convex hull insert x s" "y \<notin> insert x s"
    obtain u v b where obt: "u\<ge>0" "v\<ge>0" "u + v = 1" "b \<in> convex hull s" "y = u *\<^sub>R x + v *\<^sub>R b"
      using y(1)[unfolded convex_hull_insert[OF False]] by auto
    show "\<exists>z\<in>convex hull insert x s. norm (y - a) < norm (z - a)"
    proof (cases "y \<in> convex hull s")
      case True
      then obtain z where "z \<in> convex hull s" "norm (y - a) < norm (z - a)"
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
          using real_lbound_gt_zero[of u v] and obt(1,2) by auto
        have "x \<noteq> b"
        proof
          assume "x = b"
          then have "y = b" unfolding obt(5)
            using obt(3) by (auto simp add: scaleR_left_distrib[symmetric])
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
          moreover have "(u + w) *\<^sub>R x + (v - w) *\<^sub>R b \<in> convex hull insert x s"
            unfolding convex_hull_insert[OF \<open>s\<noteq>{}\<close>] and mem_Collect_eq
            apply (rule_tac x="u + w" in exI)
            apply rule
            defer
            apply (rule_tac x="v - w" in exI)
            using \<open>u \<ge> 0\<close> and w and obt(3,4)
            apply auto
            done
          ultimately show ?thesis by auto
        next
          assume "dist a y < dist a (y - w *\<^sub>R (x - b))"
          then have "norm (y - a) < norm ((u - w) *\<^sub>R x + (v + w) *\<^sub>R b - a)"
            unfolding dist_commute[of a]
            unfolding dist_norm obt(5)
            by (simp add: algebra_simps)
          moreover have "(u - w) *\<^sub>R x + (v + w) *\<^sub>R b \<in> convex hull insert x s"
            unfolding convex_hull_insert[OF \<open>s\<noteq>{}\<close>] and mem_Collect_eq
            apply (rule_tac x="u - w" in exI)
            apply rule
            defer
            apply (rule_tac x="v + w" in exI)
            using \<open>u \<ge> 0\<close> and w and obt(3,4)
            apply auto
            done
          ultimately show ?thesis by auto
        qed
      qed auto
    qed
  qed auto
qed (auto simp add: assms)

lemma simplex_furthest_le:
  fixes s :: "'a::real_inner set"
  assumes "finite s"
    and "s \<noteq> {}"
  shows "\<exists>y\<in>s. \<forall>x\<in> convex hull s. norm (x - a) \<le> norm (y - a)"
proof -
  have "convex hull s \<noteq> {}"
    using hull_subset[of s convex] and assms(2) by auto
  then obtain x where x: "x \<in> convex hull s" "\<forall>y\<in>convex hull s. norm (y - a) \<le> norm (x - a)"
    using distance_attains_sup[OF finite_imp_compact_convex_hull[OF assms(1)], of a]
    unfolding dist_commute[of a]
    unfolding dist_norm
    by auto
  show ?thesis
  proof (cases "x \<in> s")
    case False
    then obtain y where "y \<in> convex hull s" "norm (x - a) < norm (y - a)"
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
  fixes s :: "('a::real_inner) set"
  shows "finite s \<Longrightarrow> \<forall>x\<in>(convex hull s). \<exists>y\<in>s. norm (x - a) \<le> norm (y - a)"
  using simplex_furthest_le[of s] by (cases "s = {}") auto

lemma simplex_extremal_le:
  fixes s :: "'a::real_inner set"
  assumes "finite s"
    and "s \<noteq> {}"
  shows "\<exists>u\<in>s. \<exists>v\<in>s. \<forall>x\<in>convex hull s. \<forall>y \<in> convex hull s. norm (x - y) \<le> norm (u - v)"
proof -
  have "convex hull s \<noteq> {}"
    using hull_subset[of s convex] and assms(2) by auto
  then obtain u v where obt: "u \<in> convex hull s" "v \<in> convex hull s"
    "\<forall>x\<in>convex hull s. \<forall>y\<in>convex hull s. norm (x - y) \<le> norm (u - v)"
    using compact_sup_maxdistance[OF finite_imp_compact_convex_hull[OF assms(1)]]
    by (auto simp: dist_norm)
  then show ?thesis
  proof (cases "u\<notin>s \<or> v\<notin>s", elim disjE)
    assume "u \<notin> s"
    then obtain y where "y \<in> convex hull s" "norm (u - v) < norm (y - v)"
      using simplex_furthest_lt[OF assms(1), THEN bspec[where x=u]] and obt(1)
      by auto
    then show ?thesis
      using obt(3)[THEN bspec[where x=y], THEN bspec[where x=v]] and obt(2)
      by auto
  next
    assume "v \<notin> s"
    then obtain y where "y \<in> convex hull s" "norm (v - u) < norm (y - u)"
      using simplex_furthest_lt[OF assms(1), THEN bspec[where x=v]] and obt(2)
      by auto
    then show ?thesis
      using obt(3)[THEN bspec[where x=u], THEN bspec[where x=y]] and obt(1)
      by (auto simp add: norm_minus_commute)
  qed auto
qed

lemma simplex_extremal_le_exists:
  fixes s :: "'a::real_inner set"
  shows "finite s \<Longrightarrow> x \<in> convex hull s \<Longrightarrow> y \<in> convex hull s \<Longrightarrow>
    \<exists>u\<in>s. \<exists>v\<in>s. norm (x - y) \<le> norm (u - v)"
  using convex_hull_empty simplex_extremal_le[of s]
  by(cases "s = {}") auto


subsection \<open>Closest point of a convex set is unique, with a continuous projection.\<close>

definition closest_point :: "'a::{real_inner,heine_borel} set \<Rightarrow> 'a \<Rightarrow> 'a"
  where "closest_point s a = (SOME x. x \<in> s \<and> (\<forall>y\<in>s. dist a x \<le> dist a y))"

lemma closest_point_exists:
  assumes "closed s"
    and "s \<noteq> {}"
  shows "closest_point s a \<in> s"
    and "\<forall>y\<in>s. dist a (closest_point s a) \<le> dist a y"
  unfolding closest_point_def
  apply(rule_tac[!] someI2_ex)
  apply (auto intro: distance_attains_inf[OF assms(1,2), of a])
  done

lemma closest_point_in_set: "closed s \<Longrightarrow> s \<noteq> {} \<Longrightarrow> closest_point s a \<in> s"
  by (meson closest_point_exists)

lemma closest_point_le: "closed s \<Longrightarrow> x \<in> s \<Longrightarrow> dist a (closest_point s a) \<le> dist a x"
  using closest_point_exists[of s] by auto

lemma closest_point_self:
  assumes "x \<in> s"
  shows "closest_point s x = x"
  unfolding closest_point_def
  apply (rule some1_equality, rule ex1I[of _ x])
  using assms
  apply auto
  done

lemma closest_point_refl: "closed s \<Longrightarrow> s \<noteq> {} \<Longrightarrow> closest_point s x = x \<longleftrightarrow> x \<in> s"
  using closest_point_in_set[of s x] closest_point_self[of x s]
  by auto

lemma closer_points_lemma:
  assumes "inner y z > 0"
  shows "\<exists>u>0. \<forall>v>0. v \<le> u \<longrightarrow> norm(v *\<^sub>R z - y) < norm y"
proof -
  have z: "inner z z > 0"
    unfolding inner_gt_zero_iff using assms by auto
  then show ?thesis
    using assms
    apply (rule_tac x = "inner y z / inner z z" in exI)
    apply rule
    defer
  proof rule+
    fix v
    assume "0 < v" and "v \<le> inner y z / inner z z"
    then show "norm (v *\<^sub>R z - y) < norm y"
      unfolding norm_lt using z and assms
      by (simp add: field_simps inner_diff inner_commute mult_strict_left_mono[OF _ \<open>0<v\<close>])
  qed auto
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
    unfolding dist_norm by (auto simp add: norm_minus_commute field_simps)
qed

lemma any_closest_point_dot:
  assumes "convex s" "closed s" "x \<in> s" "y \<in> s" "\<forall>z\<in>s. dist a x \<le> dist a z"
  shows "inner (a - x) (y - x) \<le> 0"
proof (rule ccontr)
  assume "\<not> ?thesis"
  then obtain u where u: "u>0" "u\<le>1" "dist (x + u *\<^sub>R (y - x)) a < dist x a"
    using closer_point_lemma[of a x y] by auto
  let ?z = "(1 - u) *\<^sub>R x + u *\<^sub>R y"
  have "?z \<in> s"
    using convexD_alt[OF assms(1,3,4), of u] using u by auto
  then show False
    using assms(5)[THEN bspec[where x="?z"]] and u(3)
    by (auto simp add: dist_commute algebra_simps)
qed

lemma any_closest_point_unique:
  fixes x :: "'a::real_inner"
  assumes "convex s" "closed s" "x \<in> s" "y \<in> s"
    "\<forall>z\<in>s. dist a x \<le> dist a z" "\<forall>z\<in>s. dist a y \<le> dist a z"
  shows "x = y"
  using any_closest_point_dot[OF assms(1-4,5)] and any_closest_point_dot[OF assms(1-2,4,3,6)]
  unfolding norm_pths(1) and norm_le_square
  by (auto simp add: algebra_simps)

lemma closest_point_unique:
  assumes "convex s" "closed s" "x \<in> s" "\<forall>z\<in>s. dist a x \<le> dist a z"
  shows "x = closest_point s a"
  using any_closest_point_unique[OF assms(1-3) _ assms(4), of "closest_point s a"]
  using closest_point_exists[OF assms(2)] and assms(3) by auto

lemma closest_point_dot:
  assumes "convex s" "closed s" "x \<in> s"
  shows "inner (a - closest_point s a) (x - closest_point s a) \<le> 0"
  apply (rule any_closest_point_dot[OF assms(1,2) _ assms(3)])
  using closest_point_exists[OF assms(2)] and assms(3)
  apply auto
  done

lemma closest_point_lt:
  assumes "convex s" "closed s" "x \<in> s" "x \<noteq> closest_point s a"
  shows "dist a (closest_point s a) < dist a x"
  apply (rule ccontr)
  apply (rule_tac notE[OF assms(4)])
  apply (rule closest_point_unique[OF assms(1-3), of a])
  using closest_point_le[OF assms(2), of _ a]
  apply fastforce
  done

lemma closest_point_lipschitz:
  assumes "convex s"
    and "closed s" "s \<noteq> {}"
  shows "dist (closest_point s x) (closest_point s y) \<le> dist x y"
proof -
  have "inner (x - closest_point s x) (closest_point s y - closest_point s x) \<le> 0"
    and "inner (y - closest_point s y) (closest_point s x - closest_point s y) \<le> 0"
    apply (rule_tac[!] any_closest_point_dot[OF assms(1-2)])
    using closest_point_exists[OF assms(2-3)]
    apply auto
    done
  then show ?thesis unfolding dist_norm and norm_le
    using inner_ge_zero[of "(x - closest_point s x) - (y - closest_point s y)"]
    by (simp add: inner_add inner_diff inner_commute)
qed

lemma continuous_at_closest_point:
  assumes "convex s"
    and "closed s"
    and "s \<noteq> {}"
  shows "continuous (at x) (closest_point s)"
  unfolding continuous_at_eps_delta
  using le_less_trans[OF closest_point_lipschitz[OF assms]] by auto

lemma continuous_on_closest_point:
  assumes "convex s"
    and "closed s"
    and "s \<noteq> {}"
  shows "continuous_on t (closest_point s)"
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
    also have "... < norm(x - closest_point S x)"
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


subsubsection \<open>Various point-to-set separating/supporting hyperplane theorems.\<close>

lemma supporting_hyperplane_closed_point:
  fixes z :: "'a::{real_inner,heine_borel}"
  assumes "convex s"
    and "closed s"
    and "s \<noteq> {}"
    and "z \<notin> s"
  shows "\<exists>a b. \<exists>y\<in>s. inner a z < b \<and> inner a y = b \<and> (\<forall>x\<in>s. inner a x \<ge> b)"
proof -
  obtain y where "y \<in> s" and y: "\<forall>x\<in>s. dist z y \<le> dist z x"
    by (metis distance_attains_inf[OF assms(2-3)])
  show ?thesis
    apply (rule_tac x="y - z" in exI)
    apply (rule_tac x="inner (y - z) y" in exI)
    apply (rule_tac x=y in bexI)
    apply rule
    defer
    apply rule
    defer
    apply rule
    apply (rule ccontr)
    using \<open>y \<in> s\<close>
  proof -
    show "inner (y - z) z < inner (y - z) y"
      apply (subst diff_gt_0_iff_gt [symmetric])
      unfolding inner_diff_right[symmetric] and inner_gt_zero_iff
      using \<open>y\<in>s\<close> \<open>z\<notin>s\<close>
      apply auto
      done
  next
    fix x
    assume "x \<in> s"
    have *: "\<forall>u. 0 \<le> u \<and> u \<le> 1 \<longrightarrow> dist z y \<le> dist z ((1 - u) *\<^sub>R y + u *\<^sub>R x)"
      using assms(1)[unfolded convex_alt] and y and \<open>x\<in>s\<close> and \<open>y\<in>s\<close> by auto
    assume "\<not> inner (y - z) y \<le> inner (y - z) x"
    then obtain v where "v > 0" "v \<le> 1" "dist (y + v *\<^sub>R (x - y)) z < dist y z"
      using closer_point_lemma[of z y x] by (auto simp add: inner_diff)
    then show False
      using *[THEN spec[where x=v]] by (auto simp add: dist_commute algebra_simps)
  qed auto
qed

lemma separating_hyperplane_closed_point:
  fixes z :: "'a::{real_inner,heine_borel}"
  assumes "convex s"
    and "closed s"
    and "z \<notin> s"
  shows "\<exists>a b. inner a z < b \<and> (\<forall>x\<in>s. inner a x > b)"
proof (cases "s = {}")
  case True
  then show ?thesis
    apply (rule_tac x="-z" in exI)
    apply (rule_tac x=1 in exI)
    using less_le_trans[OF _ inner_ge_zero[of z]]
    apply auto
    done
next
  case False
  obtain y where "y \<in> s" and y: "\<forall>x\<in>s. dist z y \<le> dist z x"
    by (metis distance_attains_inf[OF assms(2) False])
  show ?thesis
    apply (rule_tac x="y - z" in exI)
    apply (rule_tac x="inner (y - z) z + (norm (y - z))\<^sup>2 / 2" in exI)
    apply rule
    defer
    apply rule
  proof -
    fix x
    assume "x \<in> s"
    have "\<not> 0 < inner (z - y) (x - y)"
      apply (rule notI)
      apply (drule closer_point_lemma)
    proof -
      assume "\<exists>u>0. u \<le> 1 \<and> dist (y + u *\<^sub>R (x - y)) z < dist y z"
      then obtain u where "u > 0" "u \<le> 1" "dist (y + u *\<^sub>R (x - y)) z < dist y z"
        by auto
      then show False using y[THEN bspec[where x="y + u *\<^sub>R (x - y)"]]
        using assms(1)[unfolded convex_alt, THEN bspec[where x=y]]
        using \<open>x\<in>s\<close> \<open>y\<in>s\<close> by (auto simp add: dist_commute algebra_simps)
    qed
    moreover have "0 < (norm (y - z))\<^sup>2"
      using \<open>y\<in>s\<close> \<open>z\<notin>s\<close> by auto
    then have "0 < inner (y - z) (y - z)"
      unfolding power2_norm_eq_inner by simp
    ultimately show "inner (y - z) z + (norm (y - z))\<^sup>2 / 2 < inner (y - z) x"
      unfolding power2_norm_eq_inner and not_less
      by (auto simp add: field_simps inner_commute inner_diff)
  qed (insert \<open>y\<in>s\<close> \<open>z\<notin>s\<close>, auto)
qed

lemma separating_hyperplane_closed_0:
  assumes "convex (s::('a::euclidean_space) set)"
    and "closed s"
    and "0 \<notin> s"
  shows "\<exists>a b. a \<noteq> 0 \<and> 0 < b \<and> (\<forall>x\<in>s. inner a x > b)"
proof (cases "s = {}")
  case True
  have "norm ((SOME i. i\<in>Basis)::'a) = 1" "(SOME i. i\<in>Basis) \<noteq> (0::'a)"
    defer
    apply (subst norm_le_zero_iff[symmetric])
    apply (auto simp: SOME_Basis)
    done
  then show ?thesis
    apply (rule_tac x="SOME i. i\<in>Basis" in exI)
    apply (rule_tac x=1 in exI)
    using True using DIM_positive[where 'a='a]
    apply auto
    done
next
  case False
  then show ?thesis
    using False using separating_hyperplane_closed_point[OF assms]
    apply (elim exE)
    unfolding inner_zero_right
    apply (rule_tac x=a in exI)
    apply (rule_tac x=b in exI)
    apply auto
    done
qed


subsubsection \<open>Now set-to-set for closed/compact sets\<close>

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
    apply (auto simp add: inner_diff)
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
      show "bdd_above (op \<bullet> a ` T)"
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
    apply (rule_tac x="-b" in exI)
    apply auto
    done
qed


subsubsection \<open>General case without assuming closure and getting non-strict separation\<close>

lemma separating_hyperplane_set_0:
  assumes "convex s" "(0::'a::euclidean_space) \<notin> s"
  shows "\<exists>a. a \<noteq> 0 \<and> (\<forall>x\<in>s. 0 \<le> inner a x)"
proof -
  let ?k = "\<lambda>c. {x::'a. 0 \<le> inner c x}"
  have *: "frontier (cball 0 1) \<inter> \<Inter>f \<noteq> {}" if as: "f \<subseteq> ?k ` s" "finite f" for f
  proof -
    obtain c where c: "f = ?k ` c" "c \<subseteq> s" "finite c"
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
      by (auto simp add: inner_commute del: ballE elim!: ballE)
    then show "frontier (cball 0 1) \<inter> \<Inter>f \<noteq> {}"
      unfolding c(1) frontier_cball sphere_def dist_norm by auto
  qed
  have "frontier (cball 0 1) \<inter> (\<Inter>(?k ` s)) \<noteq> {}"
    apply (rule compact_imp_fip)
    apply (rule compact_frontier[OF compact_cball])
    using * closed_halfspace_ge
    by auto
  then obtain x where "norm x = 1" "\<forall>y\<in>s. x\<in>?k y"
    unfolding frontier_cball dist_norm sphere_def by auto
  then show ?thesis
    by (metis inner_commute mem_Collect_eq norm_eq_zero zero_neq_one)
qed

lemma separating_hyperplane_sets:
  fixes s t :: "'a::euclidean_space set"
  assumes "convex s"
    and "convex t"
    and "s \<noteq> {}"
    and "t \<noteq> {}"
    and "s \<inter> t = {}"
  shows "\<exists>a b. a \<noteq> 0 \<and> (\<forall>x\<in>s. inner a x \<le> b) \<and> (\<forall>x\<in>t. inner a x \<ge> b)"
proof -
  from separating_hyperplane_set_0[OF convex_differences[OF assms(2,1)]]
  obtain a where "a \<noteq> 0" "\<forall>x\<in>{x - y |x y. x \<in> t \<and> y \<in> s}. 0 \<le> inner a x"
    using assms(3-5) by fastforce
  then have *: "\<And>x y. x \<in> t \<Longrightarrow> y \<in> s \<Longrightarrow> inner a y \<le> inner a x"
    by (force simp add: inner_diff)
  then have bdd: "bdd_above ((op \<bullet> a)`s)"
    using \<open>t \<noteq> {}\<close> by (auto intro: bdd_aboveI2[OF *])
  show ?thesis
    using \<open>a\<noteq>0\<close>
    by (intro exI[of _ a] exI[of _ "SUP x:s. a \<bullet> x"])
       (auto intro!: cSUP_upper bdd cSUP_least \<open>a \<noteq> 0\<close> \<open>s \<noteq> {}\<close> *)
qed


subsection \<open>More convexity generalities\<close>

lemma convex_closure [intro,simp]:
  fixes s :: "'a::real_normed_vector set"
  assumes "convex s"
  shows "convex (closure s)"
  apply (rule convexI)
  apply (unfold closure_sequential, elim exE)
  apply (rule_tac x="\<lambda>n. u *\<^sub>R xa n + v *\<^sub>R xb n" in exI)
  apply (rule,rule)
  apply (rule convexD [OF assms])
  apply (auto del: tendsto_const intro!: tendsto_intros)
  done

lemma convex_interior [intro,simp]:
  fixes s :: "'a::real_normed_vector set"
  assumes "convex s"
  shows "convex (interior s)"
  unfolding convex_alt Ball_def mem_interior
  apply (rule,rule,rule,rule,rule,rule)
  apply (elim exE conjE)
proof -
  fix x y u
  assume u: "0 \<le> u" "u \<le> (1::real)"
  fix e d
  assume ed: "ball x e \<subseteq> s" "ball y d \<subseteq> s" "0<d" "0<e"
  show "\<exists>e>0. ball ((1 - u) *\<^sub>R x + u *\<^sub>R y) e \<subseteq> s"
    apply (rule_tac x="min d e" in exI)
    apply rule
    unfolding subset_eq
    defer
    apply rule
  proof -
    fix z
    assume "z \<in> ball ((1 - u) *\<^sub>R x + u *\<^sub>R y) (min d e)"
    then have "(1- u) *\<^sub>R (z - u *\<^sub>R (y - x)) + u *\<^sub>R (z + (1 - u) *\<^sub>R (y - x)) \<in> s"
      apply (rule_tac assms[unfolded convex_alt, rule_format])
      using ed(1,2) and u
      unfolding subset_eq mem_ball Ball_def dist_norm
      apply (auto simp add: algebra_simps)
      done
    then show "z \<in> s"
      using u by (auto simp add: algebra_simps)
  qed(insert u ed(3-4), auto)
qed

lemma convex_hull_eq_empty[simp]: "convex hull s = {} \<longleftrightarrow> s = {}"
  using hull_subset[of s convex] convex_hull_empty by auto


subsection \<open>Moving and scaling convex hulls.\<close>

lemma convex_hull_set_plus:
  "convex hull (s + t) = convex hull s + convex hull t"
  unfolding set_plus_image
  apply (subst convex_hull_linear_image [symmetric])
  apply (simp add: linear_iff scaleR_right_distrib)
  apply (simp add: convex_hull_Times)
  done

lemma translation_eq_singleton_plus: "(\<lambda>x. a + x) ` t = {a} + t"
  unfolding set_plus_def by auto

lemma convex_hull_translation:
  "convex hull ((\<lambda>x. a + x) ` s) = (\<lambda>x. a + x) ` (convex hull s)"
  unfolding translation_eq_singleton_plus
  by (simp only: convex_hull_set_plus convex_hull_singleton)

lemma convex_hull_scaling:
  "convex hull ((\<lambda>x. c *\<^sub>R x) ` s) = (\<lambda>x. c *\<^sub>R x) ` (convex hull s)"
  using linear_scaleR by (rule convex_hull_linear_image [symmetric])

lemma convex_hull_affinity:
  "convex hull ((\<lambda>x. a + c *\<^sub>R x) ` s) = (\<lambda>x. a + c *\<^sub>R x) ` (convex hull s)"
  by(simp only: image_image[symmetric] convex_hull_scaling convex_hull_translation)


subsection \<open>Convexity of cone hulls\<close>

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
      by (auto simp add: scaleR_right_distrib)
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
  then have *: "0 \<in> S \<and> (\<forall>c. c > 0 \<longrightarrow> op *\<^sub>R c ` S = S)"
    using cone_iff[of S] assms by auto
  {
    fix c :: real
    assume "c > 0"
    then have "op *\<^sub>R c ` (convex hull S) = convex hull (op *\<^sub>R c ` S)"
      using convex_hull_scaling[of _ S] by auto
    also have "\<dots> = convex hull S"
      using * \<open>c > 0\<close> by auto
    finally have "op *\<^sub>R c ` (convex hull S) = convex hull S"
      by auto
  }
  then have "0 \<in> convex hull S" "\<And>c. c > 0 \<Longrightarrow> (op *\<^sub>R c ` (convex hull S)) = (convex hull S)"
    using * hull_subset[of S convex] by auto
  then show ?thesis
    using \<open>S \<noteq> {}\<close> cone_iff[of "convex hull S"] by auto
qed

subsection \<open>Convex set as intersection of halfspaces\<close>

lemma convex_halfspace_intersection:
  fixes s :: "('a::euclidean_space) set"
  assumes "closed s" "convex s"
  shows "s = \<Inter>{h. s \<subseteq> h \<and> (\<exists>a b. h = {x. inner a x \<le> b})}"
  apply (rule set_eqI)
  apply rule
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
    apply (erule_tac x="-b" in allE)
    apply auto
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
    apply (auto simp add: Int_absorb1)
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
        apply (rule_tac sum_mono)
        apply auto
        done
      then show ?thesis
        unfolding sum.delta[OF assms(1)] using uv(2) and \<open>u v < 0\<close> and uv(1) by auto
    qed
  qed (insert sum_nonneg_eq_0_iff[of _ u, OF fin(1)] uv(2-3), auto)

  then have *: "sum u {x\<in>c. u x > 0} > 0"
    unfolding less_le
    apply (rule_tac conjI)
    apply (rule_tac sum_nonneg)
    apply auto
    done
  moreover have "sum u ({x \<in> c. 0 < u x} \<union> {x \<in> c. u x < 0}) = sum u c"
    "(\<Sum>x\<in>{x \<in> c. 0 < u x} \<union> {x \<in> c. u x < 0}. u x *\<^sub>R x) = (\<Sum>x\<in>c. u x *\<^sub>R x)"
    using assms(1)
    apply (rule_tac[!] sum.mono_neutral_left)
    apply auto
    done
  then have "sum u {x \<in> c. 0 < u x} = - sum u {x \<in> c. 0 > u x}"
    "(\<Sum>x\<in>{x \<in> c. 0 < u x}. u x *\<^sub>R x) = - (\<Sum>x\<in>{x \<in> c. 0 > u x}. u x *\<^sub>R x)"
    unfolding eq_neg_iff_add_eq_0
    using uv(1,4)
    by (auto simp add: sum.union_inter_neutral[OF fin, symmetric])
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
    apply (auto simp add: sum_negf sum_distrib_left[symmetric])
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
    apply (auto simp add: sum_negf sum_distrib_left[symmetric])
    done
  ultimately show ?thesis
    apply (rule_tac x="{v\<in>c. u v \<le> 0}" in exI)
    apply (rule_tac x="{v\<in>c. u v > 0}" in exI)
    apply auto
    done
qed

lemma radon:
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
proof (induct n arbitrary: f)
  case 0
  then show ?case by auto
next
  case (Suc n)
  have "finite f"
    using \<open>card f = Suc n\<close> by (auto intro: card_ge_0_finite)
  show "\<Inter>f \<noteq> {}"
    apply (cases "n = DIM('a)")
    apply (rule Suc(5)[rule_format])
    unfolding \<open>card f = Suc n\<close>
  proof -
    assume ng: "n \<noteq> DIM('a)"
    then have "\<exists>X. \<forall>s\<in>f. X s \<in> \<Inter>(f - {s})"
      apply (rule_tac bchoice)
      unfolding ex_in_conv
      apply (rule, rule Suc(1)[rule_format])
      unfolding card_Diff_singleton_if[OF \<open>finite f\<close>] \<open>card f = Suc n\<close>
      defer
      defer
      apply (rule Suc(4)[rule_format])
      defer
      apply (rule Suc(5)[rule_format])
      using Suc(3) \<open>finite f\<close>
      apply auto
      done
    then obtain X where X: "\<forall>s\<in>f. X s \<in> \<Inter>(f - {s})" by auto
    show ?thesis
    proof (cases "inj_on X f")
      case False
      then obtain s t where st: "s\<noteq>t" "s\<in>f" "t\<in>f" "X s = X t"
        unfolding inj_on_def by auto
      then have *: "\<Inter>f = \<Inter>(f - {s}) \<inter> \<Inter>(f - {t})" by auto
      show ?thesis
        unfolding *
        unfolding ex_in_conv[symmetric]
        apply (rule_tac x="X s" in exI)
        apply rule
        apply (rule X[rule_format])
        using X st
        apply auto
        done
    next
      case True
      then obtain m p where mp: "m \<inter> p = {}" "m \<union> p = X ` f" "convex hull m \<inter> convex hull p \<noteq> {}"
        using radon_partition[of "X ` f"] and affine_dependent_biggerset[of "X ` f"]
        unfolding card_image[OF True] and \<open>card f = Suc n\<close>
        using Suc(3) \<open>finite f\<close> and ng
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
        apply (rule_tac [!] hull_minimal)
        using Suc gh(3-4)
        unfolding subset_eq
        apply (rule_tac [2] convex_Inter, rule_tac [4] convex_Inter)
        apply rule
        prefer 3
        apply rule
      proof -
        fix x
        assume "x \<in> X ` g"
        then obtain y where "y \<in> g" "x = X y"
          unfolding image_iff ..
        then show "x \<in> \<Inter>h"
          using X[THEN bspec[where x=y]] using * f by auto
      next
        fix x
        assume "x \<in> X ` h"
        then obtain y where "y \<in> h" "x = X y"
          unfolding image_iff ..
        then show "x \<in> \<Inter>g"
          using X[THEN bspec[where x=y]] using * f by auto
      qed auto
      then show ?thesis
        unfolding f using mp(3)[unfolded gh] by blast
    qed
  qed auto
qed

lemma helly:
  fixes f :: "'a::euclidean_space set set"
  assumes "card f \<ge> DIM('a) + 1" "\<forall>s\<in>f. convex s"
    and "\<forall>t\<subseteq>f. card t = DIM('a) + 1 \<longrightarrow> \<Inter>t \<noteq> {}"
  shows "\<Inter>f \<noteq> {}"
  apply (rule helly_induct)
  using assms
  apply auto
  done


subsection \<open>Epigraphs of convex functions\<close>

definition "epigraph s (f :: _ \<Rightarrow> real) = {xy. fst xy \<in> s \<and> f (fst xy) \<le> snd xy}"

lemma mem_epigraph: "(x, y) \<in> epigraph s f \<longleftrightarrow> x \<in> s \<and> f x \<le> y"
  unfolding epigraph_def by auto

lemma convex_epigraph: "convex (epigraph s f) \<longleftrightarrow> convex_on s f \<and> convex s"
  unfolding convex_def convex_on_def
  unfolding Ball_def split_paired_All epigraph_def
  unfolding mem_Collect_eq fst_conv snd_conv fst_add snd_add fst_scaleR snd_scaleR Ball_def[symmetric]
  apply safe
  defer
  apply (erule_tac x=x in allE)
  apply (erule_tac x="f x" in allE)
  apply safe
  apply (erule_tac x=xa in allE)
  apply (erule_tac x="f xa" in allE)
  prefer 3
  apply (rule_tac y="u * f a + v * f aa" in order_trans)
  defer
  apply (auto intro!:mult_left_mono add_mono)
  done

lemma convex_epigraphI: "convex_on s f \<Longrightarrow> convex s \<Longrightarrow> convex (epigraph s f)"
  unfolding convex_epigraph by auto

lemma convex_epigraph_convex: "convex s \<Longrightarrow> convex_on s f \<longleftrightarrow> convex(epigraph s f)"
  by (simp add: convex_epigraph)


subsubsection \<open>Use this to derive general bound property of convex function\<close>

lemma convex_on:
  assumes "convex s"
  shows "convex_on s f \<longleftrightarrow>
    (\<forall>k u x. (\<forall>i\<in>{1..k::nat}. 0 \<le> u i \<and> x i \<in> s) \<and> sum u {1..k} = 1 \<longrightarrow>
      f (sum (\<lambda>i. u i *\<^sub>R x i) {1..k} ) \<le> sum (\<lambda>i. u i * f(x i)) {1..k})"
  unfolding convex_epigraph_convex[OF assms] convex epigraph_def Ball_def mem_Collect_eq
  unfolding fst_sum snd_sum fst_scaleR snd_scaleR
  apply safe
  apply (drule_tac x=k in spec)
  apply (drule_tac x=u in spec)
  apply (drule_tac x="\<lambda>i. (x i, f (x i))" in spec)
  apply simp
  using assms[unfolded convex]
  apply simp
  apply (rule_tac y="\<Sum>i = 1..k. u i * f (fst (x i))" in order_trans)
  defer
  apply (rule sum_mono)
  apply (erule_tac x=i in allE)
  unfolding real_scaleR_def
  apply (rule mult_left_mono)
  using assms[unfolded convex]
  apply auto
  done


subsection \<open>Convexity of general and special intervals\<close>

lemma is_interval_convex:
  fixes s :: "'a::euclidean_space set"
  assumes "is_interval s"
  shows "convex s"
proof (rule convexI)
  fix x y and u v :: real
  assume as: "x \<in> s" "y \<in> s" "0 \<le> u" "0 \<le> v" "u + v = 1"
  then have *: "u = 1 - v" "1 - v \<ge> 0" and **: "v = 1 - u" "1 - u \<ge> 0"
    by auto
  {
    fix a b
    assume "\<not> b \<le> u * a + v * b"
    then have "u * a < (1 - v) * b"
      unfolding not_le using as(4) by (auto simp add: field_simps)
    then have "a < b"
      unfolding * using as(4) *(2)
      apply (rule_tac mult_left_less_imp_less[of "1 - v"])
      apply (auto simp add: field_simps)
      done
    then have "a \<le> u * a + v * b"
      unfolding * using as(4)
      by (auto simp add: field_simps intro!:mult_right_mono)
  }
  moreover
  {
    fix a b
    assume "\<not> u * a + v * b \<le> a"
    then have "v * b > (1 - u) * a"
      unfolding not_le using as(4) by (auto simp add: field_simps)
    then have "a < b"
      unfolding * using as(4)
      apply (rule_tac mult_left_less_imp_less)
      apply (auto simp add: field_simps)
      done
    then have "u * a + v * b \<le> b"
      unfolding **
      using **(2) as(3)
      by (auto simp add: field_simps intro!:mult_right_mono)
  }
  ultimately show "u *\<^sub>R x + v *\<^sub>R y \<in> s"
    apply -
    apply (rule assms[unfolded is_interval_def, rule_format, OF as(1,2)])
    using as(3-) DIM_positive[where 'a='a]
    apply (auto simp: inner_simps)
    done
qed

lemma is_interval_connected:
  fixes s :: "'a::euclidean_space set"
  shows "is_interval s \<Longrightarrow> connected s"
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

subsection \<open>On \<open>real\<close>, \<open>is_interval\<close>, \<open>convex\<close> and \<open>connected\<close> are all equivalent.\<close>

lemma is_interval_1:
  "is_interval (s::real set) \<longleftrightarrow> (\<forall>a\<in>s. \<forall>b\<in>s. \<forall> x. a \<le> x \<and> x \<le> b \<longrightarrow> x \<in> s)"
  unfolding is_interval_def by auto

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
    apply (rule_tac x = ?halfr in exI)
    apply rule
    apply (rule open_lessThan)
    apply rule
    apply (rule open_greaterThan)
    apply auto
    done
qed

lemma is_interval_convex_1:
  fixes s :: "real set"
  shows "is_interval s \<longleftrightarrow> convex s"
  by (metis is_interval_convex convex_connected is_interval_connected_1)

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
    using subspace_isomorphism [where 'a = 'a and 'b = real]
    by (metis DIM_real dim_UNIV subspace_UNIV assms)
  then have "f -` (f ` s) = s"
    by (simp add: inj_vimage_image_eq)
  then show ?thesis
    by (metis connected_convex_1 convex_linear_vimage linf convex_connected connected_linear_image)
qed

subsection \<open>Another intermediate value theorem formulation\<close>

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
    by (simp add: Topology_Euclidean_Space.connected_continuous_image assms)
qed

lemma ivt_increasing_component_1:
  fixes f :: "real \<Rightarrow> 'a::euclidean_space"
  shows "a \<le> b \<Longrightarrow> \<forall>x\<in>{a..b}. continuous (at x) f \<Longrightarrow>
    f a\<bullet>k \<le> y \<Longrightarrow> y \<le> f b\<bullet>k \<Longrightarrow> \<exists>x\<in>{a..b}. (f x)\<bullet>k = y"
  by (rule ivt_increasing_component_on_1) (auto simp add: continuous_at_imp_continuous_on)

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


subsection \<open>A bound within a convex hull, and so an interval\<close>

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

lemma set_sum_eq:
  "finite A \<Longrightarrow> (\<Sum>i\<in>A. B i) = {\<Sum>i\<in>A. f i |f. \<forall>i\<in>A. f i \<in> B i}"
  apply (induct set: finite)
  apply simp
  apply simp
  apply (safe elim!: set_plus_elim)
  apply (rule_tac x="fun_upd f x a" in exI)
  apply simp
  apply (rule_tac f="\<lambda>x. a + x" in arg_cong)
  apply (rule sum.cong [OF refl])
  apply clarsimp
  apply fast
  done

lemma box_eq_set_sum_Basis:
  shows "{x. \<forall>i\<in>Basis. x\<bullet>i \<in> B i} = (\<Sum>i\<in>Basis. image (\<lambda>x. x *\<^sub>R i) (B i))"
  apply (subst set_sum_eq [OF finite_Basis])
  apply safe
  apply (fast intro: euclidean_representation [symmetric])
  apply (subst inner_sum_left)
  apply (subgoal_tac "(\<Sum>x\<in>Basis. f x \<bullet> i) = f i \<bullet> i")
  apply (drule (1) bspec)
  apply clarsimp
  apply (frule sum.remove [OF finite_Basis])
  apply (erule trans)
  apply simp
  apply (rule sum.neutral)
  apply clarsimp
  apply (frule_tac x=i in bspec, assumption)
  apply (drule_tac x=x in bspec, assumption)
  apply clarsimp
  apply (cut_tac u=x and v=i in inner_Basis, assumption+)
  apply (rule ccontr)
  apply simp
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
  fix s assume "{x, y} \<subseteq> s" and "convex s"
  then show "cbox x y \<subseteq> s"
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
    by (simp only: convex_hull_linear_image linear_scaleR_left)
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
  obtains s :: "'a::euclidean_space set"
    where "finite s" and "cbox 0 (\<Sum>Basis) = convex hull s"
  apply (rule that[of "{x::'a. \<forall>i\<in>Basis. x\<bullet>i=0 \<or> x\<bullet>i=1}"])
  apply (rule finite_subset[of _ "(\<lambda>s. (\<Sum>i\<in>Basis. (if i\<in>s then 1 else 0) *\<^sub>R i)::'a) ` Pow Basis"])
  prefer 3
  apply (rule unit_interval_convex_hull)
  apply rule
  unfolding mem_Collect_eq
proof -
  fix x :: 'a
  assume as: "\<forall>i\<in>Basis. x \<bullet> i = 0 \<or> x \<bullet> i = 1"
  show "x \<in> (\<lambda>s. \<Sum>i\<in>Basis. (if i\<in>s then 1 else 0) *\<^sub>R i) ` Pow Basis"
    apply (rule image_eqI[where x="{i. i\<in>Basis \<and> x\<bullet>i = 1}"])
    using as
    apply (subst euclidean_eq_iff)
    apply auto
    done
qed auto

text \<open>Hence any cube (could do any nonempty interval).\<close>

lemma cube_convex_hull:
  assumes "d > 0"
  obtains s :: "'a::euclidean_space set" where
    "finite s" and "cbox (x - (\<Sum>i\<in>Basis. d*\<^sub>Ri)) (x + (\<Sum>i\<in>Basis. d*\<^sub>Ri)) = convex hull s"
proof -
  let ?d = "(\<Sum>i\<in>Basis. d*\<^sub>Ri)::'a"
  have *: "cbox (x - ?d) (x + ?d) = (\<lambda>y. x - ?d + (2 * d) *\<^sub>R y) ` cbox 0 (\<Sum>Basis)"
    apply (rule set_eqI, rule)
    unfolding image_iff
    defer
    apply (erule bexE)
  proof -
    fix y
    assume as: "y\<in>cbox (x - ?d) (x + ?d)"
    then have "inverse (2 * d) *\<^sub>R (y - (x - ?d)) \<in> cbox 0 (\<Sum>Basis)"
      using assms by (simp add: mem_box field_simps inner_simps)
    with \<open>0 < d\<close> show "\<exists>z\<in>cbox 0 (\<Sum>Basis). y = x - ?d + (2 * d) *\<^sub>R z"
      by (intro bexI[of _ "inverse (2 * d) *\<^sub>R (y - (x - ?d))"]) auto
  next
    fix y z
    assume as: "z\<in>cbox 0 (\<Sum>Basis)" "y = x - ?d + (2*d) *\<^sub>R z"
    have "\<And>i. i\<in>Basis \<Longrightarrow> 0 \<le> d * (z \<bullet> i) \<and> d * (z \<bullet> i) \<le> d"
      using assms as(1)[unfolded mem_box]
      apply (erule_tac x=i in ballE)
      apply rule
      prefer 2
      apply (rule mult_right_le_one_le)
      using assms
      apply auto
      done
    then show "y \<in> cbox (x - ?d) (x + ?d)"
      unfolding as(2) mem_box
      apply -
      apply rule
      using as(1)[unfolded mem_box]
      apply (erule_tac x=i in ballE)
      using assms
      apply (auto simp: inner_simps)
      done
  qed
  obtain s where "finite s" "cbox 0 (\<Sum>Basis::'a) = convex hull s"
    using unit_cube_convex_hull by auto
  then show ?thesis
    apply (rule_tac that[of "(\<lambda>y. x - ?d + (2 * d) *\<^sub>R y)` s"])
    unfolding * and convex_hull_affinity
    apply auto
    done
qed

subsubsection\<open>Representation of any interval as a finite convex hull\<close>

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
        by (auto simp add: field_simps)
      from False have
          "min (m i * (a \<bullet> i)) (m i * (b \<bullet> i)) = (if 0 < m i then m i * (a \<bullet> i) else m i * (b \<bullet> i))"
          "max (m i * (a \<bullet> i)) (m i * (b \<bullet> i)) = (if 0 < m i then m i * (b \<bullet> i) else m i * (a \<bullet> i))"
        using a_le_b by (auto simp: min_def max_def mult_le_cancel_left)
      with False show ?thesis using a_le_b
        unfolding * by (auto simp add: le_divide_eq divide_le_eq ac_simps)
    qed
  qed
qed simp

lemma interval_image_stretch_interval:
  "\<exists>u v. (\<lambda>x. \<Sum>k\<in>Basis. (m k * (x\<bullet>k))*\<^sub>R k) ` cbox a (b::'a::euclidean_space) = cbox u (v::'a::euclidean_space)"
  unfolding image_stretch_interval by auto

lemma cbox_translation: "cbox (c + a) (c + b) = image (\<lambda>x. c + x) (cbox a b)"
  using image_affinity_cbox [of 1 c a b]
  using box_ne_empty [of "a+c" "b+c"]  box_ne_empty [of a b]
  by (auto simp add: inner_left_distrib add.commute)

lemma cbox_image_unit_interval:
  fixes a :: "'a::euclidean_space"
  assumes "cbox a b \<noteq> {}"
    shows "cbox a b =
           op + a ` (\<lambda>x. \<Sum>k\<in>Basis. ((b \<bullet> k - a \<bullet> k) * (x \<bullet> k)) *\<^sub>R k) ` cbox 0 One"
using assms
apply (simp add: box_ne_empty image_stretch_interval cbox_translation [symmetric])
apply (simp add: min_def max_def algebra_simps sum_subtractf euclidean_representation)
done

lemma closed_interval_as_convex_hull:
  fixes a :: "'a::euclidean_space"
  obtains s where "finite s" "cbox a b = convex hull s"
proof (cases "cbox a b = {}")
  case True with convex_hull_empty that show ?thesis
    by blast
next
  case False
  obtain s::"'a set" where "finite s" and eq: "cbox 0 One = convex hull s"
    by (blast intro: unit_cube_convex_hull)
  have lin: "linear (\<lambda>x. \<Sum>k\<in>Basis. ((b \<bullet> k - a \<bullet> k) * (x \<bullet> k)) *\<^sub>R k)"
    by (rule linear_compose_sum) (auto simp: algebra_simps linearI)
  have "finite (op + a ` (\<lambda>x. \<Sum>k\<in>Basis. ((b \<bullet> k - a \<bullet> k) * (x \<bullet> k)) *\<^sub>R k) ` s)"
    by (rule finite_imageI \<open>finite s\<close>)+
  then show ?thesis
    apply (rule that)
    apply (simp add: convex_hull_translation convex_hull_linear_image [OF lin, symmetric])
    apply (simp add: eq [symmetric] cbox_image_unit_interval [OF False])
    done
qed


subsection \<open>Bounded convex function on open set is continuous\<close>

lemma convex_on_bounded_continuous:
  fixes s :: "('a::real_normed_vector) set"
  assumes "open s"
    and "convex_on s f"
    and "\<forall>x\<in>s. \<bar>f x\<bar> \<le> b"
  shows "continuous_on s f"
  apply (rule continuous_at_imp_continuous_on)
  unfolding continuous_at_real_range
proof (rule,rule,rule)
  fix x and e :: real
  assume "x \<in> s" "e > 0"
  define B where "B = \<bar>b\<bar> + 1"
  have B: "0 < B" "\<And>x. x\<in>s \<Longrightarrow> \<bar>f x\<bar> \<le> B"
    unfolding B_def
    defer
    apply (drule assms(3)[rule_format])
    apply auto
    done
  obtain k where "k > 0" and k: "cball x k \<subseteq> s"
    using assms(1)[unfolded open_contains_cball, THEN bspec[where x=x]]
    using \<open>x\<in>s\<close> by auto
  show "\<exists>d>0. \<forall>x'. norm (x' - x) < d \<longrightarrow> \<bar>f x' - f x\<bar> < e"
    apply (rule_tac x="min (k / 2) (e / (2 * B) * k)" in exI)
    apply rule
    defer
  proof (rule, rule)
    fix y
    assume as: "norm (y - x) < min (k / 2) (e / (2 * B) * k)"
    show "\<bar>f y - f x\<bar> < e"
    proof (cases "y = x")
      case False
      define t where "t = k / norm (y - x)"
      have "2 < t" "0<t"
        unfolding t_def using as False and \<open>k>0\<close>
        by (auto simp add:field_simps)
      have "y \<in> s"
        apply (rule k[unfolded subset_eq,rule_format])
        unfolding mem_cball dist_norm
        apply (rule order_trans[of _ "2 * norm (x - y)"])
        using as
        by (auto simp add: field_simps norm_minus_commute)
      {
        define w where "w = x + t *\<^sub>R (y - x)"
        have "w \<in> s"
          unfolding w_def
          apply (rule k[unfolded subset_eq,rule_format])
          unfolding mem_cball dist_norm
          unfolding t_def
          using \<open>k>0\<close>
          apply auto
          done
        have "(1 / t) *\<^sub>R x + - x + ((t - 1) / t) *\<^sub>R x = (1 / t - 1 + (t - 1) / t) *\<^sub>R x"
          by (auto simp add: algebra_simps)
        also have "\<dots> = 0"
          using \<open>t > 0\<close> by (auto simp add:field_simps)
        finally have w: "(1 / t) *\<^sub>R w + ((t - 1) / t) *\<^sub>R x = y"
          unfolding w_def using False and \<open>t > 0\<close>
          by (auto simp add: algebra_simps)
        have  "2 * B < e * t"
          unfolding t_def using \<open>0 < e\<close> \<open>0 < k\<close> \<open>B > 0\<close> and as and False
          by (auto simp add:field_simps)
        then have "(f w - f x) / t < e"
          using B(2)[OF \<open>w\<in>s\<close>] and B(2)[OF \<open>x\<in>s\<close>]
          using \<open>t > 0\<close> by (auto simp add:field_simps)
        then have th1: "f y - f x < e"
          apply -
          apply (rule le_less_trans)
          defer
          apply assumption
          using assms(2)[unfolded convex_on_def,rule_format,of w x "1/t" "(t - 1)/t", unfolded w]
          using \<open>0 < t\<close> \<open>2 < t\<close> and \<open>x \<in> s\<close> \<open>w \<in> s\<close>
          by (auto simp add:field_simps)
      }
      moreover
      {
        define w where "w = x - t *\<^sub>R (y - x)"
        have "w \<in> s"
          unfolding w_def
          apply (rule k[unfolded subset_eq,rule_format])
          unfolding mem_cball dist_norm
          unfolding t_def
          using \<open>k > 0\<close>
          apply auto
          done
        have "(1 / (1 + t)) *\<^sub>R x + (t / (1 + t)) *\<^sub>R x = (1 / (1 + t) + t / (1 + t)) *\<^sub>R x"
          by (auto simp add: algebra_simps)
        also have "\<dots> = x"
          using \<open>t > 0\<close> by (auto simp add:field_simps)
        finally have w: "(1 / (1+t)) *\<^sub>R w + (t / (1 + t)) *\<^sub>R y = x"
          unfolding w_def using False and \<open>t > 0\<close>
          by (auto simp add: algebra_simps)
        have "2 * B < e * t"
          unfolding t_def
          using \<open>0 < e\<close> \<open>0 < k\<close> \<open>B > 0\<close> and as and False
          by (auto simp add:field_simps)
        then have *: "(f w - f y) / t < e"
          using B(2)[OF \<open>w\<in>s\<close>] and B(2)[OF \<open>y\<in>s\<close>]
          using \<open>t > 0\<close>
          by (auto simp add:field_simps)
        have "f x \<le> 1 / (1 + t) * f w + (t / (1 + t)) * f y"
          using assms(2)[unfolded convex_on_def,rule_format,of w y "1/(1+t)" "t / (1+t)",unfolded w]
          using \<open>0 < t\<close> \<open>2 < t\<close> and \<open>y \<in> s\<close> \<open>w \<in> s\<close>
          by (auto simp add:field_simps)
        also have "\<dots> = (f w + t * f y) / (1 + t)"
          using \<open>t > 0\<close> by (auto simp add: divide_simps)
        also have "\<dots> < e + f y"
          using \<open>t > 0\<close> * \<open>e > 0\<close> by (auto simp add: field_simps)
        finally have "f x - f y < e" by auto
      }
      ultimately show ?thesis by auto
    qed (insert \<open>0<e\<close>, auto)
  qed (insert \<open>0<e\<close> \<open>0<k\<close> \<open>0<B\<close>, auto simp: field_simps)
qed


subsection \<open>Upper bound on a ball implies upper and lower bounds\<close>

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
    using y unfolding z_def mem_cball dist_norm * by (auto simp add: norm_minus_commute)
  have "(1 / 2) *\<^sub>R y + (1 / 2) *\<^sub>R z = x"
    unfolding z_def by (auto simp add: algebra_simps)
  then show "\<bar>f y\<bar> \<le> b + 2 * \<bar>f x\<bar>"
    using assms(1)[unfolded convex_on_def,rule_format, OF y z, of "1/2" "1/2"]
    using assms(2)[rule_format,OF y] assms(2)[rule_format,OF z]
    by (auto simp add:field_simps)
next
  case False
  fix y
  assume "y \<in> cball x e"
  then have "dist x y < 0"
    using False unfolding mem_cball not_le by (auto simp del: dist_not_less_zero)
  then show "\<bar>f y\<bar> \<le> b + 2 * \<bar>f x\<bar>"
    using zero_le_dist[of x y] by auto
qed


subsubsection \<open>Hence a convex function on an open set is continuous\<close>

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
      apply clarsimp
      apply (simp only: dist_norm)
      apply (subst inner_diff_left [symmetric])
      apply simp
      apply (erule (1) order_trans [OF Basis_le_norm])
      done
    have e': "e = (\<Sum>(i::'a)\<in>Basis. d)"
      by (simp add: d_def DIM_positive)
    show "convex hull c \<subseteq> cball x e"
      unfolding 2
      apply clarsimp
      apply (subst euclidean_dist_l2)
      apply (rule order_trans [OF setL2_le_sum])
      apply (rule zero_le_dist)
      unfolding e'
      apply (rule sum_mono)
      apply simp
      done
  qed
  define k where "k = Max (f ` c)"
  have "convex_on (convex hull c) f"
    apply(rule convex_on_subset[OF assms(2)])
    apply(rule subset_trans[OF _ e(1)])
    apply(rule c1)
    done
  then have k: "\<forall>y\<in>convex hull c. f y \<le> k"
    apply (rule_tac convex_on_convex_hull_bound)
    apply assumption
    unfolding k_def
    apply (rule, rule Max_ge)
    using c(1)
    apply auto
    done
  have "d \<le> e"
    unfolding d_def
    apply (rule mult_imp_div_pos_le)
    using \<open>e > 0\<close>
    unfolding mult_le_cancel_left1
    apply (auto simp: real_of_nat_ge_one_iff Suc_le_eq DIM_positive)
    done
  then have dsube: "cball x d \<subseteq> cball x e"
    by (rule subset_cball)
  have conv: "convex_on (cball x d) f"
    apply (rule convex_on_subset)
    apply (rule convex_on_subset[OF assms(2)])
    apply (rule e(1))
    apply (rule dsube)
    done
  then have "\<forall>y\<in>cball x d. \<bar>f y\<bar> \<le> k + 2 * \<bar>f x\<bar>"
    apply (rule convex_bounds_lemma)
    apply (rule ballI)
    apply (rule k [rule_format])
    apply (erule rev_subsetD)
    apply (rule c2)
    done
  then have "continuous_on (ball x d) f"
    apply (rule_tac convex_on_bounded_continuous)
    apply (rule open_ball, rule convex_on_subset[OF conv])
    apply (rule ball_subset_cball)
    apply force
    done
  then show "continuous (at x) f"
    unfolding continuous_on_eq_continuous_at[OF open_ball]
    using \<open>d > 0\<close> by auto
qed


subsection \<open>Line segments, Starlike Sets, etc.\<close>

definition midpoint :: "'a::real_vector \<Rightarrow> 'a \<Rightarrow> 'a"
  where "midpoint a b = (inverse (2::real)) *\<^sub>R (a + b)"

definition closed_segment :: "'a::real_vector \<Rightarrow> 'a \<Rightarrow> 'a set"
  where "closed_segment a b = {(1 - u) *\<^sub>R a + u *\<^sub>R b | u::real. 0 \<le> u \<and> u \<le> 1}"

definition open_segment :: "'a::real_vector \<Rightarrow> 'a \<Rightarrow> 'a set" where
  "open_segment a b \<equiv> closed_segment a b - {a,b}"

lemmas segment = open_segment_def closed_segment_def

lemma in_segment:
    "x \<in> closed_segment a b \<longleftrightarrow> (\<exists>u. 0 \<le> u \<and> u \<le> 1 \<and> x = (1 - u) *\<^sub>R a + u *\<^sub>R b)"
    "x \<in> open_segment a b \<longleftrightarrow> a \<noteq> b \<and> (\<exists>u. 0 < u \<and> u < 1 \<and> x = (1 - u) *\<^sub>R a + u *\<^sub>R b)"
  using less_eq_real_def by (auto simp: segment algebra_simps)

lemma closed_segment_linear_image:
    "linear f \<Longrightarrow> closed_segment (f a) (f b) = f ` (closed_segment a b)"
  by (force simp add: in_segment linear_add_cmul)

lemma open_segment_linear_image:
    "\<lbrakk>linear f; inj f\<rbrakk> \<Longrightarrow> open_segment (f a) (f b) = f ` (open_segment a b)"
  by (force simp: open_segment_def closed_segment_linear_image inj_on_def)

lemma closed_segment_translation:
    "closed_segment (c + a) (c + b) = image (\<lambda>x. c + x) (closed_segment a b)"
apply safe
apply (rule_tac x="x-c" in image_eqI)
apply (auto simp: in_segment algebra_simps)
done

lemma open_segment_translation:
    "open_segment (c + a) (c + b) = image (\<lambda>x. c + x) (open_segment a b)"
by (simp add: open_segment_def closed_segment_translation translation_diff)

lemma closed_segment_of_real:
    "closed_segment (of_real x) (of_real y) = of_real ` closed_segment x y"
  apply (auto simp: image_iff in_segment scaleR_conv_of_real)
    apply (rule_tac x="(1-u)*x + u*y" in bexI)
  apply (auto simp: in_segment)
  done

lemma open_segment_of_real:
    "open_segment (of_real x) (of_real y) = of_real ` open_segment x y"
  apply (auto simp: image_iff in_segment scaleR_conv_of_real)
    apply (rule_tac x="(1-u)*x + u*y" in bexI)
  apply (auto simp: in_segment)
  done

lemma closed_segment_Reals:
    "\<lbrakk>x \<in> Reals; y \<in> Reals\<rbrakk> \<Longrightarrow> closed_segment x y = of_real ` closed_segment (Re x) (Re y)"
  by (metis closed_segment_of_real of_real_Re)

lemma open_segment_Reals:
    "\<lbrakk>x \<in> Reals; y \<in> Reals\<rbrakk> \<Longrightarrow> open_segment x y = of_real ` open_segment (Re x) (Re y)"
  by (metis open_segment_of_real of_real_Re)

lemma open_segment_PairD:
    "(x, x') \<in> open_segment (a, a') (b, b')
     \<Longrightarrow> (x \<in> open_segment a b \<or> a = b) \<and> (x' \<in> open_segment a' b' \<or> a' = b')"
  by (auto simp: in_segment)

lemma closed_segment_PairD:
  "(x, x') \<in> closed_segment (a, a') (b, b') \<Longrightarrow> x \<in> closed_segment a b \<and> x' \<in> closed_segment a' b'"
  by (auto simp: closed_segment_def)

lemma closed_segment_translation_eq [simp]:
    "d + x \<in> closed_segment (d + a) (d + b) \<longleftrightarrow> x \<in> closed_segment a b"
proof -
  have *: "\<And>d x a b. x \<in> closed_segment a b \<Longrightarrow> d + x \<in> closed_segment (d + a) (d + b)"
    apply (simp add: closed_segment_def)
    apply (erule ex_forward)
    apply (simp add: algebra_simps)
    done
  show ?thesis
  using * [where d = "-d"] *
  by (fastforce simp add:)
qed

lemma open_segment_translation_eq [simp]:
    "d + x \<in> open_segment (d + a) (d + b) \<longleftrightarrow> x \<in> open_segment a b"
  by (simp add: open_segment_def)

lemma of_real_closed_segment [simp]:
  "of_real x \<in> closed_segment (of_real a) (of_real b) \<longleftrightarrow> x \<in> closed_segment a b"
  apply (auto simp: in_segment scaleR_conv_of_real elim!: ex_forward)
  using of_real_eq_iff by fastforce

lemma of_real_open_segment [simp]:
  "of_real x \<in> open_segment (of_real a) (of_real b) \<longleftrightarrow> x \<in> open_segment a b"
  apply (auto simp: in_segment scaleR_conv_of_real elim!: ex_forward del: exE)
  using of_real_eq_iff by fastforce

lemma midpoint_idem [simp]: "midpoint x x = x"
  unfolding midpoint_def
  unfolding scaleR_right_distrib
  unfolding scaleR_left_distrib[symmetric]
  by auto

lemma midpoint_sym: "midpoint a b = midpoint b a"
  unfolding midpoint_def by (auto simp add: scaleR_right_distrib)

lemma midpoint_eq_iff: "midpoint a b = c \<longleftrightarrow> a + b = c + c"
proof -
  have "midpoint a b = c \<longleftrightarrow> scaleR 2 (midpoint a b) = scaleR 2 c"
    by simp
  then show ?thesis
    unfolding midpoint_def scaleR_2 [symmetric] by simp
qed

lemma
  fixes a::real
  assumes "a \<le> b" shows ge_midpoint_1: "a \<le> midpoint a b"
                    and le_midpoint_1: "midpoint a b \<le> b"
  by (simp_all add: midpoint_def assms)

lemma dist_midpoint:
  fixes a b :: "'a::real_normed_vector" shows
  "dist a (midpoint a b) = (dist a b) / 2" (is ?t1)
  "dist b (midpoint a b) = (dist a b) / 2" (is ?t2)
  "dist (midpoint a b) a = (dist a b) / 2" (is ?t3)
  "dist (midpoint a b) b = (dist a b) / 2" (is ?t4)
proof -
  have *: "\<And>x y::'a. 2 *\<^sub>R x = - y \<Longrightarrow> norm x = (norm y) / 2"
    unfolding equation_minus_iff by auto
  have **: "\<And>x y::'a. 2 *\<^sub>R x =   y \<Longrightarrow> norm x = (norm y) / 2"
    by auto
  note scaleR_right_distrib [simp]
  show ?t1
    unfolding midpoint_def dist_norm
    apply (rule **)
    apply (simp add: scaleR_right_diff_distrib)
    apply (simp add: scaleR_2)
    done
  show ?t2
    unfolding midpoint_def dist_norm
    apply (rule *)
    apply (simp add: scaleR_right_diff_distrib)
    apply (simp add: scaleR_2)
    done
  show ?t3
    unfolding midpoint_def dist_norm
    apply (rule *)
    apply (simp add: scaleR_right_diff_distrib)
    apply (simp add: scaleR_2)
    done
  show ?t4
    unfolding midpoint_def dist_norm
    apply (rule **)
    apply (simp add: scaleR_right_diff_distrib)
    apply (simp add: scaleR_2)
    done
qed

lemma midpoint_eq_endpoint [simp]:
  "midpoint a b = a \<longleftrightarrow> a = b"
  "midpoint a b = b \<longleftrightarrow> a = b"
  unfolding midpoint_eq_iff by auto

lemma midpoint_plus_self [simp]: "midpoint a b + midpoint a b = a + b"
  using midpoint_eq_iff by metis

lemma midpoint_linear_image:
   "linear f \<Longrightarrow> midpoint(f a)(f b) = f(midpoint a b)"
by (simp add: linear_iff midpoint_def)

subsection\<open>Starlike sets\<close>

definition "starlike S \<longleftrightarrow> (\<exists>a\<in>S. \<forall>x\<in>S. closed_segment a x \<subseteq> S)"

lemma starlike_UNIV [simp]: "starlike UNIV"
  by (simp add: starlike_def)

lemma convex_contains_segment:
  "convex S \<longleftrightarrow> (\<forall>a\<in>S. \<forall>b\<in>S. closed_segment a b \<subseteq> S)"
  unfolding convex_alt closed_segment_def by auto

lemma closed_segment_subset: "\<lbrakk>x \<in> S; y \<in> S; convex S\<rbrakk> \<Longrightarrow> closed_segment x y \<subseteq> S"
  by (simp add: convex_contains_segment)

lemma closed_segment_subset_convex_hull:
    "\<lbrakk>x \<in> convex hull S; y \<in> convex hull S\<rbrakk> \<Longrightarrow> closed_segment x y \<subseteq> convex hull S"
  using convex_contains_segment by blast

lemma convex_imp_starlike:
  "convex S \<Longrightarrow> S \<noteq> {} \<Longrightarrow> starlike S"
  unfolding convex_contains_segment starlike_def by auto

lemma segment_convex_hull:
  "closed_segment a b = convex hull {a,b}"
proof -
  have *: "\<And>x. {x} \<noteq> {}" by auto
  show ?thesis
    unfolding segment convex_hull_insert[OF *] convex_hull_singleton
    by (safe; rule_tac x="1 - u" in exI; force)
qed

lemma open_closed_segment: "u \<in> open_segment w z \<Longrightarrow> u \<in> closed_segment w z"
  by (auto simp add: closed_segment_def open_segment_def)

lemma segment_open_subset_closed:
   "open_segment a b \<subseteq> closed_segment a b"
  by (auto simp: closed_segment_def open_segment_def)

lemma bounded_closed_segment:
    fixes a :: "'a::euclidean_space" shows "bounded (closed_segment a b)"
  by (simp add: segment_convex_hull compact_convex_hull compact_imp_bounded)

lemma bounded_open_segment:
    fixes a :: "'a::euclidean_space" shows "bounded (open_segment a b)"
  by (rule bounded_subset [OF bounded_closed_segment segment_open_subset_closed])

lemmas bounded_segment = bounded_closed_segment open_closed_segment

lemma ends_in_segment [iff]: "a \<in> closed_segment a b" "b \<in> closed_segment a b"
  unfolding segment_convex_hull
  by (auto intro!: hull_subset[unfolded subset_eq, rule_format])

lemma eventually_closed_segment:
  fixes x0::"'a::real_normed_vector"
  assumes "open X0" "x0 \<in> X0"
  shows "\<forall>\<^sub>F x in at x0 within U. closed_segment x0 x \<subseteq> X0"
proof -
  from openE[OF assms]
  obtain e where e: "0 < e" "ball x0 e \<subseteq> X0" .
  then have "\<forall>\<^sub>F x in at x0 within U. x \<in> ball x0 e"
    by (auto simp: dist_commute eventually_at)
  then show ?thesis
  proof eventually_elim
    case (elim x)
    have "x0 \<in> ball x0 e" using \<open>e > 0\<close> by simp
    from convex_ball[unfolded convex_contains_segment, rule_format, OF this elim]
    have "closed_segment x0 x \<subseteq> ball x0 e" .
    also note \<open>\<dots> \<subseteq> X0\<close>
    finally show ?case .
  qed
qed

lemma segment_furthest_le:
  fixes a b x y :: "'a::euclidean_space"
  assumes "x \<in> closed_segment a b"
  shows "norm (y - x) \<le> norm (y - a) \<or>  norm (y - x) \<le> norm (y - b)"
proof -
  obtain z where "z \<in> {a, b}" "norm (x - y) \<le> norm (z - y)"
    using simplex_furthest_le[of "{a, b}" y]
    using assms[unfolded segment_convex_hull]
    by auto
  then show ?thesis
    by (auto simp add:norm_minus_commute)
qed

lemma closed_segment_commute: "closed_segment a b = closed_segment b a"
proof -
  have "{a, b} = {b, a}" by auto
  thus ?thesis
    by (simp add: segment_convex_hull)
qed

lemma segment_bound1:
  assumes "x \<in> closed_segment a b"
  shows "norm (x - a) \<le> norm (b - a)"
proof -
  obtain u where "x = (1 - u) *\<^sub>R a + u *\<^sub>R b" "0 \<le> u" "u \<le> 1"
    using assms by (auto simp add: closed_segment_def)
  then show "norm (x - a) \<le> norm (b - a)"
    apply clarify
    apply (auto simp: algebra_simps)
    apply (simp add: scaleR_diff_right [symmetric] mult_left_le_one_le)
    done
qed

lemma segment_bound:
  assumes "x \<in> closed_segment a b"
  shows "norm (x - a) \<le> norm (b - a)" "norm (x - b) \<le> norm (b - a)"
apply (simp add: assms segment_bound1)
by (metis assms closed_segment_commute dist_commute dist_norm segment_bound1)

lemma open_segment_commute: "open_segment a b = open_segment b a"
proof -
  have "{a, b} = {b, a}" by auto
  thus ?thesis
    by (simp add: closed_segment_commute open_segment_def)
qed

lemma closed_segment_idem [simp]: "closed_segment a a = {a}"
  unfolding segment by (auto simp add: algebra_simps)

lemma open_segment_idem [simp]: "open_segment a a = {}"
  by (simp add: open_segment_def)

lemma closed_segment_eq_open: "closed_segment a b = open_segment a b \<union> {a,b}"
  using open_segment_def by auto

lemma convex_contains_open_segment:
  "convex s \<longleftrightarrow> (\<forall>a\<in>s. \<forall>b\<in>s. open_segment a b \<subseteq> s)"
  by (simp add: convex_contains_segment closed_segment_eq_open)

lemma closed_segment_eq_real_ivl:
  fixes a b::real
  shows "closed_segment a b = (if a \<le> b then {a .. b} else {b .. a})"
proof -
  have "b \<le> a \<Longrightarrow> closed_segment b a = {b .. a}"
    and "a \<le> b \<Longrightarrow> closed_segment a b = {a .. b}"
    by (auto simp: convex_hull_eq_real_cbox segment_convex_hull)
  thus ?thesis
    by (auto simp: closed_segment_commute)
qed

lemma open_segment_eq_real_ivl:
  fixes a b::real
  shows "open_segment a b = (if a \<le> b then {a<..<b} else {b<..<a})"
by (auto simp: closed_segment_eq_real_ivl open_segment_def split: if_split_asm)

lemma closed_segment_real_eq:
  fixes u::real shows "closed_segment u v = (\<lambda>x. (v - u) * x + u) ` {0..1}"
  by (simp add: add.commute [of u] image_affinity_atLeastAtMost [where c=u] closed_segment_eq_real_ivl)

lemma dist_in_closed_segment:
  fixes a :: "'a :: euclidean_space"
  assumes "x \<in> closed_segment a b"
    shows "dist x a \<le> dist a b \<and> dist x b \<le> dist a b"
proof (intro conjI)
  obtain u where u: "0 \<le> u" "u \<le> 1" and x: "x = (1 - u) *\<^sub>R a + u *\<^sub>R b"
    using assms by (force simp: in_segment algebra_simps)
  have "dist x a = u * dist a b"
    apply (simp add: dist_norm algebra_simps x)
    by (metis \<open>0 \<le> u\<close> abs_of_nonneg norm_minus_commute norm_scaleR real_vector.scale_right_diff_distrib)
  also have "...  \<le> dist a b"
    by (simp add: mult_left_le_one_le u)
  finally show "dist x a \<le> dist a b" .
  have "dist x b = norm ((1-u) *\<^sub>R a - (1-u) *\<^sub>R b)"
    by (simp add: dist_norm algebra_simps x)
  also have "... = (1-u) * dist a b"
  proof -
    have "norm ((1 - 1 * u) *\<^sub>R (a - b)) = (1 - 1 * u) * norm (a - b)"
      using \<open>u \<le> 1\<close> by force
    then show ?thesis                     
      by (simp add: dist_norm real_vector.scale_right_diff_distrib)
  qed
  also have "... \<le> dist a b"
    by (simp add: mult_left_le_one_le u)
  finally show "dist x b \<le> dist a b" .
qed

lemma dist_in_open_segment:
  fixes a :: "'a :: euclidean_space"
  assumes "x \<in> open_segment a b"
    shows "dist x a < dist a b \<and> dist x b < dist a b"
proof (intro conjI)
  obtain u where u: "0 < u" "u < 1" and x: "x = (1 - u) *\<^sub>R a + u *\<^sub>R b"
    using assms by (force simp: in_segment algebra_simps)
  have "dist x a = u * dist a b"
    apply (simp add: dist_norm algebra_simps x)
    by (metis abs_of_nonneg less_eq_real_def norm_minus_commute norm_scaleR real_vector.scale_right_diff_distrib \<open>0 < u\<close>)
  also have *: "...  < dist a b"
    by (metis (no_types) assms dist_eq_0_iff dist_not_less_zero in_segment(2) linorder_neqE_linordered_idom mult.left_neutral real_mult_less_iff1 \<open>u < 1\<close>)
  finally show "dist x a < dist a b" .
  have ab_ne0: "dist a b \<noteq> 0"
    using * by fastforce
  have "dist x b = norm ((1-u) *\<^sub>R a - (1-u) *\<^sub>R b)"
    by (simp add: dist_norm algebra_simps x)
  also have "... = (1-u) * dist a b"
  proof -
    have "norm ((1 - 1 * u) *\<^sub>R (a - b)) = (1 - 1 * u) * norm (a - b)"
      using \<open>u < 1\<close> by force
    then show ?thesis
      by (simp add: dist_norm real_vector.scale_right_diff_distrib)
  qed
  also have "... < dist a b"
    using ab_ne0 \<open>0 < u\<close> by simp
  finally show "dist x b < dist a b" .
qed

lemma dist_decreases_open_segment_0:
  fixes x :: "'a :: euclidean_space"
  assumes "x \<in> open_segment 0 b"
    shows "dist c x < dist c 0 \<or> dist c x < dist c b"
proof (rule ccontr, clarsimp simp: not_less)
  obtain u where u: "0 \<noteq> b" "0 < u" "u < 1" and x: "x = u *\<^sub>R b"
    using assms by (auto simp: in_segment)
  have xb: "x \<bullet> b < b \<bullet> b"
    using u x by auto
  assume "norm c \<le> dist c x"
  then have "c \<bullet> c \<le> (c - x) \<bullet> (c - x)"
    by (simp add: dist_norm norm_le)
  moreover have "0 < x \<bullet> b"
    using u x by auto
  ultimately have less: "c \<bullet> b < x \<bullet> b"
    by (simp add: x algebra_simps inner_commute u)
  assume "dist c b \<le> dist c x"
  then have "(c - b) \<bullet> (c - b) \<le> (c - x) \<bullet> (c - x)"
    by (simp add: dist_norm norm_le)
  then have "(b \<bullet> b) * (1 - u*u) \<le> 2 * (b \<bullet> c) * (1-u)"
    by (simp add: x algebra_simps inner_commute)
  then have "(1+u) * (b \<bullet> b) * (1-u) \<le> 2 * (b \<bullet> c) * (1-u)"
    by (simp add: algebra_simps)
  then have "(1+u) * (b \<bullet> b) \<le> 2 * (b \<bullet> c)"
    using \<open>u < 1\<close> by auto
  with xb have "c \<bullet> b \<ge> x \<bullet> b"
    by (auto simp: x algebra_simps inner_commute)
  with less show False by auto
qed

proposition dist_decreases_open_segment:
  fixes a :: "'a :: euclidean_space"
  assumes "x \<in> open_segment a b"
    shows "dist c x < dist c a \<or> dist c x < dist c b"
proof -
  have *: "x - a \<in> open_segment 0 (b - a)" using assms
    by (metis diff_self open_segment_translation_eq uminus_add_conv_diff)
  show ?thesis
    using dist_decreases_open_segment_0 [OF *, of "c-a"] assms
    by (simp add: dist_norm)
qed

corollary open_segment_furthest_le:
  fixes a b x y :: "'a::euclidean_space"
  assumes "x \<in> open_segment a b"
  shows "norm (y - x) < norm (y - a) \<or>  norm (y - x) < norm (y - b)"
  by (metis assms dist_decreases_open_segment dist_norm)

corollary dist_decreases_closed_segment:
  fixes a :: "'a :: euclidean_space"
  assumes "x \<in> closed_segment a b"
    shows "dist c x \<le> dist c a \<or> dist c x \<le> dist c b"
apply (cases "x \<in> open_segment a b")
 using dist_decreases_open_segment less_eq_real_def apply blast
by (metis DiffI assms empty_iff insertE open_segment_def order_refl)

lemma convex_intermediate_ball:
  fixes a :: "'a :: euclidean_space"
  shows "\<lbrakk>ball a r \<subseteq> T; T \<subseteq> cball a r\<rbrakk> \<Longrightarrow> convex T"
apply (simp add: convex_contains_open_segment, clarify)
by (metis (no_types, hide_lams) less_le_trans mem_ball mem_cball subsetCE dist_decreases_open_segment)

lemma csegment_midpoint_subset: "closed_segment (midpoint a b) b \<subseteq> closed_segment a b"
  apply (clarsimp simp: midpoint_def in_segment)
  apply (rule_tac x="(1 + u) / 2" in exI)
  apply (auto simp: algebra_simps add_divide_distrib diff_divide_distrib)
  by (metis real_sum_of_halves scaleR_left.add)

lemma notin_segment_midpoint:
  fixes a :: "'a :: euclidean_space"
  shows "a \<noteq> b \<Longrightarrow> a \<notin> closed_segment (midpoint a b) b"
by (auto simp: dist_midpoint dest!: dist_in_closed_segment)

lemma segment_to_closest_point:
  fixes S :: "'a :: euclidean_space set"
  shows "\<lbrakk>closed S; S \<noteq> {}\<rbrakk> \<Longrightarrow> open_segment a (closest_point S a) \<inter> S = {}"
  apply (subst disjoint_iff_not_equal)
  apply (clarify dest!: dist_in_open_segment)
  by (metis closest_point_le dist_commute le_less_trans less_irrefl)

lemma segment_to_point_exists:
  fixes S :: "'a :: euclidean_space set"
    assumes "closed S" "S \<noteq> {}"
    obtains b where "b \<in> S" "open_segment a b \<inter> S = {}"
  by (metis assms segment_to_closest_point closest_point_exists that)

subsubsection\<open>More lemmas, especially for working with the underlying formula\<close>

lemma segment_eq_compose:
  fixes a :: "'a :: real_vector"
  shows "(\<lambda>u. (1 - u) *\<^sub>R a + u *\<^sub>R b) = (\<lambda>x. a + x) o (\<lambda>u. u *\<^sub>R (b - a))"
    by (simp add: o_def algebra_simps)

lemma segment_degen_1:
  fixes a :: "'a :: real_vector"
  shows "(1 - u) *\<^sub>R a + u *\<^sub>R b = b \<longleftrightarrow> a=b \<or> u=1"
proof -
  { assume "(1 - u) *\<^sub>R a + u *\<^sub>R b = b"
    then have "(1 - u) *\<^sub>R a = (1 - u) *\<^sub>R b"
      by (simp add: algebra_simps)
    then have "a=b \<or> u=1"
      by simp
  } then show ?thesis
      by (auto simp: algebra_simps)
qed

lemma segment_degen_0:
    fixes a :: "'a :: real_vector"
    shows "(1 - u) *\<^sub>R a + u *\<^sub>R b = a \<longleftrightarrow> a=b \<or> u=0"
  using segment_degen_1 [of "1-u" b a]
  by (auto simp: algebra_simps)

lemma add_scaleR_degen:
  fixes a b ::"'a::real_vector"
  assumes  "(u *\<^sub>R b + v *\<^sub>R a) = (u *\<^sub>R a + v *\<^sub>R b)"  "u \<noteq> v"
  shows "a=b"
  by (metis (no_types, hide_lams) add.commute add_diff_eq diff_add_cancel real_vector.scale_cancel_left real_vector.scale_left_diff_distrib assms)
  
lemma closed_segment_image_interval:
     "closed_segment a b = (\<lambda>u. (1 - u) *\<^sub>R a + u *\<^sub>R b) ` {0..1}"
  by (auto simp: set_eq_iff image_iff closed_segment_def)

lemma open_segment_image_interval:
     "open_segment a b = (if a=b then {} else (\<lambda>u. (1 - u) *\<^sub>R a + u *\<^sub>R b) ` {0<..<1})"
  by (auto simp:  open_segment_def closed_segment_def segment_degen_0 segment_degen_1)

lemmas segment_image_interval = closed_segment_image_interval open_segment_image_interval

lemma open_segment_bound1:
  assumes "x \<in> open_segment a b"
  shows "norm (x - a) < norm (b - a)"
proof -
  obtain u where "x = (1 - u) *\<^sub>R a + u *\<^sub>R b" "0 < u" "u < 1" "a \<noteq> b"
    using assms by (auto simp add: open_segment_image_interval split: if_split_asm)
  then show "norm (x - a) < norm (b - a)"
    apply clarify
    apply (auto simp: algebra_simps)
    apply (simp add: scaleR_diff_right [symmetric])
    done
qed

lemma compact_segment [simp]:
  fixes a :: "'a::real_normed_vector"
  shows "compact (closed_segment a b)"
  by (auto simp: segment_image_interval intro!: compact_continuous_image continuous_intros)

lemma closed_segment [simp]:
  fixes a :: "'a::real_normed_vector"
  shows "closed (closed_segment a b)"
  by (simp add: compact_imp_closed)

lemma closure_closed_segment [simp]:
  fixes a :: "'a::real_normed_vector"
  shows "closure(closed_segment a b) = closed_segment a b"
  by simp

lemma open_segment_bound:
  assumes "x \<in> open_segment a b"
  shows "norm (x - a) < norm (b - a)" "norm (x - b) < norm (b - a)"
apply (simp add: assms open_segment_bound1)
by (metis assms norm_minus_commute open_segment_bound1 open_segment_commute)

lemma closure_open_segment [simp]:
    fixes a :: "'a::euclidean_space"
    shows "closure(open_segment a b) = (if a = b then {} else closed_segment a b)"
proof -
  have "closure ((\<lambda>u. u *\<^sub>R (b - a)) ` {0<..<1}) = (\<lambda>u. u *\<^sub>R (b - a)) ` closure {0<..<1}" if "a \<noteq> b"
    apply (rule closure_injective_linear_image [symmetric])
    apply (simp add:)
    using that by (simp add: inj_on_def)
  then show ?thesis
    by (simp add: segment_image_interval segment_eq_compose closure_greaterThanLessThan [symmetric]
         closure_translation image_comp [symmetric] del: closure_greaterThanLessThan)
qed

lemma closed_open_segment_iff [simp]:
    fixes a :: "'a::euclidean_space"  shows "closed(open_segment a b) \<longleftrightarrow> a = b"
  by (metis open_segment_def DiffE closure_eq closure_open_segment ends_in_segment(1) insert_iff segment_image_interval(2))

lemma compact_open_segment_iff [simp]:
    fixes a :: "'a::euclidean_space"  shows "compact(open_segment a b) \<longleftrightarrow> a = b"
  by (simp add: bounded_open_segment compact_eq_bounded_closed)

lemma convex_closed_segment [iff]: "convex (closed_segment a b)"
  unfolding segment_convex_hull by(rule convex_convex_hull)

lemma convex_open_segment [iff]: "convex(open_segment a b)"
proof -
  have "convex ((\<lambda>u. u *\<^sub>R (b-a)) ` {0<..<1})"
    by (rule convex_linear_image) auto
  then show ?thesis
    apply (simp add: open_segment_image_interval segment_eq_compose)
    by (metis image_comp convex_translation)
qed


lemmas convex_segment = convex_closed_segment convex_open_segment

lemma connected_segment [iff]:
  fixes x :: "'a :: real_normed_vector"
  shows "connected (closed_segment x y)"
  by (simp add: convex_connected)

lemma affine_hull_closed_segment [simp]:
     "affine hull (closed_segment a b) = affine hull {a,b}"
  by (simp add: segment_convex_hull)

lemma affine_hull_open_segment [simp]:
    fixes a :: "'a::euclidean_space"
    shows "affine hull (open_segment a b) = (if a = b then {} else affine hull {a,b})"
by (metis affine_hull_convex_hull affine_hull_empty closure_open_segment closure_same_affine_hull segment_convex_hull)

lemma rel_interior_closure_convex_segment:
  fixes S :: "_::euclidean_space set"
  assumes "convex S" "a \<in> rel_interior S" "b \<in> closure S"
    shows "open_segment a b \<subseteq> rel_interior S"
proof
  fix x
  have [simp]: "(1 - u) *\<^sub>R a + u *\<^sub>R b = b - (1 - u) *\<^sub>R (b - a)" for u
    by (simp add: algebra_simps)
  assume "x \<in> open_segment a b"
  then show "x \<in> rel_interior S"
    unfolding closed_segment_def open_segment_def  using assms
    by (auto intro: rel_interior_closure_convex_shrink)
qed

lemma convex_hull_insert_segments:
   "convex hull (insert a S) =
    (if S = {} then {a} else  \<Union>x \<in> convex hull S. closed_segment a x)"
  by (force simp add: convex_hull_insert_alt in_segment)

lemma Int_convex_hull_insert_rel_exterior:
  fixes z :: "'a::euclidean_space"
  assumes "convex C" "T \<subseteq> C" and z: "z \<in> rel_interior C" and dis: "disjnt S (rel_interior C)"
  shows "S \<inter> (convex hull (insert z T)) = S \<inter> (convex hull T)" (is "?lhs = ?rhs")
proof
  have "T = {} \<Longrightarrow> z \<notin> S"
    using dis z by (auto simp add: disjnt_def)
  then show "?lhs \<subseteq> ?rhs"
  proof (clarsimp simp add: convex_hull_insert_segments)
    fix x y
    assume "x \<in> S" and y: "y \<in> convex hull T" and "x \<in> closed_segment z y"
    have "y \<in> closure C"
      by (metis y \<open>convex C\<close> \<open>T \<subseteq> C\<close> closure_subset contra_subsetD convex_hull_eq hull_mono)
    moreover have "x \<notin> rel_interior C"
      by (meson \<open>x \<in> S\<close> dis disjnt_iff)
    moreover have "x \<in> open_segment z y \<union> {z, y}"
      using \<open>x \<in> closed_segment z y\<close> closed_segment_eq_open by blast
    ultimately show "x \<in> convex hull T"
      using rel_interior_closure_convex_segment [OF \<open>convex C\<close> z]
      using y z by blast
  qed
  show "?rhs \<subseteq> ?lhs"
    by (meson hull_mono inf_mono subset_insertI subset_refl)
qed

subsection\<open>More results about segments\<close>

lemma dist_half_times2:
  fixes a :: "'a :: real_normed_vector"
  shows "dist ((1 / 2) *\<^sub>R (a + b)) x * 2 = dist (a+b) (2 *\<^sub>R x)"
proof -
  have "norm ((1 / 2) *\<^sub>R (a + b) - x) * 2 = norm (2 *\<^sub>R ((1 / 2) *\<^sub>R (a + b) - x))"
    by simp
  also have "... = norm ((a + b) - 2 *\<^sub>R x)"
    by (simp add: real_vector.scale_right_diff_distrib)
  finally show ?thesis
    by (simp only: dist_norm)
qed

lemma closed_segment_as_ball:
    "closed_segment a b = affine hull {a,b} \<inter> cball(inverse 2 *\<^sub>R (a + b))(norm(b - a) / 2)"
proof (cases "b = a")
  case True then show ?thesis by (auto simp: hull_inc)
next
  case False
  then have *: "((\<exists>u v. x = u *\<^sub>R a + v *\<^sub>R b \<and> u + v = 1) \<and>
                  dist ((1 / 2) *\<^sub>R (a + b)) x * 2 \<le> norm (b - a)) =
                 (\<exists>u. x = (1 - u) *\<^sub>R a + u *\<^sub>R b \<and> 0 \<le> u \<and> u \<le> 1)" for x
  proof -
    have "((\<exists>u v. x = u *\<^sub>R a + v *\<^sub>R b \<and> u + v = 1) \<and>
                  dist ((1 / 2) *\<^sub>R (a + b)) x * 2 \<le> norm (b - a)) =
          ((\<exists>u. x = (1 - u) *\<^sub>R a + u *\<^sub>R b) \<and>
                  dist ((1 / 2) *\<^sub>R (a + b)) x * 2 \<le> norm (b - a))"
      unfolding eq_diff_eq [symmetric] by simp
    also have "... = (\<exists>u. x = (1 - u) *\<^sub>R a + u *\<^sub>R b \<and>
                          norm ((a+b) - (2 *\<^sub>R x)) \<le> norm (b - a))"
      by (simp add: dist_half_times2) (simp add: dist_norm)
    also have "... = (\<exists>u. x = (1 - u) *\<^sub>R a + u *\<^sub>R b \<and>
            norm ((a+b) - (2 *\<^sub>R ((1 - u) *\<^sub>R a + u *\<^sub>R b))) \<le> norm (b - a))"
      by auto
    also have "... = (\<exists>u. x = (1 - u) *\<^sub>R a + u *\<^sub>R b \<and>
                norm ((1 - u * 2) *\<^sub>R (b - a)) \<le> norm (b - a))"
      by (simp add: algebra_simps scaleR_2)
    also have "... = (\<exists>u. x = (1 - u) *\<^sub>R a + u *\<^sub>R b \<and>
                          \<bar>1 - u * 2\<bar> * norm (b - a) \<le> norm (b - a))"
      by simp
    also have "... = (\<exists>u. x = (1 - u) *\<^sub>R a + u *\<^sub>R b \<and> \<bar>1 - u * 2\<bar> \<le> 1)"
      by (simp add: mult_le_cancel_right2 False)
    also have "... = (\<exists>u. x = (1 - u) *\<^sub>R a + u *\<^sub>R b \<and> 0 \<le> u \<and> u \<le> 1)"
      by auto
    finally show ?thesis .
  qed
  show ?thesis
    by (simp add: affine_hull_2 Set.set_eq_iff closed_segment_def *)
qed

lemma open_segment_as_ball:
    "open_segment a b =
     affine hull {a,b} \<inter> ball(inverse 2 *\<^sub>R (a + b))(norm(b - a) / 2)"
proof (cases "b = a")
  case True then show ?thesis by (auto simp: hull_inc)
next
  case False
  then have *: "((\<exists>u v. x = u *\<^sub>R a + v *\<^sub>R b \<and> u + v = 1) \<and>
                  dist ((1 / 2) *\<^sub>R (a + b)) x * 2 < norm (b - a)) =
                 (\<exists>u. x = (1 - u) *\<^sub>R a + u *\<^sub>R b \<and> 0 < u \<and> u < 1)" for x
  proof -
    have "((\<exists>u v. x = u *\<^sub>R a + v *\<^sub>R b \<and> u + v = 1) \<and>
                  dist ((1 / 2) *\<^sub>R (a + b)) x * 2 < norm (b - a)) =
          ((\<exists>u. x = (1 - u) *\<^sub>R a + u *\<^sub>R b) \<and>
                  dist ((1 / 2) *\<^sub>R (a + b)) x * 2 < norm (b - a))"
      unfolding eq_diff_eq [symmetric] by simp
    also have "... = (\<exists>u. x = (1 - u) *\<^sub>R a + u *\<^sub>R b \<and>
                          norm ((a+b) - (2 *\<^sub>R x)) < norm (b - a))"
      by (simp add: dist_half_times2) (simp add: dist_norm)
    also have "... = (\<exists>u. x = (1 - u) *\<^sub>R a + u *\<^sub>R b \<and>
            norm ((a+b) - (2 *\<^sub>R ((1 - u) *\<^sub>R a + u *\<^sub>R b))) < norm (b - a))"
      by auto
    also have "... = (\<exists>u. x = (1 - u) *\<^sub>R a + u *\<^sub>R b \<and>
                norm ((1 - u * 2) *\<^sub>R (b - a)) < norm (b - a))"
      by (simp add: algebra_simps scaleR_2)
    also have "... = (\<exists>u. x = (1 - u) *\<^sub>R a + u *\<^sub>R b \<and>
                          \<bar>1 - u * 2\<bar> * norm (b - a) < norm (b - a))"
      by simp
    also have "... = (\<exists>u. x = (1 - u) *\<^sub>R a + u *\<^sub>R b \<and> \<bar>1 - u * 2\<bar> < 1)"
      by (simp add: mult_le_cancel_right2 False)
    also have "... = (\<exists>u. x = (1 - u) *\<^sub>R a + u *\<^sub>R b \<and> 0 < u \<and> u < 1)"
      by auto
    finally show ?thesis .
  qed
  show ?thesis
    using False by (force simp: affine_hull_2 Set.set_eq_iff open_segment_image_interval *)
qed

lemmas segment_as_ball = closed_segment_as_ball open_segment_as_ball

lemma closed_segment_neq_empty [simp]: "closed_segment a b \<noteq> {}"
  by auto

lemma open_segment_eq_empty [simp]: "open_segment a b = {} \<longleftrightarrow> a = b"
proof -
  { assume a1: "open_segment a b = {}"
    have "{} \<noteq> {0::real<..<1}"
      by simp
    then have "a = b"
      using a1 open_segment_image_interval by fastforce
  } then show ?thesis by auto
qed

lemma open_segment_eq_empty' [simp]: "{} = open_segment a b \<longleftrightarrow> a = b"
  using open_segment_eq_empty by blast

lemmas segment_eq_empty = closed_segment_neq_empty open_segment_eq_empty

lemma inj_segment:
  fixes a :: "'a :: real_vector"
  assumes "a \<noteq> b"
    shows "inj_on (\<lambda>u. (1 - u) *\<^sub>R a + u *\<^sub>R b) I"
proof
  fix x y
  assume "(1 - x) *\<^sub>R a + x *\<^sub>R b = (1 - y) *\<^sub>R a + y *\<^sub>R b"
  then have "x *\<^sub>R (b - a) = y *\<^sub>R (b - a)"
    by (simp add: algebra_simps)
  with assms show "x = y"
    by (simp add: real_vector.scale_right_imp_eq)
qed

lemma finite_closed_segment [simp]: "finite(closed_segment a b) \<longleftrightarrow> a = b"
  apply auto
  apply (rule ccontr)
  apply (simp add: segment_image_interval)
  using infinite_Icc [OF zero_less_one] finite_imageD [OF _ inj_segment] apply blast
  done

lemma finite_open_segment [simp]: "finite(open_segment a b) \<longleftrightarrow> a = b"
  by (auto simp: open_segment_def)

lemmas finite_segment = finite_closed_segment finite_open_segment

lemma closed_segment_eq_sing: "closed_segment a b = {c} \<longleftrightarrow> a = c \<and> b = c"
  by auto

lemma open_segment_eq_sing: "open_segment a b \<noteq> {c}"
  by (metis finite_insert finite_open_segment insert_not_empty open_segment_image_interval)

lemmas segment_eq_sing = closed_segment_eq_sing open_segment_eq_sing

lemma subset_closed_segment:
    "closed_segment a b \<subseteq> closed_segment c d \<longleftrightarrow>
     a \<in> closed_segment c d \<and> b \<in> closed_segment c d"
  by auto (meson contra_subsetD convex_closed_segment convex_contains_segment)

lemma subset_co_segment:
    "closed_segment a b \<subseteq> open_segment c d \<longleftrightarrow>
     a \<in> open_segment c d \<and> b \<in> open_segment c d"
using closed_segment_subset by blast

lemma subset_open_segment:
  fixes a :: "'a::euclidean_space"
  shows "open_segment a b \<subseteq> open_segment c d \<longleftrightarrow>
         a = b \<or> a \<in> closed_segment c d \<and> b \<in> closed_segment c d"
        (is "?lhs = ?rhs")
proof (cases "a = b")
  case True then show ?thesis by simp
next
  case False show ?thesis
  proof
    assume rhs: ?rhs
    with \<open>a \<noteq> b\<close> have "c \<noteq> d"
      using closed_segment_idem singleton_iff by auto
    have "\<exists>uc. (1 - u) *\<^sub>R ((1 - ua) *\<^sub>R c + ua *\<^sub>R d) + u *\<^sub>R ((1 - ub) *\<^sub>R c + ub *\<^sub>R d) =
               (1 - uc) *\<^sub>R c + uc *\<^sub>R d \<and> 0 < uc \<and> uc < 1"
        if neq: "(1 - ua) *\<^sub>R c + ua *\<^sub>R d \<noteq> (1 - ub) *\<^sub>R c + ub *\<^sub>R d" "c \<noteq> d"
           and "a = (1 - ua) *\<^sub>R c + ua *\<^sub>R d" "b = (1 - ub) *\<^sub>R c + ub *\<^sub>R d"
           and u: "0 < u" "u < 1" and uab: "0 \<le> ua" "ua \<le> 1" "0 \<le> ub" "ub \<le> 1"
        for u ua ub
    proof -
      have "ua \<noteq> ub"
        using neq by auto
      moreover have "(u - 1) * ua \<le> 0" using u uab
        by (simp add: mult_nonpos_nonneg)
      ultimately have lt: "(u - 1) * ua < u * ub" using u uab
        by (metis antisym_conv diff_ge_0_iff_ge le_less_trans mult_eq_0_iff mult_le_0_iff not_less)
      have "p * ua + q * ub < p+q" if p: "0 < p" and  q: "0 < q" for p q
      proof -
        have "\<not> p \<le> 0" "\<not> q \<le> 0"
          using p q not_less by blast+
        then show ?thesis
          by (metis \<open>ua \<noteq> ub\<close> add_less_cancel_left add_less_cancel_right add_mono_thms_linordered_field(5)
                    less_eq_real_def mult_cancel_left1 mult_less_cancel_left2 uab(2) uab(4))
      qed
      then have "(1 - u) * ua + u * ub < 1" using u \<open>ua \<noteq> ub\<close>
        by (metis diff_add_cancel diff_gt_0_iff_gt)
      with lt show ?thesis
        by (rule_tac x="ua + u*(ub-ua)" in exI) (simp add: algebra_simps)
    qed
    with rhs \<open>a \<noteq> b\<close> \<open>c \<noteq> d\<close> show ?lhs
      unfolding open_segment_image_interval closed_segment_def
      by (fastforce simp add:)
  next
    assume lhs: ?lhs
    with \<open>a \<noteq> b\<close> have "c \<noteq> d"
      by (meson finite_open_segment rev_finite_subset)
    have "closure (open_segment a b) \<subseteq> closure (open_segment c d)"
      using lhs closure_mono by blast
    then have "closed_segment a b \<subseteq> closed_segment c d"
      by (simp add: \<open>a \<noteq> b\<close> \<open>c \<noteq> d\<close>)
    then show ?rhs
      by (force simp: \<open>a \<noteq> b\<close>)
  qed
qed

lemma subset_oc_segment:
  fixes a :: "'a::euclidean_space"
  shows "open_segment a b \<subseteq> closed_segment c d \<longleftrightarrow>
         a = b \<or> a \<in> closed_segment c d \<and> b \<in> closed_segment c d"
apply (simp add: subset_open_segment [symmetric])
apply (rule iffI)
 apply (metis closure_closed_segment closure_mono closure_open_segment subset_closed_segment subset_open_segment)
apply (meson dual_order.trans segment_open_subset_closed)
done

lemmas subset_segment = subset_closed_segment subset_co_segment subset_oc_segment subset_open_segment


subsection\<open>Betweenness\<close>

definition "between = (\<lambda>(a,b) x. x \<in> closed_segment a b)"

lemma betweenI:
  assumes "0 \<le> u" "u \<le> 1" "x = (1 - u) *\<^sub>R a + u *\<^sub>R b"
  shows "between (a, b) x"
using assms unfolding between_def closed_segment_def by auto

lemma betweenE:
  assumes "between (a, b) x"
  obtains u where "0 \<le> u" "u \<le> 1" "x = (1 - u) *\<^sub>R a + u *\<^sub>R b"
using assms unfolding between_def closed_segment_def by auto

lemma between_implies_scaled_diff:
  assumes "between (S, T) X" "between (S, T) Y" "S \<noteq> Y"
  obtains c where "(X - Y) = c *\<^sub>R (S - Y)"
proof -
  from \<open>between (S, T) X\<close> obtain u\<^sub>X where X: "X = u\<^sub>X *\<^sub>R S + (1 - u\<^sub>X) *\<^sub>R T"
    by (metis add.commute betweenE eq_diff_eq)
  from \<open>between (S, T) Y\<close> obtain u\<^sub>Y where Y: "Y = u\<^sub>Y *\<^sub>R S + (1 - u\<^sub>Y) *\<^sub>R T"
    by (metis add.commute betweenE eq_diff_eq)
  have "X - Y = (u\<^sub>X - u\<^sub>Y) *\<^sub>R (S - T)"
  proof -
    from X Y have "X - Y =  u\<^sub>X *\<^sub>R S - u\<^sub>Y *\<^sub>R S + ((1 - u\<^sub>X) *\<^sub>R T - (1 - u\<^sub>Y) *\<^sub>R T)" by simp
    also have "\<dots> = (u\<^sub>X - u\<^sub>Y) *\<^sub>R S - (u\<^sub>X - u\<^sub>Y) *\<^sub>R T" by (simp add: scaleR_left.diff)
    finally show ?thesis by (simp add: real_vector.scale_right_diff_distrib)
  qed
  moreover from Y have "S - Y = (1 - u\<^sub>Y) *\<^sub>R (S - T)"
    by (simp add: real_vector.scale_left_diff_distrib real_vector.scale_right_diff_distrib)
  moreover note \<open>S \<noteq> Y\<close>
  ultimately have "(X - Y) = ((u\<^sub>X - u\<^sub>Y) / (1 - u\<^sub>Y)) *\<^sub>R (S - Y)" by auto
  from this that show thesis by blast
qed

lemma between_mem_segment: "between (a,b) x \<longleftrightarrow> x \<in> closed_segment a b"
  unfolding between_def by auto

lemma between: "between (a, b) (x::'a::euclidean_space) \<longleftrightarrow> dist a b = (dist a x) + (dist x b)"
proof (cases "a = b")
  case True
  then show ?thesis
    unfolding between_def split_conv
    by (auto simp add: dist_commute)
next
  case False
  then have Fal: "norm (a - b) \<noteq> 0" and Fal2: "norm (a - b) > 0"
    by auto
  have *: "\<And>u. a - ((1 - u) *\<^sub>R a + u *\<^sub>R b) = u *\<^sub>R (a - b)"
    by (auto simp add: algebra_simps)
  show ?thesis
    unfolding between_def split_conv closed_segment_def mem_Collect_eq
    apply rule
    apply (elim exE conjE)
    apply (subst dist_triangle_eq)
  proof -
    fix u
    assume as: "x = (1 - u) *\<^sub>R a + u *\<^sub>R b" "0 \<le> u" "u \<le> 1"
    then have *: "a - x = u *\<^sub>R (a - b)" "x - b = (1 - u) *\<^sub>R (a - b)"
      unfolding as(1) by (auto simp add:algebra_simps)
    show "norm (a - x) *\<^sub>R (x - b) = norm (x - b) *\<^sub>R (a - x)"
      unfolding norm_minus_commute[of x a] * using as(2,3)
      by (auto simp add: field_simps)
  next
    assume as: "dist a b = dist a x + dist x b"
    have "norm (a - x) / norm (a - b) \<le> 1"
      using Fal2 unfolding as[unfolded dist_norm] norm_ge_zero by auto
    then show "\<exists>u. x = (1 - u) *\<^sub>R a + u *\<^sub>R b \<and> 0 \<le> u \<and> u \<le> 1"
      apply (rule_tac x="dist a x / dist a b" in exI)
      unfolding dist_norm
      apply (subst euclidean_eq_iff)
      apply rule
      defer
      apply rule
      prefer 3
      apply rule
    proof -
      fix i :: 'a
      assume i: "i \<in> Basis"
      have "((1 - norm (a - x) / norm (a - b)) *\<^sub>R a + (norm (a - x) / norm (a - b)) *\<^sub>R b) \<bullet> i =
        ((norm (a - b) - norm (a - x)) * (a \<bullet> i) + norm (a - x) * (b \<bullet> i)) / norm (a - b)"
        using Fal by (auto simp add: field_simps inner_simps)
      also have "\<dots> = x\<bullet>i"
        apply (rule divide_eq_imp[OF Fal])
        unfolding as[unfolded dist_norm]
        using as[unfolded dist_triangle_eq]
        apply -
        apply (subst (asm) euclidean_eq_iff)
        using i
        apply (erule_tac x=i in ballE)
        apply (auto simp add: field_simps inner_simps)
        done
      finally show "x \<bullet> i =
        ((1 - norm (a - x) / norm (a - b)) *\<^sub>R a + (norm (a - x) / norm (a - b)) *\<^sub>R b) \<bullet> i"
        by auto
    qed (insert Fal2, auto)
  qed
qed

lemma between_midpoint:
  fixes a :: "'a::euclidean_space"
  shows "between (a,b) (midpoint a b)" (is ?t1)
    and "between (b,a) (midpoint a b)" (is ?t2)
proof -
  have *: "\<And>x y z. x = (1/2::real) *\<^sub>R z \<Longrightarrow> y = (1/2) *\<^sub>R z \<Longrightarrow> norm z = norm x + norm y"
    by auto
  show ?t1 ?t2
    unfolding between midpoint_def dist_norm
    apply(rule_tac[!] *)
    unfolding euclidean_eq_iff[where 'a='a]
    apply (auto simp add: field_simps inner_simps)
    done
qed

lemma between_mem_convex_hull:
  "between (a,b) x \<longleftrightarrow> x \<in> convex hull {a,b}"
  unfolding between_mem_segment segment_convex_hull ..

lemma between_triv_iff [simp]: "between (a,a) b \<longleftrightarrow> a=b"
  by (auto simp: between_def)

lemma between_triv1 [simp]: "between (a,b) a"
  by (auto simp: between_def)

lemma between_triv2 [simp]: "between (a,b) b"
  by (auto simp: between_def)

lemma between_commute:
   "between (a,b) = between (b,a)"
by (auto simp: between_def closed_segment_commute)

lemma between_antisym:
  fixes a :: "'a :: euclidean_space"
  shows "\<lbrakk>between (b,c) a; between (a,c) b\<rbrakk> \<Longrightarrow> a = b"
by (auto simp: between dist_commute)

lemma between_trans:
    fixes a :: "'a :: euclidean_space"
    shows "\<lbrakk>between (b,c) a; between (a,c) d\<rbrakk> \<Longrightarrow> between (b,c) d"
  using dist_triangle2 [of b c d] dist_triangle3 [of b d a]
  by (auto simp: between dist_commute)

lemma between_norm:
    fixes a :: "'a :: euclidean_space"
    shows "between (a,b) x \<longleftrightarrow> norm(x - a) *\<^sub>R (b - x) = norm(b - x) *\<^sub>R (x - a)"
  by (auto simp: between dist_triangle_eq norm_minus_commute algebra_simps)

lemma between_swap:
  fixes A B X Y :: "'a::euclidean_space"
  assumes "between (A, B) X"
  assumes "between (A, B) Y"
  shows "between (X, B) Y \<longleftrightarrow> between (A, Y) X"
using assms by (auto simp add: between)

lemma between_translation [simp]: "between (a + y,a + z) (a + x) \<longleftrightarrow> between (y,z) x"
  by (auto simp: between_def)

lemma between_trans_2:
  fixes a :: "'a :: euclidean_space"
  shows "\<lbrakk>between (b,c) a; between (a,b) d\<rbrakk> \<Longrightarrow> between (c,d) a"
  by (metis between_commute between_swap between_trans)

lemma between_scaleR_lift [simp]:
  fixes v :: "'a::euclidean_space"
  shows "between (a *\<^sub>R v, b *\<^sub>R v) (c *\<^sub>R v) \<longleftrightarrow> v = 0 \<or> between (a, b) c"
  by (simp add: between dist_norm scaleR_left_diff_distrib [symmetric] distrib_right [symmetric])

lemma between_1:
  fixes x::real
  shows "between (a,b) x \<longleftrightarrow> (a \<le> x \<and> x \<le> b) \<or> (b \<le> x \<and> x \<le> a)"
  by (auto simp: between_mem_segment closed_segment_eq_real_ivl)


subsection \<open>Shrinking towards the interior of a convex set\<close>

lemma mem_interior_convex_shrink:
  fixes s :: "'a::euclidean_space set"
  assumes "convex s"
    and "c \<in> interior s"
    and "x \<in> s"
    and "0 < e"
    and "e \<le> 1"
  shows "x - e *\<^sub>R (x - c) \<in> interior s"
proof -
  obtain d where "d > 0" and d: "ball c d \<subseteq> s"
    using assms(2) unfolding mem_interior by auto
  show ?thesis
    unfolding mem_interior
    apply (rule_tac x="e*d" in exI)
    apply rule
    defer
    unfolding subset_eq Ball_def mem_ball
  proof (rule, rule)
    fix y
    assume as: "dist (x - e *\<^sub>R (x - c)) y < e * d"
    have *: "y = (1 - (1 - e)) *\<^sub>R ((1 / e) *\<^sub>R y - ((1 - e) / e) *\<^sub>R x) + (1 - e) *\<^sub>R x"
      using \<open>e > 0\<close> by (auto simp add: scaleR_left_diff_distrib scaleR_right_diff_distrib)
    have "dist c ((1 / e) *\<^sub>R y - ((1 - e) / e) *\<^sub>R x) = \<bar>1/e\<bar> * norm (e *\<^sub>R c - y + (1 - e) *\<^sub>R x)"
      unfolding dist_norm
      unfolding norm_scaleR[symmetric]
      apply (rule arg_cong[where f=norm])
      using \<open>e > 0\<close>
      by (auto simp add: euclidean_eq_iff[where 'a='a] field_simps inner_simps)
    also have "\<dots> = \<bar>1/e\<bar> * norm (x - e *\<^sub>R (x - c) - y)"
      by (auto intro!:arg_cong[where f=norm] simp add: algebra_simps)
    also have "\<dots> < d"
      using as[unfolded dist_norm] and \<open>e > 0\<close>
      by (auto simp add:pos_divide_less_eq[OF \<open>e > 0\<close>] mult.commute)
    finally show "y \<in> s"
      apply (subst *)
      apply (rule assms(1)[unfolded convex_alt,rule_format])
      apply (rule d[unfolded subset_eq,rule_format])
      unfolding mem_ball
      using assms(3-5)
      apply auto
      done
  qed (insert \<open>e>0\<close> \<open>d>0\<close>, auto)
qed

lemma mem_interior_closure_convex_shrink:
  fixes s :: "'a::euclidean_space set"
  assumes "convex s"
    and "c \<in> interior s"
    and "x \<in> closure s"
    and "0 < e"
    and "e \<le> 1"
  shows "x - e *\<^sub>R (x - c) \<in> interior s"
proof -
  obtain d where "d > 0" and d: "ball c d \<subseteq> s"
    using assms(2) unfolding mem_interior by auto
  have "\<exists>y\<in>s. norm (y - x) * (1 - e) < e * d"
  proof (cases "x \<in> s")
    case True
    then show ?thesis
      using \<open>e > 0\<close> \<open>d > 0\<close>
      apply (rule_tac bexI[where x=x])
      apply (auto)
      done
  next
    case False
    then have x: "x islimpt s"
      using assms(3)[unfolded closure_def] by auto
    show ?thesis
    proof (cases "e = 1")
      case True
      obtain y where "y \<in> s" "y \<noteq> x" "dist y x < 1"
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
      then obtain y where "y \<in> s" "y \<noteq> x" "dist y x < e * d / (1 - e)"
        using x[unfolded islimpt_approachable,THEN spec[where x="e*d / (1 - e)"]] by auto
      then show ?thesis
        apply (rule_tac x=y in bexI)
        unfolding dist_norm
        using pos_less_divide_eq[OF *]
        apply auto
        done
    qed
  qed
  then obtain y where "y \<in> s" and y: "norm (y - x) * (1 - e) < e * d"
    by auto
  define z where "z = c + ((1 - e) / e) *\<^sub>R (x - y)"
  have *: "x - e *\<^sub>R (x - c) = y - e *\<^sub>R (y - z)"
    unfolding z_def using \<open>e > 0\<close>
    by (auto simp add: scaleR_right_diff_distrib scaleR_right_distrib scaleR_left_diff_distrib)
  have "z \<in> interior s"
    apply (rule interior_mono[OF d,unfolded subset_eq,rule_format])
    unfolding interior_open[OF open_ball] mem_ball z_def dist_norm using y and assms(4,5)
    apply (auto simp add:field_simps norm_minus_commute)
    done
  then show ?thesis
    unfolding *
    apply -
    apply (rule mem_interior_convex_shrink)
    using assms(1,4-5) \<open>y\<in>s\<close>
    apply auto
    done
qed

lemma in_interior_closure_convex_segment:
  fixes S :: "'a::euclidean_space set"
  assumes "convex S" and a: "a \<in> interior S" and b: "b \<in> closure S"
    shows "open_segment a b \<subseteq> interior S"
proof (clarsimp simp: in_segment)
  fix u::real
  assume u: "0 < u" "u < 1"
  have "(1 - u) *\<^sub>R a + u *\<^sub>R b = b - (1 - u) *\<^sub>R (b - a)"
    by (simp add: algebra_simps)
  also have "... \<in> interior S" using mem_interior_closure_convex_shrink [OF assms] u
    by simp
  finally show "(1 - u) *\<^sub>R a + u *\<^sub>R b \<in> interior S" .
qed

lemma closure_open_Int_superset:
  assumes "open S" "S \<subseteq> closure T"
  shows "closure(S \<inter> T) = closure S"
proof -
  have "closure S \<subseteq> closure(S \<inter> T)"
    by (metis assms closed_closure closure_minimal inf.orderE open_Int_closure_subset)
  then show ?thesis
    by (simp add: closure_mono dual_order.antisym)
qed

lemma convex_closure_interior:
  fixes S :: "'a::euclidean_space set"
  assumes "convex S" and int: "interior S \<noteq> {}"
  shows "closure(interior S) = closure S"
proof -
  obtain a where a: "a \<in> interior S"
    using int by auto
  have "closure S \<subseteq> closure(interior S)"
  proof
    fix x
    assume x: "x \<in> closure S"
    show "x \<in> closure (interior S)"
    proof (cases "x=a")
      case True
      then show ?thesis
        using \<open>a \<in> interior S\<close> closure_subset by blast
    next
      case False
      show ?thesis
      proof (clarsimp simp add: closure_def islimpt_approachable)
        fix e::real
        assume xnotS: "x \<notin> interior S" and "0 < e"
        show "\<exists>x'\<in>interior S. x' \<noteq> x \<and> dist x' x < e"
        proof (intro bexI conjI)
          show "x - min (e/2 / norm (x - a)) 1 *\<^sub>R (x - a) \<noteq> x"
            using False \<open>0 < e\<close> by (auto simp: algebra_simps min_def)
          show "dist (x - min (e/2 / norm (x - a)) 1 *\<^sub>R (x - a)) x < e"
            using \<open>0 < e\<close> by (auto simp: dist_norm min_def)
          show "x - min (e/2 / norm (x - a)) 1 *\<^sub>R (x - a) \<in> interior S"
            apply (clarsimp simp add: min_def a)
            apply (rule mem_interior_closure_convex_shrink [OF \<open>convex S\<close> a x])
            using \<open>0 < e\<close> False apply (auto simp: divide_simps)
            done
        qed
      qed
    qed
  qed
  then show ?thesis
    by (simp add: closure_mono interior_subset subset_antisym)
qed

lemma closure_convex_Int_superset:
  fixes S :: "'a::euclidean_space set"
  assumes "convex S" "interior S \<noteq> {}" "interior S \<subseteq> closure T"
  shows "closure(S \<inter> T) = closure S"
proof -
  have "closure S \<subseteq> closure(interior S)"
    by (simp add: convex_closure_interior assms)
  also have "... \<subseteq> closure (S \<inter> T)"
    using interior_subset [of S] assms
    by (metis (no_types, lifting) Int_assoc Int_lower2 closure_mono closure_open_Int_superset inf.orderE open_interior)
  finally show ?thesis
    by (simp add: closure_mono dual_order.antisym)
qed


subsection \<open>Some obvious but surprisingly hard simplex lemmas\<close>

lemma simplex:
  assumes "finite s"
    and "0 \<notin> s"
  shows "convex hull (insert 0 s) =
    {y. (\<exists>u. (\<forall>x\<in>s. 0 \<le> u x) \<and> sum u s \<le> 1 \<and> sum (\<lambda>x. u x *\<^sub>R x) s = y)}"
  unfolding convex_hull_finite[OF finite.insertI[OF assms(1)]]
  apply (rule set_eqI, rule)
  unfolding mem_Collect_eq
  apply (erule_tac[!] exE)
  apply (erule_tac[!] conjE)+
  unfolding sum_clauses(2)[OF \<open>finite s\<close>]
  apply (rule_tac x=u in exI)
  defer
  apply (rule_tac x="\<lambda>x. if x = 0 then 1 - sum u s else u x" in exI)
  using assms(2)
  unfolding if_smult and sum_delta_notmem[OF assms(2)]
  apply auto
  done

lemma substd_simplex:
  assumes d: "d \<subseteq> Basis"
  shows "convex hull (insert 0 d) =
    {x. (\<forall>i\<in>Basis. 0 \<le> x\<bullet>i) \<and> (\<Sum>i\<in>d. x\<bullet>i) \<le> 1 \<and> (\<forall>i\<in>Basis. i \<notin> d \<longrightarrow> x\<bullet>i = 0)}"
  (is "convex hull (insert 0 ?p) = ?s")
proof -
  let ?D = d
  have "0 \<notin> ?p"
    using assms by (auto simp: image_def)
  from d have "finite d"
    by (blast intro: finite_subset finite_Basis)
  show ?thesis
    unfolding simplex[OF \<open>finite d\<close> \<open>0 \<notin> ?p\<close>]
    apply (rule set_eqI)
    unfolding mem_Collect_eq
    apply rule
    apply (elim exE conjE)
    apply (erule_tac[2] conjE)+
  proof -
    fix x :: "'a::euclidean_space"
    fix u
    assume as: "\<forall>x\<in>?D. 0 \<le> u x" "sum u ?D \<le> 1" "(\<Sum>x\<in>?D. u x *\<^sub>R x) = x"
    have *: "\<forall>i\<in>Basis. i:d \<longrightarrow> u i = x\<bullet>i"
      and "(\<forall>i\<in>Basis. i \<notin> d \<longrightarrow> x \<bullet> i = 0)"
      using as(3)
      unfolding substdbasis_expansion_unique[OF assms]
      by auto
    then have **: "sum u ?D = sum (op \<bullet> x) ?D"
      apply -
      apply (rule sum.cong)
      using assms
      apply auto
      done
    have "(\<forall>i\<in>Basis. 0 \<le> x\<bullet>i) \<and> sum (op \<bullet> x) ?D \<le> 1"
    proof (rule,rule)
      fix i :: 'a
      assume i: "i \<in> Basis"
      have "i \<in> d \<Longrightarrow> 0 \<le> x\<bullet>i"
        unfolding *[rule_format,OF i,symmetric]
         apply (rule_tac as(1)[rule_format])
         apply auto
         done
      moreover have "i \<notin> d \<Longrightarrow> 0 \<le> x\<bullet>i"
        using \<open>(\<forall>i\<in>Basis. i \<notin> d \<longrightarrow> x \<bullet> i = 0)\<close>[rule_format, OF i] by auto
      ultimately show "0 \<le> x\<bullet>i" by auto
    qed (insert as(2)[unfolded **], auto)
    then show "(\<forall>i\<in>Basis. 0 \<le> x\<bullet>i) \<and> sum (op \<bullet> x) ?D \<le> 1 \<and> (\<forall>i\<in>Basis. i \<notin> d \<longrightarrow> x \<bullet> i = 0)"
      using \<open>(\<forall>i\<in>Basis. i \<notin> d \<longrightarrow> x \<bullet> i = 0)\<close> by auto
  next
    fix x :: "'a::euclidean_space"
    assume as: "\<forall>i\<in>Basis. 0 \<le> x \<bullet> i" "sum (op \<bullet> x) ?D \<le> 1" "(\<forall>i\<in>Basis. i \<notin> d \<longrightarrow> x \<bullet> i = 0)"
    show "\<exists>u. (\<forall>x\<in>?D. 0 \<le> u x) \<and> sum u ?D \<le> 1 \<and> (\<Sum>x\<in>?D. u x *\<^sub>R x) = x"
      using as d
      unfolding substdbasis_expansion_unique[OF assms]
      apply (rule_tac x="inner x" in exI)
      apply auto
      done
  qed
qed

lemma std_simplex:
  "convex hull (insert 0 Basis) =
    {x::'a::euclidean_space. (\<forall>i\<in>Basis. 0 \<le> x\<bullet>i) \<and> sum (\<lambda>i. x\<bullet>i) Basis \<le> 1}"
  using substd_simplex[of Basis] by auto

lemma interior_std_simplex:
  "interior (convex hull (insert 0 Basis)) =
    {x::'a::euclidean_space. (\<forall>i\<in>Basis. 0 < x\<bullet>i) \<and> sum (\<lambda>i. x\<bullet>i) Basis < 1}"
  apply (rule set_eqI)
  unfolding mem_interior std_simplex
  unfolding subset_eq mem_Collect_eq Ball_def mem_ball
  unfolding Ball_def[symmetric]
  apply rule
  apply (elim exE conjE)
  defer
  apply (erule conjE)
proof -
  fix x :: 'a
  fix e
  assume "e > 0" and as: "\<forall>xa. dist x xa < e \<longrightarrow> (\<forall>x\<in>Basis. 0 \<le> xa \<bullet> x) \<and> sum (op \<bullet> xa) Basis \<le> 1"
  show "(\<forall>xa\<in>Basis. 0 < x \<bullet> xa) \<and> sum (op \<bullet> x) Basis < 1"
    apply safe
  proof -
    fix i :: 'a
    assume i: "i \<in> Basis"
    then show "0 < x \<bullet> i"
      using as[THEN spec[where x="x - (e / 2) *\<^sub>R i"]] and \<open>e > 0\<close>
      unfolding dist_norm
      by (auto elim!: ballE[where x=i] simp: inner_simps)
  next
    have **: "dist x (x + (e / 2) *\<^sub>R (SOME i. i\<in>Basis)) < e" using \<open>e > 0\<close>
      unfolding dist_norm
      by (auto intro!: mult_strict_left_mono simp: SOME_Basis)
    have "\<And>i. i \<in> Basis \<Longrightarrow> (x + (e / 2) *\<^sub>R (SOME i. i\<in>Basis)) \<bullet> i =
      x\<bullet>i + (if i = (SOME i. i\<in>Basis) then e/2 else 0)"
      by (auto simp: SOME_Basis inner_Basis inner_simps)
    then have *: "sum (op \<bullet> (x + (e / 2) *\<^sub>R (SOME i. i\<in>Basis))) Basis =
      sum (\<lambda>i. x\<bullet>i + (if (SOME i. i\<in>Basis) = i then e/2 else 0)) Basis"
      apply (rule_tac sum.cong)
      apply auto
      done
    have "sum (op \<bullet> x) Basis < sum (op \<bullet> (x + (e / 2) *\<^sub>R (SOME i. i\<in>Basis))) Basis"
      unfolding * sum.distrib
      using \<open>e > 0\<close> DIM_positive[where 'a='a]
      apply (subst sum.delta')
      apply (auto simp: SOME_Basis)
      done
    also have "\<dots> \<le> 1"
      using **
      apply (drule_tac as[rule_format])
      apply auto
      done
    finally show "sum (op \<bullet> x) Basis < 1" by auto
  qed
next
  fix x :: 'a
  assume as: "\<forall>i\<in>Basis. 0 < x \<bullet> i" "sum (op \<bullet> x) Basis < 1"
  obtain a :: 'b where "a \<in> UNIV" using UNIV_witness ..
  let ?d = "(1 - sum (op \<bullet> x) Basis) / real (DIM('a))"
  show "\<exists>e>0. \<forall>y. dist x y < e \<longrightarrow> (\<forall>i\<in>Basis. 0 \<le> y \<bullet> i) \<and> sum (op \<bullet> y) Basis \<le> 1"
  proof (rule_tac x="min (Min ((op \<bullet> x) ` Basis)) D" for D in exI, intro conjI impI allI)
    fix y
    assume y: "dist x y < min (Min (op \<bullet> x ` Basis)) ?d"
    have "sum (op \<bullet> y) Basis \<le> sum (\<lambda>i. x\<bullet>i + ?d) Basis"
    proof (rule sum_mono)
      fix i :: 'a
      assume i: "i \<in> Basis"
      then have "\<bar>y\<bullet>i - x\<bullet>i\<bar> < ?d"
        apply -
        apply (rule le_less_trans)
        using Basis_le_norm[OF i, of "y - x"]
        using y[unfolded min_less_iff_conj dist_norm, THEN conjunct2]
        apply (auto simp add: norm_minus_commute inner_diff_left)
        done
      then show "y \<bullet> i \<le> x \<bullet> i + ?d" by auto
    qed
    also have "\<dots> \<le> 1"
      unfolding sum.distrib sum_constant
      by (auto simp add: Suc_le_eq)
    finally show "sum (op \<bullet> y) Basis \<le> 1" .
    show "(\<forall>i\<in>Basis. 0 \<le> y \<bullet> i)"
    proof safe
      fix i :: 'a
      assume i: "i \<in> Basis"
      have "norm (x - y) < x\<bullet>i"
        apply (rule less_le_trans)
        apply (rule y[unfolded min_less_iff_conj dist_norm, THEN conjunct1])
        using i
        apply auto
        done
      then show "0 \<le> y\<bullet>i"
        using Basis_le_norm[OF i, of "x - y"] and as(1)[rule_format, OF i]
        by (auto simp: inner_simps)
    qed
  next
    have "Min ((op \<bullet> x) ` Basis) > 0"
      using as by simp
    moreover have "?d > 0"
      using as by (auto simp: Suc_le_eq)
    ultimately show "0 < min (Min (op \<bullet> x ` Basis)) ((1 - sum (op \<bullet> x) Basis) / real DIM('a))"
      by linarith
  qed 
qed

lemma interior_std_simplex_nonempty:
  obtains a :: "'a::euclidean_space" where
    "a \<in> interior(convex hull (insert 0 Basis))"
proof -
  let ?D = "Basis :: 'a set"
  let ?a = "sum (\<lambda>b::'a. inverse (2 * real DIM('a)) *\<^sub>R b) Basis"
  {
    fix i :: 'a
    assume i: "i \<in> Basis"
    have "?a \<bullet> i = inverse (2 * real DIM('a))"
      by (rule trans[of _ "sum (\<lambda>j. if i = j then inverse (2 * real DIM('a)) else 0) ?D"])
         (simp_all add: sum.If_cases i) }
  note ** = this
  show ?thesis
    apply (rule that[of ?a])
    unfolding interior_std_simplex mem_Collect_eq
  proof safe
    fix i :: 'a
    assume i: "i \<in> Basis"
    show "0 < ?a \<bullet> i"
      unfolding **[OF i] by (auto simp add: Suc_le_eq DIM_positive)
  next
    have "sum (op \<bullet> ?a) ?D = sum (\<lambda>i. inverse (2 * real DIM('a))) ?D"
      apply (rule sum.cong)
      apply rule
      apply auto
      done
    also have "\<dots> < 1"
      unfolding sum_constant divide_inverse[symmetric]
      by (auto simp add: field_simps)
    finally show "sum (op \<bullet> ?a) ?D < 1" by auto
  qed
qed

lemma rel_interior_substd_simplex:
  assumes d: "d \<subseteq> Basis"
  shows "rel_interior (convex hull (insert 0 d)) =
    {x::'a::euclidean_space. (\<forall>i\<in>d. 0 < x\<bullet>i) \<and> (\<Sum>i\<in>d. x\<bullet>i) < 1 \<and> (\<forall>i\<in>Basis. i \<notin> d \<longrightarrow> x\<bullet>i = 0)}"
  (is "rel_interior (convex hull (insert 0 ?p)) = ?s")
proof -
  have "finite d"
    apply (rule finite_subset)
    using assms
    apply auto
    done
  show ?thesis
  proof (cases "d = {}")
    case True
    then show ?thesis
      using rel_interior_sing using euclidean_eq_iff[of _ 0] by auto
  next
    case False
    have h0: "affine hull (convex hull (insert 0 ?p)) =
      {x::'a::euclidean_space. (\<forall>i\<in>Basis. i \<notin> d \<longrightarrow> x\<bullet>i = 0)}"
      using affine_hull_convex_hull affine_hull_substd_basis assms by auto
    have aux: "\<And>x::'a. \<forall>i\<in>Basis. (\<forall>i\<in>d. 0 \<le> x\<bullet>i) \<and> (\<forall>i\<in>Basis. i \<notin> d \<longrightarrow> x\<bullet>i = 0) \<longrightarrow> 0 \<le> x\<bullet>i"
      by auto
    {
      fix x :: "'a::euclidean_space"
      assume x: "x \<in> rel_interior (convex hull (insert 0 ?p))"
      then obtain e where e0: "e > 0" and
        "ball x e \<inter> {xa. (\<forall>i\<in>Basis. i \<notin> d \<longrightarrow> xa\<bullet>i = 0)} \<subseteq> convex hull (insert 0 ?p)"
        using mem_rel_interior_ball[of x "convex hull (insert 0 ?p)"] h0 by auto
      then have as: "\<forall>xa. dist x xa < e \<and> (\<forall>i\<in>Basis. i \<notin> d \<longrightarrow> xa\<bullet>i = 0) \<longrightarrow>
        (\<forall>i\<in>d. 0 \<le> xa \<bullet> i) \<and> sum (op \<bullet> xa) d \<le> 1"
        unfolding ball_def unfolding substd_simplex[OF assms] using assms by auto
      have x0: "(\<forall>i\<in>Basis. i \<notin> d \<longrightarrow> x\<bullet>i = 0)"
        using x rel_interior_subset  substd_simplex[OF assms] by auto
      have "(\<forall>i\<in>d. 0 < x \<bullet> i) \<and> sum (op \<bullet> x) d < 1 \<and> (\<forall>i\<in>Basis. i \<notin> d \<longrightarrow> x\<bullet>i = 0)"
        apply rule
        apply rule
      proof -
        fix i :: 'a
        assume "i \<in> d"
        then have "\<forall>ia\<in>d. 0 \<le> (x - (e / 2) *\<^sub>R i) \<bullet> ia"
          apply -
          apply (rule as[rule_format,THEN conjunct1])
          unfolding dist_norm
          using d \<open>e > 0\<close> x0
          apply (auto simp: inner_simps inner_Basis)
          done
        then show "0 < x \<bullet> i"
          apply (erule_tac x=i in ballE)
          using \<open>e > 0\<close> \<open>i \<in> d\<close> d
          apply (auto simp: inner_simps inner_Basis)
          done
      next
        obtain a where a: "a \<in> d"
          using \<open>d \<noteq> {}\<close> by auto
        then have **: "dist x (x + (e / 2) *\<^sub>R a) < e"
          using \<open>e > 0\<close> norm_Basis[of a] d
          unfolding dist_norm
          by auto
        have "\<And>i. i \<in> Basis \<Longrightarrow> (x + (e / 2) *\<^sub>R a) \<bullet> i = x\<bullet>i + (if i = a then e/2 else 0)"
          using a d by (auto simp: inner_simps inner_Basis)
        then have *: "sum (op \<bullet> (x + (e / 2) *\<^sub>R a)) d =
          sum (\<lambda>i. x\<bullet>i + (if a = i then e/2 else 0)) d"
          using d by (intro sum.cong) auto
        have "a \<in> Basis"
          using \<open>a \<in> d\<close> d by auto
        then have h1: "(\<forall>i\<in>Basis. i \<notin> d \<longrightarrow> (x + (e / 2) *\<^sub>R a) \<bullet> i = 0)"
          using x0 d \<open>a\<in>d\<close> by (auto simp add: inner_add_left inner_Basis)
        have "sum (op \<bullet> x) d < sum (op \<bullet> (x + (e / 2) *\<^sub>R a)) d"
          unfolding * sum.distrib
          using \<open>e > 0\<close> \<open>a \<in> d\<close>
          using \<open>finite d\<close>
          by (auto simp add: sum.delta')
        also have "\<dots> \<le> 1"
          using ** h1 as[rule_format, of "x + (e / 2) *\<^sub>R a"]
          by auto
        finally show "sum (op \<bullet> x) d < 1 \<and> (\<forall>i\<in>Basis. i \<notin> d \<longrightarrow> x\<bullet>i = 0)"
          using x0 by auto
      qed
    }
    moreover
    {
      fix x :: "'a::euclidean_space"
      assume as: "x \<in> ?s"
      have "\<forall>i. 0 < x\<bullet>i \<or> 0 = x\<bullet>i \<longrightarrow> 0 \<le> x\<bullet>i"
        by auto
      moreover have "\<forall>i. i \<in> d \<or> i \<notin> d" by auto
      ultimately
      have "\<forall>i. (\<forall>i\<in>d. 0 < x\<bullet>i) \<and> (\<forall>i. i \<notin> d \<longrightarrow> x\<bullet>i = 0) \<longrightarrow> 0 \<le> x\<bullet>i"
        by metis
      then have h2: "x \<in> convex hull (insert 0 ?p)"
        using as assms
        unfolding substd_simplex[OF assms] by fastforce
      obtain a where a: "a \<in> d"
        using \<open>d \<noteq> {}\<close> by auto
      let ?d = "(1 - sum (op \<bullet> x) d) / real (card d)"
      have "0 < card d" using \<open>d \<noteq> {}\<close> \<open>finite d\<close>
        by (simp add: card_gt_0_iff)
      have "Min ((op \<bullet> x) ` d) > 0"
        using as \<open>d \<noteq> {}\<close> \<open>finite d\<close> by (simp add: Min_gr_iff)
      moreover have "?d > 0" using as using \<open>0 < card d\<close> by auto
      ultimately have h3: "min (Min ((op \<bullet> x) ` d)) ?d > 0"
        by auto

      have "x \<in> rel_interior (convex hull (insert 0 ?p))"
        unfolding rel_interior_ball mem_Collect_eq h0
        apply (rule,rule h2)
        unfolding substd_simplex[OF assms]
        apply (rule_tac x="min (Min ((op \<bullet> x) ` d)) ?d" in exI)
        apply (rule, rule h3)
        apply safe
        unfolding mem_ball
      proof -
        fix y :: 'a
        assume y: "dist x y < min (Min (op \<bullet> x ` d)) ?d"
        assume y2: "\<forall>i\<in>Basis. i \<notin> d \<longrightarrow> y\<bullet>i = 0"
        have "sum (op \<bullet> y) d \<le> sum (\<lambda>i. x\<bullet>i + ?d) d"
        proof (rule sum_mono)
          fix i
          assume "i \<in> d"
          with d have i: "i \<in> Basis"
            by auto
          have "\<bar>y\<bullet>i - x\<bullet>i\<bar> < ?d"
            apply (rule le_less_trans)
            using Basis_le_norm[OF i, of "y - x"]
            using y[unfolded min_less_iff_conj dist_norm, THEN conjunct2]
            apply (auto simp add: norm_minus_commute inner_simps)
            done
          then show "y \<bullet> i \<le> x \<bullet> i + ?d" by auto
        qed
        also have "\<dots> \<le> 1"
          unfolding sum.distrib sum_constant  using \<open>0 < card d\<close>
          by auto
        finally show "sum (op \<bullet> y) d \<le> 1" .

        fix i :: 'a
        assume i: "i \<in> Basis"
        then show "0 \<le> y\<bullet>i"
        proof (cases "i\<in>d")
          case True
          have "norm (x - y) < x\<bullet>i"
            using y[unfolded min_less_iff_conj dist_norm, THEN conjunct1]
            using Min_gr_iff[of "op \<bullet> x ` d" "norm (x - y)"] \<open>0 < card d\<close> \<open>i:d\<close>
            by (simp add: card_gt_0_iff)
          then show "0 \<le> y\<bullet>i"
            using Basis_le_norm[OF i, of "x - y"] and as(1)[rule_format]
            by (auto simp: inner_simps)
        qed (insert y2, auto)
      qed
    }
    ultimately have
      "\<And>x. x \<in> rel_interior (convex hull insert 0 d) \<longleftrightarrow>
        x \<in> {x. (\<forall>i\<in>d. 0 < x \<bullet> i) \<and> sum (op \<bullet> x) d < 1 \<and> (\<forall>i\<in>Basis. i \<notin> d \<longrightarrow> x \<bullet> i = 0)}"
      by blast
    then show ?thesis by (rule set_eqI)
  qed
qed

lemma rel_interior_substd_simplex_nonempty:
  assumes "d \<noteq> {}"
    and "d \<subseteq> Basis"
  obtains a :: "'a::euclidean_space"
    where "a \<in> rel_interior (convex hull (insert 0 d))"
proof -
  let ?D = d
  let ?a = "sum (\<lambda>b::'a::euclidean_space. inverse (2 * real (card d)) *\<^sub>R b) ?D"
  have "finite d"
    apply (rule finite_subset)
    using assms(2)
    apply auto
    done
  then have d1: "0 < real (card d)"
    using \<open>d \<noteq> {}\<close> by auto
  {
    fix i
    assume "i \<in> d"
    have "?a \<bullet> i = inverse (2 * real (card d))"
      apply (rule trans[of _ "sum (\<lambda>j. if i = j then inverse (2 * real (card d)) else 0) ?D"])
      unfolding inner_sum_left
      apply (rule sum.cong)
      using \<open>i \<in> d\<close> \<open>finite d\<close> sum.delta'[of d i "(\<lambda>k. inverse (2 * real (card d)))"]
        d1 assms(2)
      by (auto simp: inner_Basis set_rev_mp[OF _ assms(2)])
  }
  note ** = this
  show ?thesis
    apply (rule that[of ?a])
    unfolding rel_interior_substd_simplex[OF assms(2)] mem_Collect_eq
  proof safe
    fix i
    assume "i \<in> d"
    have "0 < inverse (2 * real (card d))"
      using d1 by auto
    also have "\<dots> = ?a \<bullet> i" using **[of i] \<open>i \<in> d\<close>
      by auto
    finally show "0 < ?a \<bullet> i" by auto
  next
    have "sum (op \<bullet> ?a) ?D = sum (\<lambda>i. inverse (2 * real (card d))) ?D"
      by (rule sum.cong) (rule refl, rule **)
    also have "\<dots> < 1"
      unfolding sum_constant divide_real_def[symmetric]
      by (auto simp add: field_simps)
    finally show "sum (op \<bullet> ?a) ?D < 1" by auto
  next
    fix i
    assume "i \<in> Basis" and "i \<notin> d"
    have "?a \<in> span d"
    proof (rule span_sum[of d "(\<lambda>b. b /\<^sub>R (2 * real (card d)))" d])
      {
        fix x :: "'a::euclidean_space"
        assume "x \<in> d"
        then have "x \<in> span d"
          using span_superset[of _ "d"] by auto
        then have "x /\<^sub>R (2 * real (card d)) \<in> span d"
          using span_mul[of x "d" "(inverse (real (card d)) / 2)"] by auto
      }
      then show "\<And>x. x\<in>d \<Longrightarrow> x /\<^sub>R (2 * real (card d)) \<in> span d"
        by auto
    qed
    then show "?a \<bullet> i = 0 "
      using \<open>i \<notin> d\<close> unfolding span_substd_basis[OF assms(2)] using \<open>i \<in> Basis\<close> by auto
  qed
qed


subsection \<open>Relative interior of convex set\<close>

lemma rel_interior_convex_nonempty_aux:
  fixes S :: "'n::euclidean_space set"
  assumes "convex S"
    and "0 \<in> S"
  shows "rel_interior S \<noteq> {}"
proof (cases "S = {0}")
  case True
  then show ?thesis using rel_interior_sing by auto
next
  case False
  obtain B where B: "independent B \<and> B \<le> S \<and> S \<le> span B \<and> card B = dim S"
    using basis_exists[of S] by auto
  then have "B \<noteq> {}"
    using B assms \<open>S \<noteq> {0}\<close> span_empty by auto
  have "insert 0 B \<le> span B"
    using subspace_span[of B] subspace_0[of "span B"] span_inc by auto
  then have "span (insert 0 B) \<le> span B"
    using span_span[of B] span_mono[of "insert 0 B" "span B"] by blast
  then have "convex hull insert 0 B \<le> span B"
    using convex_hull_subset_span[of "insert 0 B"] by auto
  then have "span (convex hull insert 0 B) \<le> span B"
    using span_span[of B] span_mono[of "convex hull insert 0 B" "span B"] by blast
  then have *: "span (convex hull insert 0 B) = span B"
    using span_mono[of B "convex hull insert 0 B"] hull_subset[of "insert 0 B"] by auto
  then have "span (convex hull insert 0 B) = span S"
    using B span_mono[of B S] span_mono[of S "span B"] span_span[of B] by auto
  moreover have "0 \<in> affine hull (convex hull insert 0 B)"
    using hull_subset[of "convex hull insert 0 B"] hull_subset[of "insert 0 B"] by auto
  ultimately have **: "affine hull (convex hull insert 0 B) = affine hull S"
    using affine_hull_span_0[of "convex hull insert 0 B"] affine_hull_span_0[of "S"]
      assms hull_subset[of S]
    by auto
  obtain d and f :: "'n \<Rightarrow> 'n" where
    fd: "card d = card B" "linear f" "f ` B = d"
      "f ` span B = {x. \<forall>i\<in>Basis. i \<notin> d \<longrightarrow> x \<bullet> i = (0::real)} \<and> inj_on f (span B)"
    and d: "d \<subseteq> Basis"
    using basis_to_substdbasis_subspace_isomorphism[of B,OF _ ] B by auto
  then have "bounded_linear f"
    using linear_conv_bounded_linear by auto
  have "d \<noteq> {}"
    using fd B \<open>B \<noteq> {}\<close> by auto
  have "insert 0 d = f ` (insert 0 B)"
    using fd linear_0 by auto
  then have "(convex hull (insert 0 d)) = f ` (convex hull (insert 0 B))"
    using convex_hull_linear_image[of f "(insert 0 d)"]
      convex_hull_linear_image[of f "(insert 0 B)"] \<open>linear f\<close>
    by auto
  moreover have "rel_interior (f ` (convex hull insert 0 B)) =
    f ` rel_interior (convex hull insert 0 B)"
    apply (rule  rel_interior_injective_on_span_linear_image[of f "(convex hull insert 0 B)"])
    using \<open>bounded_linear f\<close> fd *
    apply auto
    done
  ultimately have "rel_interior (convex hull insert 0 B) \<noteq> {}"
    using rel_interior_substd_simplex_nonempty[OF \<open>d \<noteq> {}\<close> d]
    apply auto
    apply blast
    done
  moreover have "convex hull (insert 0 B) \<subseteq> S"
    using B assms hull_mono[of "insert 0 B" "S" "convex"] convex_hull_eq
    by auto
  ultimately show ?thesis
    using subset_rel_interior[of "convex hull insert 0 B" S] ** by auto
qed

lemma rel_interior_eq_empty:
  fixes S :: "'n::euclidean_space set"
  assumes "convex S"
  shows "rel_interior S = {} \<longleftrightarrow> S = {}"
proof -
  {
    assume "S \<noteq> {}"
    then obtain a where "a \<in> S" by auto
    then have "0 \<in> op + (-a) ` S"
      using assms exI[of "(\<lambda>x. x \<in> S \<and> - a + x = 0)" a] by auto
    then have "rel_interior (op + (-a) ` S) \<noteq> {}"
      using rel_interior_convex_nonempty_aux[of "op + (-a) ` S"]
        convex_translation[of S "-a"] assms
      by auto
    then have "rel_interior S \<noteq> {}"
      using rel_interior_translation by auto
  }
  then show ?thesis
    using rel_interior_empty by auto
qed

lemma interior_simplex_nonempty:
  fixes S :: "'N :: euclidean_space set"
  assumes "independent S" "finite S" "card S = DIM('N)"
  obtains a where "a \<in> interior (convex hull (insert 0 S))"
proof -
  have "affine hull (insert 0 S) = UNIV"
    apply (simp add: hull_inc affine_hull_span_0)
    using assms dim_eq_full indep_card_eq_dim_span by fastforce
  moreover have "rel_interior (convex hull insert 0 S) \<noteq> {}"
    using rel_interior_eq_empty [of "convex hull (insert 0 S)"] by auto
  ultimately have "interior (convex hull insert 0 S) \<noteq> {}"
    by (simp add: rel_interior_interior)
  with that show ?thesis
    by auto
qed

lemma convex_rel_interior:
  fixes S :: "'n::euclidean_space set"
  assumes "convex S"
  shows "convex (rel_interior S)"
proof -
  {
    fix x y and u :: real
    assume assm: "x \<in> rel_interior S" "y \<in> rel_interior S" "0 \<le> u" "u \<le> 1"
    then have "x \<in> S"
      using rel_interior_subset by auto
    have "x - u *\<^sub>R (x-y) \<in> rel_interior S"
    proof (cases "0 = u")
      case False
      then have "0 < u" using assm by auto
      then show ?thesis
        using assm rel_interior_convex_shrink[of S y x u] assms \<open>x \<in> S\<close> by auto
    next
      case True
      then show ?thesis using assm by auto
    qed
    then have "(1 - u) *\<^sub>R x + u *\<^sub>R y \<in> rel_interior S"
      by (simp add: algebra_simps)
  }
  then show ?thesis
    unfolding convex_alt by auto
qed

lemma convex_closure_rel_interior:
  fixes S :: "'n::euclidean_space set"
  assumes "convex S"
  shows "closure (rel_interior S) = closure S"
proof -
  have h1: "closure (rel_interior S) \<le> closure S"
    using closure_mono[of "rel_interior S" S] rel_interior_subset[of S] by auto
  show ?thesis
  proof (cases "S = {}")
    case False
    then obtain a where a: "a \<in> rel_interior S"
      using rel_interior_eq_empty assms by auto
    { fix x
      assume x: "x \<in> closure S"
      {
        assume "x = a"
        then have "x \<in> closure (rel_interior S)"
          using a unfolding closure_def by auto
      }
      moreover
      {
        assume "x \<noteq> a"
         {
           fix e :: real
           assume "e > 0"
           define e1 where "e1 = min 1 (e/norm (x - a))"
           then have e1: "e1 > 0" "e1 \<le> 1" "e1 * norm (x - a) \<le> e"
             using \<open>x \<noteq> a\<close> \<open>e > 0\<close> le_divide_eq[of e1 e "norm (x - a)"]
             by simp_all
           then have *: "x - e1 *\<^sub>R (x - a) : rel_interior S"
             using rel_interior_closure_convex_shrink[of S a x e1] assms x a e1_def
             by auto
           have "\<exists>y. y \<in> rel_interior S \<and> y \<noteq> x \<and> dist y x \<le> e"
              apply (rule_tac x="x - e1 *\<^sub>R (x - a)" in exI)
              using * e1 dist_norm[of "x - e1 *\<^sub>R (x - a)" x] \<open>x \<noteq> a\<close>
              apply simp
              done
        }
        then have "x islimpt rel_interior S"
          unfolding islimpt_approachable_le by auto
        then have "x \<in> closure(rel_interior S)"
          unfolding closure_def by auto
      }
      ultimately have "x \<in> closure(rel_interior S)" by auto
    }
    then show ?thesis using h1 by auto
  next
    case True
    then have "rel_interior S = {}"
      using rel_interior_empty by auto
    then have "closure (rel_interior S) = {}"
      using closure_empty by auto
    with True show ?thesis by auto
  qed
qed

lemma rel_interior_same_affine_hull:
  fixes S :: "'n::euclidean_space set"
  assumes "convex S"
  shows "affine hull (rel_interior S) = affine hull S"
  by (metis assms closure_same_affine_hull convex_closure_rel_interior)

lemma rel_interior_aff_dim:
  fixes S :: "'n::euclidean_space set"
  assumes "convex S"
  shows "aff_dim (rel_interior S) = aff_dim S"
  by (metis aff_dim_affine_hull2 assms rel_interior_same_affine_hull)

lemma rel_interior_rel_interior:
  fixes S :: "'n::euclidean_space set"
  assumes "convex S"
  shows "rel_interior (rel_interior S) = rel_interior S"
proof -
  have "openin (subtopology euclidean (affine hull (rel_interior S))) (rel_interior S)"
    using openin_rel_interior[of S] rel_interior_same_affine_hull[of S] assms by auto
  then show ?thesis
    using rel_interior_def by auto
qed

lemma rel_interior_rel_open:
  fixes S :: "'n::euclidean_space set"
  assumes "convex S"
  shows "rel_open (rel_interior S)"
  unfolding rel_open_def using rel_interior_rel_interior assms by auto

lemma convex_rel_interior_closure_aux:
  fixes x y z :: "'n::euclidean_space"
  assumes "0 < a" "0 < b" "(a + b) *\<^sub>R z = a *\<^sub>R x + b *\<^sub>R y"
  obtains e where "0 < e" "e \<le> 1" "z = y - e *\<^sub>R (y - x)"
proof -
  define e where "e = a / (a + b)"
  have "z = (1 / (a + b)) *\<^sub>R ((a + b) *\<^sub>R z)"
    apply auto
    using assms
    apply simp
    done
  also have "\<dots> = (1 / (a + b)) *\<^sub>R (a *\<^sub>R x + b *\<^sub>R y)"
    using assms scaleR_cancel_left[of "1/(a+b)" "(a + b) *\<^sub>R z" "a *\<^sub>R x + b *\<^sub>R y"]
    by auto
  also have "\<dots> = y - e *\<^sub>R (y-x)"
    using e_def
    apply (simp add: algebra_simps)
    using scaleR_left_distrib[of "a/(a+b)" "b/(a+b)" y] assms add_divide_distrib[of a b "a+b"]
    apply auto
    done
  finally have "z = y - e *\<^sub>R (y-x)"
    by auto
  moreover have "e > 0" using e_def assms by auto
  moreover have "e \<le> 1" using e_def assms by auto
  ultimately show ?thesis using that[of e] by auto
qed

lemma convex_rel_interior_closure:
  fixes S :: "'n::euclidean_space set"
  assumes "convex S"
  shows "rel_interior (closure S) = rel_interior S"
proof (cases "S = {}")
  case True
  then show ?thesis
    using assms rel_interior_eq_empty by auto
next
  case False
  have "rel_interior (closure S) \<supseteq> rel_interior S"
    using subset_rel_interior[of S "closure S"] closure_same_affine_hull closure_subset
    by auto
  moreover
  {
    fix z
    assume z: "z \<in> rel_interior (closure S)"
    obtain x where x: "x \<in> rel_interior S"
      using \<open>S \<noteq> {}\<close> assms rel_interior_eq_empty by auto
    have "z \<in> rel_interior S"
    proof (cases "x = z")
      case True
      then show ?thesis using x by auto
    next
      case False
      obtain e where e: "e > 0" "cball z e \<inter> affine hull closure S \<le> closure S"
        using z rel_interior_cball[of "closure S"] by auto
      hence *: "0 < e/norm(z-x)" using e False by auto
      define y where "y = z + (e/norm(z-x)) *\<^sub>R (z-x)"
      have yball: "y \<in> cball z e"
        using mem_cball y_def dist_norm[of z y] e by auto
      have "x \<in> affine hull closure S"
        using x rel_interior_subset_closure hull_inc[of x "closure S"] by blast
      moreover have "z \<in> affine hull closure S"
        using z rel_interior_subset hull_subset[of "closure S"] by blast
      ultimately have "y \<in> affine hull closure S"
        using y_def affine_affine_hull[of "closure S"]
          mem_affine_3_minus [of "affine hull closure S" z z x "e/norm(z-x)"] by auto
      then have "y \<in> closure S" using e yball by auto
      have "(1 + (e/norm(z-x))) *\<^sub>R z = (e/norm(z-x)) *\<^sub>R x + y"
        using y_def by (simp add: algebra_simps)
      then obtain e1 where "0 < e1" "e1 \<le> 1" "z = y - e1 *\<^sub>R (y - x)"
        using * convex_rel_interior_closure_aux[of "e / norm (z - x)" 1 z x y]
        by (auto simp add: algebra_simps)
      then show ?thesis
        using rel_interior_closure_convex_shrink assms x \<open>y \<in> closure S\<close>
        by auto
    qed
  }
  ultimately show ?thesis by auto
qed

lemma convex_interior_closure:
  fixes S :: "'n::euclidean_space set"
  assumes "convex S"
  shows "interior (closure S) = interior S"
  using closure_aff_dim[of S] interior_rel_interior_gen[of S]
    interior_rel_interior_gen[of "closure S"]
    convex_rel_interior_closure[of S] assms
  by auto

lemma closure_eq_rel_interior_eq:
  fixes S1 S2 :: "'n::euclidean_space set"
  assumes "convex S1"
    and "convex S2"
  shows "closure S1 = closure S2 \<longleftrightarrow> rel_interior S1 = rel_interior S2"
  by (metis convex_rel_interior_closure convex_closure_rel_interior assms)

lemma closure_eq_between:
  fixes S1 S2 :: "'n::euclidean_space set"
  assumes "convex S1"
    and "convex S2"
  shows "closure S1 = closure S2 \<longleftrightarrow> rel_interior S1 \<le> S2 \<and> S2 \<subseteq> closure S1"
  (is "?A \<longleftrightarrow> ?B")
proof
  assume ?A
  then show ?B
    by (metis assms closure_subset convex_rel_interior_closure rel_interior_subset)
next
  assume ?B
  then have "closure S1 \<subseteq> closure S2"
    by (metis assms(1) convex_closure_rel_interior closure_mono)
  moreover from \<open>?B\<close> have "closure S1 \<supseteq> closure S2"
    by (metis closed_closure closure_minimal)
  ultimately show ?A ..
qed

lemma open_inter_closure_rel_interior:
  fixes S A :: "'n::euclidean_space set"
  assumes "convex S"
    and "open A"
  shows "A \<inter> closure S = {} \<longleftrightarrow> A \<inter> rel_interior S = {}"
  by (metis assms convex_closure_rel_interior open_Int_closure_eq_empty)

lemma rel_interior_open_segment:
  fixes a :: "'a :: euclidean_space"
  shows "rel_interior(open_segment a b) = open_segment a b"
proof (cases "a = b")
  case True then show ?thesis by auto
next
  case False then show ?thesis
    apply (simp add: rel_interior_eq openin_open)
    apply (rule_tac x="ball (inverse 2 *\<^sub>R (a + b)) (norm(b - a) / 2)" in exI)
    apply (simp add: open_segment_as_ball)
    done
qed

lemma rel_interior_closed_segment:
  fixes a :: "'a :: euclidean_space"
  shows "rel_interior(closed_segment a b) =
         (if a = b then {a} else open_segment a b)"
proof (cases "a = b")
  case True then show ?thesis by auto
next
  case False then show ?thesis
    by simp
       (metis closure_open_segment convex_open_segment convex_rel_interior_closure
              rel_interior_open_segment)
qed

lemmas rel_interior_segment = rel_interior_closed_segment rel_interior_open_segment

lemma starlike_convex_tweak_boundary_points:
  fixes S :: "'a::euclidean_space set"
  assumes "convex S" "S \<noteq> {}" and ST: "rel_interior S \<subseteq> T" and TS: "T \<subseteq> closure S"
  shows "starlike T"
proof -
  have "rel_interior S \<noteq> {}"
    by (simp add: assms rel_interior_eq_empty)
  then obtain a where a: "a \<in> rel_interior S"  by blast
  with ST have "a \<in> T"  by blast
  have *: "\<And>x. x \<in> T \<Longrightarrow> open_segment a x \<subseteq> rel_interior S"
    apply (rule rel_interior_closure_convex_segment [OF \<open>convex S\<close> a])
    using assms by blast
  show ?thesis
    unfolding starlike_def
    apply (rule bexI [OF _ \<open>a \<in> T\<close>])
    apply (simp add: closed_segment_eq_open)
    apply (intro conjI ballI a \<open>a \<in> T\<close> rel_interior_closure_convex_segment [OF \<open>convex S\<close> a])
    apply (simp add: order_trans [OF * ST])
    done
qed

subsection\<open>The relative frontier of a set\<close>

definition "rel_frontier S = closure S - rel_interior S"

lemma rel_frontier_empty [simp]: "rel_frontier {} = {}"
  by (simp add: rel_frontier_def)

lemma rel_frontier_eq_empty:
    fixes S :: "'n::euclidean_space set"
    shows "rel_frontier S = {} \<longleftrightarrow> affine S"
  apply (simp add: rel_frontier_def)
  apply (simp add: rel_interior_eq_closure [symmetric])
  using rel_interior_subset_closure by blast

lemma rel_frontier_sing [simp]:
    fixes a :: "'n::euclidean_space"
    shows "rel_frontier {a} = {}"
  by (simp add: rel_frontier_def)

lemma rel_frontier_affine_hull:
  fixes S :: "'a::euclidean_space set"
  shows "rel_frontier S \<subseteq> affine hull S"
using closure_affine_hull rel_frontier_def by fastforce

lemma rel_frontier_cball [simp]:
    fixes a :: "'n::euclidean_space"
    shows "rel_frontier(cball a r) = (if r = 0 then {} else sphere a r)"
proof (cases rule: linorder_cases [of r 0])
  case less then show ?thesis
    by (force simp: sphere_def)
next
  case equal then show ?thesis by simp
next
  case greater then show ?thesis
    apply simp
    by (metis centre_in_ball empty_iff frontier_cball frontier_def interior_cball interior_rel_interior_gen rel_frontier_def)
qed

lemma rel_frontier_translation:
  fixes a :: "'a::euclidean_space"
  shows "rel_frontier((\<lambda>x. a + x) ` S) = (\<lambda>x. a + x) ` (rel_frontier S)"
by (simp add: rel_frontier_def translation_diff rel_interior_translation closure_translation)

lemma closed_affine_hull [iff]:
  fixes S :: "'n::euclidean_space set"
  shows "closed (affine hull S)"
  by (metis affine_affine_hull affine_closed)

lemma rel_frontier_nonempty_interior:
  fixes S :: "'n::euclidean_space set"
  shows "interior S \<noteq> {} \<Longrightarrow> rel_frontier S = frontier S"
by (metis frontier_def interior_rel_interior_gen rel_frontier_def)

lemma rel_frontier_frontier:
  fixes S :: "'n::euclidean_space set"
  shows "affine hull S = UNIV \<Longrightarrow> rel_frontier S = frontier S"
by (simp add: frontier_def rel_frontier_def rel_interior_interior)

lemma closest_point_in_rel_frontier:
   "\<lbrakk>closed S; S \<noteq> {}; x \<in> affine hull S - rel_interior S\<rbrakk>
   \<Longrightarrow> closest_point S x \<in> rel_frontier S"
  by (simp add: closest_point_in_rel_interior closest_point_in_set rel_frontier_def)

lemma closed_rel_frontier [iff]:
  fixes S :: "'n::euclidean_space set"
  shows "closed (rel_frontier S)"
proof -
  have *: "closedin (subtopology euclidean (affine hull S)) (closure S - rel_interior S)"
    by (simp add: closed_subset closedin_diff closure_affine_hull openin_rel_interior)
  show ?thesis
    apply (rule closedin_closed_trans[of "affine hull S" "rel_frontier S"])
    unfolding rel_frontier_def
    using * closed_affine_hull
    apply auto
    done
qed

lemma closed_rel_boundary:
  fixes S :: "'n::euclidean_space set"
  shows "closed S \<Longrightarrow> closed(S - rel_interior S)"
by (metis closed_rel_frontier closure_closed rel_frontier_def)

lemma compact_rel_boundary:
  fixes S :: "'n::euclidean_space set"
  shows "compact S \<Longrightarrow> compact(S - rel_interior S)"
by (metis bounded_diff closed_rel_boundary closure_eq compact_closure compact_imp_closed)

lemma bounded_rel_frontier:
  fixes S :: "'n::euclidean_space set"
  shows "bounded S \<Longrightarrow> bounded(rel_frontier S)"
by (simp add: bounded_closure bounded_diff rel_frontier_def)

lemma compact_rel_frontier_bounded:
  fixes S :: "'n::euclidean_space set"
  shows "bounded S \<Longrightarrow> compact(rel_frontier S)"
using bounded_rel_frontier closed_rel_frontier compact_eq_bounded_closed by blast

lemma compact_rel_frontier:
  fixes S :: "'n::euclidean_space set"
  shows "compact S \<Longrightarrow> compact(rel_frontier S)"
by (meson compact_eq_bounded_closed compact_rel_frontier_bounded)

lemma convex_same_rel_interior_closure:
  fixes S :: "'n::euclidean_space set"
  shows "\<lbrakk>convex S; convex T\<rbrakk>
         \<Longrightarrow> rel_interior S = rel_interior T \<longleftrightarrow> closure S = closure T"
by (simp add: closure_eq_rel_interior_eq)

lemma convex_same_rel_interior_closure_straddle:
  fixes S :: "'n::euclidean_space set"
  shows "\<lbrakk>convex S; convex T\<rbrakk>
         \<Longrightarrow> rel_interior S = rel_interior T \<longleftrightarrow>
             rel_interior S \<subseteq> T \<and> T \<subseteq> closure S"
by (simp add: closure_eq_between convex_same_rel_interior_closure)

lemma convex_rel_frontier_aff_dim:
  fixes S1 S2 :: "'n::euclidean_space set"
  assumes "convex S1"
    and "convex S2"
    and "S2 \<noteq> {}"
    and "S1 \<le> rel_frontier S2"
  shows "aff_dim S1 < aff_dim S2"
proof -
  have "S1 \<subseteq> closure S2"
    using assms unfolding rel_frontier_def by auto
  then have *: "affine hull S1 \<subseteq> affine hull S2"
    using hull_mono[of "S1" "closure S2"] closure_same_affine_hull[of S2] by blast
  then have "aff_dim S1 \<le> aff_dim S2"
    using * aff_dim_affine_hull[of S1] aff_dim_affine_hull[of S2]
      aff_dim_subset[of "affine hull S1" "affine hull S2"]
    by auto
  moreover
  {
    assume eq: "aff_dim S1 = aff_dim S2"
    then have "S1 \<noteq> {}"
      using aff_dim_empty[of S1] aff_dim_empty[of S2] \<open>S2 \<noteq> {}\<close> by auto
    have **: "affine hull S1 = affine hull S2"
       apply (rule affine_dim_equal)
       using * affine_affine_hull
       apply auto
       using \<open>S1 \<noteq> {}\<close> hull_subset[of S1]
       apply auto
       using eq aff_dim_affine_hull[of S1] aff_dim_affine_hull[of S2]
       apply auto
       done
    obtain a where a: "a \<in> rel_interior S1"
      using \<open>S1 \<noteq> {}\<close> rel_interior_eq_empty assms by auto
    obtain T where T: "open T" "a \<in> T \<inter> S1" "T \<inter> affine hull S1 \<subseteq> S1"
       using mem_rel_interior[of a S1] a by auto
    then have "a \<in> T \<inter> closure S2"
      using a assms unfolding rel_frontier_def by auto
    then obtain b where b: "b \<in> T \<inter> rel_interior S2"
      using open_inter_closure_rel_interior[of S2 T] assms T by auto
    then have "b \<in> affine hull S1"
      using rel_interior_subset hull_subset[of S2] ** by auto
    then have "b \<in> S1"
      using T b by auto
    then have False
      using b assms unfolding rel_frontier_def by auto
  }
  ultimately show ?thesis
    using less_le by auto
qed

lemma convex_rel_interior_if:
  fixes S ::  "'n::euclidean_space set"
  assumes "convex S"
    and "z \<in> rel_interior S"
  shows "\<forall>x\<in>affine hull S. \<exists>m. m > 1 \<and> (\<forall>e. e > 1 \<and> e \<le> m \<longrightarrow> (1 - e) *\<^sub>R x + e *\<^sub>R z \<in> S)"
proof -
  obtain e1 where e1: "e1 > 0 \<and> cball z e1 \<inter> affine hull S \<subseteq> S"
    using mem_rel_interior_cball[of z S] assms by auto
  {
    fix x
    assume x: "x \<in> affine hull S"
    {
      assume "x \<noteq> z"
      define m where "m = 1 + e1/norm(x-z)"
      hence "m > 1" using e1 \<open>x \<noteq> z\<close> by auto
      {
        fix e
        assume e: "e > 1 \<and> e \<le> m"
        have "z \<in> affine hull S"
          using assms rel_interior_subset hull_subset[of S] by auto
        then have *: "(1 - e)*\<^sub>R x + e *\<^sub>R z \<in> affine hull S"
          using mem_affine[of "affine hull S" x z "(1-e)" e] affine_affine_hull[of S] x
          by auto
        have "norm (z + e *\<^sub>R x - (x + e *\<^sub>R z)) = norm ((e - 1) *\<^sub>R (x - z))"
          by (simp add: algebra_simps)
        also have "\<dots> = (e - 1) * norm (x-z)"
          using norm_scaleR e by auto
        also have "\<dots> \<le> (m - 1) * norm (x - z)"
          using e mult_right_mono[of _ _ "norm(x-z)"] by auto
        also have "\<dots> = (e1 / norm (x - z)) * norm (x - z)"
          using m_def by auto
        also have "\<dots> = e1"
          using \<open>x \<noteq> z\<close> e1 by simp
        finally have **: "norm (z + e *\<^sub>R x - (x + e *\<^sub>R z)) \<le> e1"
          by auto
        have "(1 - e)*\<^sub>R x+ e *\<^sub>R z \<in> cball z e1"
          using m_def **
          unfolding cball_def dist_norm
          by (auto simp add: algebra_simps)
        then have "(1 - e) *\<^sub>R x+ e *\<^sub>R z \<in> S"
          using e * e1 by auto
      }
      then have "\<exists>m. m > 1 \<and> (\<forall>e. e > 1 \<and> e \<le> m \<longrightarrow> (1 - e) *\<^sub>R x + e *\<^sub>R z \<in> S )"
        using \<open>m> 1 \<close> by auto
    }
    moreover
    {
      assume "x = z"
      define m where "m = 1 + e1"
      then have "m > 1"
        using e1 by auto
      {
        fix e
        assume e: "e > 1 \<and> e \<le> m"
        then have "(1 - e) *\<^sub>R x + e *\<^sub>R z \<in> S"
          using e1 x \<open>x = z\<close> by (auto simp add: algebra_simps)
        then have "(1 - e) *\<^sub>R x + e *\<^sub>R z \<in> S"
          using e by auto
      }
      then have "\<exists>m. m > 1 \<and> (\<forall>e. e > 1 \<and> e \<le> m \<longrightarrow> (1 - e) *\<^sub>R x + e *\<^sub>R z \<in> S)"
        using \<open>m > 1\<close> by auto
    }
    ultimately have "\<exists>m. m > 1 \<and> (\<forall>e. e > 1 \<and> e \<le> m \<longrightarrow> (1 - e) *\<^sub>R x + e *\<^sub>R z \<in> S )"
      by blast
  }
  then show ?thesis by auto
qed

lemma convex_rel_interior_if2:
  fixes S :: "'n::euclidean_space set"
  assumes "convex S"
  assumes "z \<in> rel_interior S"
  shows "\<forall>x\<in>affine hull S. \<exists>e. e > 1 \<and> (1 - e)*\<^sub>R x + e *\<^sub>R z \<in> S"
  using convex_rel_interior_if[of S z] assms by auto

lemma convex_rel_interior_only_if:
  fixes S :: "'n::euclidean_space set"
  assumes "convex S"
    and "S \<noteq> {}"
  assumes "\<forall>x\<in>S. \<exists>e. e > 1 \<and> (1 - e) *\<^sub>R x + e *\<^sub>R z \<in> S"
  shows "z \<in> rel_interior S"
proof -
  obtain x where x: "x \<in> rel_interior S"
    using rel_interior_eq_empty assms by auto
  then have "x \<in> S"
    using rel_interior_subset by auto
  then obtain e where e: "e > 1 \<and> (1 - e) *\<^sub>R x + e *\<^sub>R z \<in> S"
    using assms by auto
  define y where [abs_def]: "y = (1 - e) *\<^sub>R x + e *\<^sub>R z"
  then have "y \<in> S" using e by auto
  define e1 where "e1 = 1/e"
  then have "0 < e1 \<and> e1 < 1" using e by auto
  then have "z  =y - (1 - e1) *\<^sub>R (y - x)"
    using e1_def y_def by (auto simp add: algebra_simps)
  then show ?thesis
    using rel_interior_convex_shrink[of S x y "1-e1"] \<open>0 < e1 \<and> e1 < 1\<close> \<open>y \<in> S\<close> x assms
    by auto
qed

lemma convex_rel_interior_iff:
  fixes S :: "'n::euclidean_space set"
  assumes "convex S"
    and "S \<noteq> {}"
  shows "z \<in> rel_interior S \<longleftrightarrow> (\<forall>x\<in>S. \<exists>e. e > 1 \<and> (1 - e) *\<^sub>R x + e *\<^sub>R z \<in> S)"
  using assms hull_subset[of S "affine"]
    convex_rel_interior_if[of S z] convex_rel_interior_only_if[of S z]
  by auto

lemma convex_rel_interior_iff2:
  fixes S :: "'n::euclidean_space set"
  assumes "convex S"
    and "S \<noteq> {}"
  shows "z \<in> rel_interior S \<longleftrightarrow> (\<forall>x\<in>affine hull S. \<exists>e. e > 1 \<and> (1 - e) *\<^sub>R x + e *\<^sub>R z \<in> S)"
  using assms hull_subset[of S] convex_rel_interior_if2[of S z] convex_rel_interior_only_if[of S z]
  by auto

lemma convex_interior_iff:
  fixes S :: "'n::euclidean_space set"
  assumes "convex S"
  shows "z \<in> interior S \<longleftrightarrow> (\<forall>x. \<exists>e. e > 0 \<and> z + e *\<^sub>R x \<in> S)"
proof (cases "aff_dim S = int DIM('n)")
  case False
  {
    assume "z \<in> interior S"
    then have False
      using False interior_rel_interior_gen[of S] by auto
  }
  moreover
  {
    assume r: "\<forall>x. \<exists>e. e > 0 \<and> z + e *\<^sub>R x \<in> S"
    {
      fix x
      obtain e1 where e1: "e1 > 0 \<and> z + e1 *\<^sub>R (x - z) \<in> S"
        using r by auto
      obtain e2 where e2: "e2 > 0 \<and> z + e2 *\<^sub>R (z - x) \<in> S"
        using r by auto
      define x1 where [abs_def]: "x1 = z + e1 *\<^sub>R (x - z)"
      then have x1: "x1 \<in> affine hull S"
        using e1 hull_subset[of S] by auto
      define x2 where [abs_def]: "x2 = z + e2 *\<^sub>R (z - x)"
      then have x2: "x2 \<in> affine hull S"
        using e2 hull_subset[of S] by auto
      have *: "e1/(e1+e2) + e2/(e1+e2) = 1"
        using add_divide_distrib[of e1 e2 "e1+e2"] e1 e2 by simp
      then have "z = (e2/(e1+e2)) *\<^sub>R x1 + (e1/(e1+e2)) *\<^sub>R x2"
        using x1_def x2_def
        apply (auto simp add: algebra_simps)
        using scaleR_left_distrib[of "e1/(e1+e2)" "e2/(e1+e2)" z]
        apply auto
        done
      then have z: "z \<in> affine hull S"
        using mem_affine[of "affine hull S" x1 x2 "e2/(e1+e2)" "e1/(e1+e2)"]
          x1 x2 affine_affine_hull[of S] *
        by auto
      have "x1 - x2 = (e1 + e2) *\<^sub>R (x - z)"
        using x1_def x2_def by (auto simp add: algebra_simps)
      then have "x = z+(1/(e1+e2)) *\<^sub>R (x1-x2)"
        using e1 e2 by simp
      then have "x \<in> affine hull S"
        using mem_affine_3_minus[of "affine hull S" z x1 x2 "1/(e1+e2)"]
          x1 x2 z affine_affine_hull[of S]
        by auto
    }
    then have "affine hull S = UNIV"
      by auto
    then have "aff_dim S = int DIM('n)"
      using aff_dim_affine_hull[of S] by (simp add: aff_dim_UNIV)
    then have False
      using False by auto
  }
  ultimately show ?thesis by auto
next
  case True
  then have "S \<noteq> {}"
    using aff_dim_empty[of S] by auto
  have *: "affine hull S = UNIV"
    using True affine_hull_UNIV by auto
  {
    assume "z \<in> interior S"
    then have "z \<in> rel_interior S"
      using True interior_rel_interior_gen[of S] by auto
    then have **: "\<forall>x. \<exists>e. e > 1 \<and> (1 - e) *\<^sub>R x + e *\<^sub>R z \<in> S"
      using convex_rel_interior_iff2[of S z] assms \<open>S \<noteq> {}\<close> * by auto
    fix x
    obtain e1 where e1: "e1 > 1" "(1 - e1) *\<^sub>R (z - x) + e1 *\<^sub>R z \<in> S"
      using **[rule_format, of "z-x"] by auto
    define e where [abs_def]: "e = e1 - 1"
    then have "(1 - e1) *\<^sub>R (z - x) + e1 *\<^sub>R z = z + e *\<^sub>R x"
      by (simp add: algebra_simps)
    then have "e > 0" "z + e *\<^sub>R x \<in> S"
      using e1 e_def by auto
    then have "\<exists>e. e > 0 \<and> z + e *\<^sub>R x \<in> S"
      by auto
  }
  moreover
  {
    assume r: "\<forall>x. \<exists>e. e > 0 \<and> z + e *\<^sub>R x \<in> S"
    {
      fix x
      obtain e1 where e1: "e1 > 0" "z + e1 *\<^sub>R (z - x) \<in> S"
        using r[rule_format, of "z-x"] by auto
      define e where "e = e1 + 1"
      then have "z + e1 *\<^sub>R (z - x) = (1 - e) *\<^sub>R x + e *\<^sub>R z"
        by (simp add: algebra_simps)
      then have "e > 1" "(1 - e)*\<^sub>R x + e *\<^sub>R z \<in> S"
        using e1 e_def by auto
      then have "\<exists>e. e > 1 \<and> (1 - e) *\<^sub>R x + e *\<^sub>R z \<in> S" by auto
    }
    then have "z \<in> rel_interior S"
      using convex_rel_interior_iff2[of S z] assms \<open>S \<noteq> {}\<close> by auto
    then have "z \<in> interior S"
      using True interior_rel_interior_gen[of S] by auto
  }
  ultimately show ?thesis by auto
qed


subsubsection \<open>Relative interior and closure under common operations\<close>

lemma rel_interior_inter_aux: "\<Inter>{rel_interior S |S. S : I} \<subseteq> \<Inter>I"
proof -
  {
    fix y
    assume "y \<in> \<Inter>{rel_interior S |S. S : I}"
    then have y: "\<forall>S \<in> I. y \<in> rel_interior S"
      by auto
    {
      fix S
      assume "S \<in> I"
      then have "y \<in> S"
        using rel_interior_subset y by auto
    }
    then have "y \<in> \<Inter>I" by auto
  }
  then show ?thesis by auto
qed

lemma closure_Int: "closure (\<Inter>I) \<le> \<Inter>{closure S |S. S \<in> I}"
proof -
  {
    fix y
    assume "y \<in> \<Inter>I"
    then have y: "\<forall>S \<in> I. y \<in> S" by auto
    {
      fix S
      assume "S \<in> I"
      then have "y \<in> closure S"
        using closure_subset y by auto
    }
    then have "y \<in> \<Inter>{closure S |S. S \<in> I}"
      by auto
  }
  then have "\<Inter>I \<subseteq> \<Inter>{closure S |S. S \<in> I}"
    by auto
  moreover have "closed (\<Inter>{closure S |S. S \<in> I})"
    unfolding closed_Inter closed_closure by auto
  ultimately show ?thesis using closure_hull[of "\<Inter>I"]
    hull_minimal[of "\<Inter>I" "\<Inter>{closure S |S. S \<in> I}" "closed"] by auto
qed

lemma convex_closure_rel_interior_inter:
  assumes "\<forall>S\<in>I. convex (S :: 'n::euclidean_space set)"
    and "\<Inter>{rel_interior S |S. S \<in> I} \<noteq> {}"
  shows "\<Inter>{closure S |S. S \<in> I} \<le> closure (\<Inter>{rel_interior S |S. S \<in> I})"
proof -
  obtain x where x: "\<forall>S\<in>I. x \<in> rel_interior S"
    using assms by auto
  {
    fix y
    assume "y \<in> \<Inter>{closure S |S. S \<in> I}"
    then have y: "\<forall>S \<in> I. y \<in> closure S"
      by auto
    {
      assume "y = x"
      then have "y \<in> closure (\<Inter>{rel_interior S |S. S \<in> I})"
        using x closure_subset[of "\<Inter>{rel_interior S |S. S \<in> I}"] by auto
    }
    moreover
    {
      assume "y \<noteq> x"
      { fix e :: real
        assume e: "e > 0"
        define e1 where "e1 = min 1 (e/norm (y - x))"
        then have e1: "e1 > 0" "e1 \<le> 1" "e1 * norm (y - x) \<le> e"
          using \<open>y \<noteq> x\<close> \<open>e > 0\<close> le_divide_eq[of e1 e "norm (y - x)"]
          by simp_all
        define z where "z = y - e1 *\<^sub>R (y - x)"
        {
          fix S
          assume "S \<in> I"
          then have "z \<in> rel_interior S"
            using rel_interior_closure_convex_shrink[of S x y e1] assms x y e1 z_def
            by auto
        }
        then have *: "z \<in> \<Inter>{rel_interior S |S. S \<in> I}"
          by auto
        have "\<exists>z. z \<in> \<Inter>{rel_interior S |S. S \<in> I} \<and> z \<noteq> y \<and> dist z y \<le> e"
          apply (rule_tac x="z" in exI)
          using \<open>y \<noteq> x\<close> z_def * e1 e dist_norm[of z y]
          apply simp
          done
      }
      then have "y islimpt \<Inter>{rel_interior S |S. S \<in> I}"
        unfolding islimpt_approachable_le by blast
      then have "y \<in> closure (\<Inter>{rel_interior S |S. S \<in> I})"
        unfolding closure_def by auto
    }
    ultimately have "y \<in> closure (\<Inter>{rel_interior S |S. S \<in> I})"
      by auto
  }
  then show ?thesis by auto
qed

lemma convex_closure_inter:
  assumes "\<forall>S\<in>I. convex (S :: 'n::euclidean_space set)"
    and "\<Inter>{rel_interior S |S. S \<in> I} \<noteq> {}"
  shows "closure (\<Inter>I) = \<Inter>{closure S |S. S \<in> I}"
proof -
  have "\<Inter>{closure S |S. S \<in> I} \<le> closure (\<Inter>{rel_interior S |S. S \<in> I})"
    using convex_closure_rel_interior_inter assms by auto
  moreover
  have "closure (\<Inter>{rel_interior S |S. S \<in> I}) \<le> closure (\<Inter>I)"
    using rel_interior_inter_aux closure_mono[of "\<Inter>{rel_interior S |S. S \<in> I}" "\<Inter>I"]
    by auto
  ultimately show ?thesis
    using closure_Int[of I] by auto
qed

lemma convex_inter_rel_interior_same_closure:
  assumes "\<forall>S\<in>I. convex (S :: 'n::euclidean_space set)"
    and "\<Inter>{rel_interior S |S. S \<in> I} \<noteq> {}"
  shows "closure (\<Inter>{rel_interior S |S. S \<in> I}) = closure (\<Inter>I)"
proof -
  have "\<Inter>{closure S |S. S \<in> I} \<le> closure (\<Inter>{rel_interior S |S. S \<in> I})"
    using convex_closure_rel_interior_inter assms by auto
  moreover
  have "closure (\<Inter>{rel_interior S |S. S \<in> I}) \<le> closure (\<Inter>I)"
    using rel_interior_inter_aux closure_mono[of "\<Inter>{rel_interior S |S. S \<in> I}" "\<Inter>I"]
    by auto
  ultimately show ?thesis
    using closure_Int[of I] by auto
qed

lemma convex_rel_interior_inter:
  assumes "\<forall>S\<in>I. convex (S :: 'n::euclidean_space set)"
    and "\<Inter>{rel_interior S |S. S \<in> I} \<noteq> {}"
  shows "rel_interior (\<Inter>I) \<subseteq> \<Inter>{rel_interior S |S. S \<in> I}"
proof -
  have "convex (\<Inter>I)"
    using assms convex_Inter by auto
  moreover
  have "convex (\<Inter>{rel_interior S |S. S \<in> I})"
    apply (rule convex_Inter)
    using assms convex_rel_interior
    apply auto
    done
  ultimately
  have "rel_interior (\<Inter>{rel_interior S |S. S \<in> I}) = rel_interior (\<Inter>I)"
    using convex_inter_rel_interior_same_closure assms
      closure_eq_rel_interior_eq[of "\<Inter>{rel_interior S |S. S \<in> I}" "\<Inter>I"]
    by blast
  then show ?thesis
    using rel_interior_subset[of "\<Inter>{rel_interior S |S. S \<in> I}"] by auto
qed

lemma convex_rel_interior_finite_inter:
  assumes "\<forall>S\<in>I. convex (S :: 'n::euclidean_space set)"
    and "\<Inter>{rel_interior S |S. S \<in> I} \<noteq> {}"
    and "finite I"
  shows "rel_interior (\<Inter>I) = \<Inter>{rel_interior S |S. S \<in> I}"
proof -
  have "\<Inter>I \<noteq> {}"
    using assms rel_interior_inter_aux[of I] by auto
  have "convex (\<Inter>I)"
    using convex_Inter assms by auto
  show ?thesis
  proof (cases "I = {}")
    case True
    then show ?thesis
      using Inter_empty rel_interior_UNIV by auto
  next
    case False
    {
      fix z
      assume z: "z \<in> \<Inter>{rel_interior S |S. S \<in> I}"
      {
        fix x
        assume x: "x \<in> \<Inter>I"
        {
          fix S
          assume S: "S \<in> I"
          then have "z \<in> rel_interior S" "x \<in> S"
            using z x by auto
          then have "\<exists>m. m > 1 \<and> (\<forall>e. e > 1 \<and> e \<le> m \<longrightarrow> (1 - e)*\<^sub>R x + e *\<^sub>R z \<in> S)"
            using convex_rel_interior_if[of S z] S assms hull_subset[of S] by auto
        }
        then obtain mS where
          mS: "\<forall>S\<in>I. mS S > 1 \<and> (\<forall>e. e > 1 \<and> e \<le> mS S \<longrightarrow> (1 - e) *\<^sub>R x + e *\<^sub>R z \<in> S)" by metis
        define e where "e = Min (mS ` I)"
        then have "e \<in> mS ` I" using assms \<open>I \<noteq> {}\<close> by simp
        then have "e > 1" using mS by auto
        moreover have "\<forall>S\<in>I. e \<le> mS S"
          using e_def assms by auto
        ultimately have "\<exists>e > 1. (1 - e) *\<^sub>R x + e *\<^sub>R z \<in> \<Inter>I"
          using mS by auto
      }
      then have "z \<in> rel_interior (\<Inter>I)"
        using convex_rel_interior_iff[of "\<Inter>I" z] \<open>\<Inter>I \<noteq> {}\<close> \<open>convex (\<Inter>I)\<close> by auto
    }
    then show ?thesis
      using convex_rel_interior_inter[of I] assms by auto
  qed
qed

lemma convex_closure_inter_two:
  fixes S T :: "'n::euclidean_space set"
  assumes "convex S"
    and "convex T"
  assumes "rel_interior S \<inter> rel_interior T \<noteq> {}"
  shows "closure (S \<inter> T) = closure S \<inter> closure T"
  using convex_closure_inter[of "{S,T}"] assms by auto

lemma convex_rel_interior_inter_two:
  fixes S T :: "'n::euclidean_space set"
  assumes "convex S"
    and "convex T"
    and "rel_interior S \<inter> rel_interior T \<noteq> {}"
  shows "rel_interior (S \<inter> T) = rel_interior S \<inter> rel_interior T"
  using convex_rel_interior_finite_inter[of "{S,T}"] assms by auto

lemma convex_affine_closure_Int:
  fixes S T :: "'n::euclidean_space set"
  assumes "convex S"
    and "affine T"
    and "rel_interior S \<inter> T \<noteq> {}"
  shows "closure (S \<inter> T) = closure S \<inter> T"
proof -
  have "affine hull T = T"
    using assms by auto
  then have "rel_interior T = T"
    using rel_interior_affine_hull[of T] by metis
  moreover have "closure T = T"
    using assms affine_closed[of T] by auto
  ultimately show ?thesis
    using convex_closure_inter_two[of S T] assms affine_imp_convex by auto
qed

lemma connected_component_1_gen:
  fixes S :: "'a :: euclidean_space set"
  assumes "DIM('a) = 1"
  shows "connected_component S a b \<longleftrightarrow> closed_segment a b \<subseteq> S"
unfolding connected_component_def
by (metis (no_types, lifting) assms subsetD subsetI convex_contains_segment convex_segment(1)
            ends_in_segment connected_convex_1_gen)

lemma connected_component_1:
  fixes S :: "real set"
  shows "connected_component S a b \<longleftrightarrow> closed_segment a b \<subseteq> S"
by (simp add: connected_component_1_gen)

lemma convex_affine_rel_interior_Int:
  fixes S T :: "'n::euclidean_space set"
  assumes "convex S"
    and "affine T"
    and "rel_interior S \<inter> T \<noteq> {}"
  shows "rel_interior (S \<inter> T) = rel_interior S \<inter> T"
proof -
  have "affine hull T = T"
    using assms by auto
  then have "rel_interior T = T"
    using rel_interior_affine_hull[of T] by metis
  moreover have "closure T = T"
    using assms affine_closed[of T] by auto
  ultimately show ?thesis
    using convex_rel_interior_inter_two[of S T] assms affine_imp_convex by auto
qed

lemma convex_affine_rel_frontier_Int:
   fixes S T :: "'n::euclidean_space set"
  assumes "convex S"
    and "affine T"
    and "interior S \<inter> T \<noteq> {}"
  shows "rel_frontier(S \<inter> T) = frontier S \<inter> T"
using assms
apply (simp add: rel_frontier_def convex_affine_closure_Int frontier_def)
by (metis Diff_Int_distrib2 Int_emptyI convex_affine_closure_Int convex_affine_rel_interior_Int empty_iff interior_rel_interior_gen)

lemma rel_interior_convex_Int_affine:
  fixes S :: "'a::euclidean_space set"
  assumes "convex S" "affine T" "interior S \<inter> T \<noteq> {}"
    shows "rel_interior(S \<inter> T) = interior S \<inter> T"
proof -
  obtain a where aS: "a \<in> interior S" and aT:"a \<in> T"
    using assms by force
  have "rel_interior S = interior S"
    by (metis (no_types) aS affine_hull_nonempty_interior equals0D rel_interior_interior)
  then show ?thesis
    by (metis (no_types) affine_imp_convex assms convex_rel_interior_inter_two hull_same rel_interior_affine_hull)
qed

lemma closure_convex_Int_affine:
  fixes S :: "'a::euclidean_space set"
  assumes "convex S" "affine T" "rel_interior S \<inter> T \<noteq> {}"
  shows "closure(S \<inter> T) = closure S \<inter> T"
proof
  have "closure (S \<inter> T) \<subseteq> closure T"
    by (simp add: closure_mono)
  also have "... \<subseteq> T"
    by (simp add: affine_closed assms)
  finally show "closure(S \<inter> T) \<subseteq> closure S \<inter> T"
    by (simp add: closure_mono)
next
  obtain a where "a \<in> rel_interior S" "a \<in> T"
    using assms by auto
  then have ssT: "subspace ((\<lambda>x. (-a)+x) ` T)" and "a \<in> S"
    using affine_diffs_subspace rel_interior_subset assms by blast+
  show "closure S \<inter> T \<subseteq> closure (S \<inter> T)"
  proof
    fix x  assume "x \<in> closure S \<inter> T"
    show "x \<in> closure (S \<inter> T)"
    proof (cases "x = a")
      case True
      then show ?thesis
        using \<open>a \<in> S\<close> \<open>a \<in> T\<close> closure_subset by fastforce
    next
      case False
      then have "x \<in> closure(open_segment a x)"
        by auto
      then show ?thesis
        using \<open>x \<in> closure S \<inter> T\<close> assms convex_affine_closure_Int by blast
    qed
  qed
qed

lemma subset_rel_interior_convex:
  fixes S T :: "'n::euclidean_space set"
  assumes "convex S"
    and "convex T"
    and "S \<le> closure T"
    and "\<not> S \<subseteq> rel_frontier T"
  shows "rel_interior S \<subseteq> rel_interior T"
proof -
  have *: "S \<inter> closure T = S"
    using assms by auto
  have "\<not> rel_interior S \<subseteq> rel_frontier T"
    using closure_mono[of "rel_interior S" "rel_frontier T"] closed_rel_frontier[of T]
      closure_closed[of S] convex_closure_rel_interior[of S] closure_subset[of S] assms
    by auto
  then have "rel_interior S \<inter> rel_interior (closure T) \<noteq> {}"
    using assms rel_frontier_def[of T] rel_interior_subset convex_rel_interior_closure[of T]
    by auto
  then have "rel_interior S \<inter> rel_interior T = rel_interior (S \<inter> closure T)"
    using assms convex_closure convex_rel_interior_inter_two[of S "closure T"]
      convex_rel_interior_closure[of T]
    by auto
  also have "\<dots> = rel_interior S"
    using * by auto
  finally show ?thesis
    by auto
qed

lemma rel_interior_convex_linear_image:
  fixes f :: "'m::euclidean_space \<Rightarrow> 'n::euclidean_space"
  assumes "linear f"
    and "convex S"
  shows "f ` (rel_interior S) = rel_interior (f ` S)"
proof (cases "S = {}")
  case True
  then show ?thesis
    using assms rel_interior_empty rel_interior_eq_empty by auto
next
  case False
  have *: "f ` (rel_interior S) \<subseteq> f ` S"
    unfolding image_mono using rel_interior_subset by auto
  have "f ` S \<subseteq> f ` (closure S)"
    unfolding image_mono using closure_subset by auto
  also have "\<dots> = f ` (closure (rel_interior S))"
    using convex_closure_rel_interior assms by auto
  also have "\<dots> \<subseteq> closure (f ` (rel_interior S))"
    using closure_linear_image_subset assms by auto
  finally have "closure (f ` S) = closure (f ` rel_interior S)"
    using closure_mono[of "f ` S" "closure (f ` rel_interior S)"] closure_closure
      closure_mono[of "f ` rel_interior S" "f ` S"] *
    by auto
  then have "rel_interior (f ` S) = rel_interior (f ` rel_interior S)"
    using assms convex_rel_interior
      linear_conv_bounded_linear[of f] convex_linear_image[of _ S]
      convex_linear_image[of _ "rel_interior S"]
      closure_eq_rel_interior_eq[of "f ` S" "f ` rel_interior S"]
    by auto
  then have "rel_interior (f ` S) \<subseteq> f ` rel_interior S"
    using rel_interior_subset by auto
  moreover
  {
    fix z
    assume "z \<in> f ` rel_interior S"
    then obtain z1 where z1: "z1 \<in> rel_interior S" "f z1 = z" by auto
    {
      fix x
      assume "x \<in> f ` S"
      then obtain x1 where x1: "x1 \<in> S" "f x1 = x" by auto
      then obtain e where e: "e > 1" "(1 - e) *\<^sub>R x1 + e *\<^sub>R z1 : S"
        using convex_rel_interior_iff[of S z1] \<open>convex S\<close> x1 z1 by auto
      moreover have "f ((1 - e) *\<^sub>R x1 + e *\<^sub>R z1) = (1 - e) *\<^sub>R x + e *\<^sub>R z"
        using x1 z1 \<open>linear f\<close> by (simp add: linear_add_cmul)
      ultimately have "(1 - e) *\<^sub>R x + e *\<^sub>R z : f ` S"
        using imageI[of "(1 - e) *\<^sub>R x1 + e *\<^sub>R z1" S f] by auto
      then have "\<exists>e. e > 1 \<and> (1 - e) *\<^sub>R x + e *\<^sub>R z : f ` S"
        using e by auto
    }
    then have "z \<in> rel_interior (f ` S)"
      using convex_rel_interior_iff[of "f ` S" z] \<open>convex S\<close>
        \<open>linear f\<close> \<open>S \<noteq> {}\<close> convex_linear_image[of f S]  linear_conv_bounded_linear[of f]
      by auto
  }
  ultimately show ?thesis by auto
qed

lemma rel_interior_convex_linear_preimage:
  fixes f :: "'m::euclidean_space \<Rightarrow> 'n::euclidean_space"
  assumes "linear f"
    and "convex S"
    and "f -` (rel_interior S) \<noteq> {}"
  shows "rel_interior (f -` S) = f -` (rel_interior S)"
proof -
  have "S \<noteq> {}"
    using assms rel_interior_empty by auto
  have nonemp: "f -` S \<noteq> {}"
    by (metis assms(3) rel_interior_subset subset_empty vimage_mono)
  then have "S \<inter> (range f) \<noteq> {}"
    by auto
  have conv: "convex (f -` S)"
    using convex_linear_vimage assms by auto
  then have "convex (S \<inter> range f)"
    by (metis assms(1) assms(2) convex_Int subspace_UNIV subspace_imp_convex subspace_linear_image)
  {
    fix z
    assume "z \<in> f -` (rel_interior S)"
    then have z: "f z : rel_interior S"
      by auto
    {
      fix x
      assume "x \<in> f -` S"
      then have "f x \<in> S" by auto
      then obtain e where e: "e > 1" "(1 - e) *\<^sub>R f x + e *\<^sub>R f z \<in> S"
        using convex_rel_interior_iff[of S "f z"] z assms \<open>S \<noteq> {}\<close> by auto
      moreover have "(1 - e) *\<^sub>R f x + e *\<^sub>R f z = f ((1 - e) *\<^sub>R x + e *\<^sub>R z)"
        using \<open>linear f\<close> by (simp add: linear_iff)
      ultimately have "\<exists>e. e > 1 \<and> (1 - e) *\<^sub>R x + e *\<^sub>R z \<in> f -` S"
        using e by auto
    }
    then have "z \<in> rel_interior (f -` S)"
      using convex_rel_interior_iff[of "f -` S" z] conv nonemp by auto
  }
  moreover
  {
    fix z
    assume z: "z \<in> rel_interior (f -` S)"
    {
      fix x
      assume "x \<in> S \<inter> range f"
      then obtain y where y: "f y = x" "y \<in> f -` S" by auto
      then obtain e where e: "e > 1" "(1 - e) *\<^sub>R y + e *\<^sub>R z \<in> f -` S"
        using convex_rel_interior_iff[of "f -` S" z] z conv by auto
      moreover have "(1 - e) *\<^sub>R x + e *\<^sub>R f z = f ((1 - e) *\<^sub>R y + e *\<^sub>R z)"
        using \<open>linear f\<close> y by (simp add: linear_iff)
      ultimately have "\<exists>e. e > 1 \<and> (1 - e) *\<^sub>R x + e *\<^sub>R f z \<in> S \<inter> range f"
        using e by auto
    }
    then have "f z \<in> rel_interior (S \<inter> range f)"
      using \<open>convex (S \<inter> (range f))\<close> \<open>S \<inter> range f \<noteq> {}\<close>
        convex_rel_interior_iff[of "S \<inter> (range f)" "f z"]
      by auto
    moreover have "affine (range f)"
      by (metis assms(1) subspace_UNIV subspace_imp_affine subspace_linear_image)
    ultimately have "f z \<in> rel_interior S"
      using convex_affine_rel_interior_Int[of S "range f"] assms by auto
    then have "z \<in> f -` (rel_interior S)"
      by auto
  }
  ultimately show ?thesis by auto
qed

lemma rel_interior_Times:
  fixes S :: "'n::euclidean_space set"
    and T :: "'m::euclidean_space set"
  assumes "convex S"
    and "convex T"
  shows "rel_interior (S \<times> T) = rel_interior S \<times> rel_interior T"
proof -
  { assume "S = {}"
    then have ?thesis
      by auto
  }
  moreover
  { assume "T = {}"
    then have ?thesis
       by auto
  }
  moreover
  {
    assume "S \<noteq> {}" "T \<noteq> {}"
    then have ri: "rel_interior S \<noteq> {}" "rel_interior T \<noteq> {}"
      using rel_interior_eq_empty assms by auto
    then have "fst -` rel_interior S \<noteq> {}"
      using fst_vimage_eq_Times[of "rel_interior S"] by auto
    then have "rel_interior ((fst :: 'n * 'm \<Rightarrow> 'n) -` S) = fst -` rel_interior S"
      using fst_linear \<open>convex S\<close> rel_interior_convex_linear_preimage[of fst S] by auto
    then have s: "rel_interior (S \<times> (UNIV :: 'm set)) = rel_interior S \<times> UNIV"
      by (simp add: fst_vimage_eq_Times)
    from ri have "snd -` rel_interior T \<noteq> {}"
      using snd_vimage_eq_Times[of "rel_interior T"] by auto
    then have "rel_interior ((snd :: 'n * 'm \<Rightarrow> 'm) -` T) = snd -` rel_interior T"
      using snd_linear \<open>convex T\<close> rel_interior_convex_linear_preimage[of snd T] by auto
    then have t: "rel_interior ((UNIV :: 'n set) \<times> T) = UNIV \<times> rel_interior T"
      by (simp add: snd_vimage_eq_Times)
    from s t have *: "rel_interior (S \<times> (UNIV :: 'm set)) \<inter> rel_interior ((UNIV :: 'n set) \<times> T) =
      rel_interior S \<times> rel_interior T" by auto
    have "S \<times> T = S \<times> (UNIV :: 'm set) \<inter> (UNIV :: 'n set) \<times> T"
      by auto
    then have "rel_interior (S \<times> T) = rel_interior ((S \<times> (UNIV :: 'm set)) \<inter> ((UNIV :: 'n set) \<times> T))"
      by auto
    also have "\<dots> = rel_interior (S \<times> (UNIV :: 'm set)) \<inter> rel_interior ((UNIV :: 'n set) \<times> T)"
       apply (subst convex_rel_interior_inter_two[of "S \<times> (UNIV :: 'm set)" "(UNIV :: 'n set) \<times> T"])
       using * ri assms convex_Times
       apply auto
       done
    finally have ?thesis using * by auto
  }
  ultimately show ?thesis by blast
qed

lemma rel_interior_scaleR:
  fixes S :: "'n::euclidean_space set"
  assumes "c \<noteq> 0"
  shows "(op *\<^sub>R c) ` (rel_interior S) = rel_interior ((op *\<^sub>R c) ` S)"
  using rel_interior_injective_linear_image[of "(op *\<^sub>R c)" S]
    linear_conv_bounded_linear[of "op *\<^sub>R c"] linear_scaleR injective_scaleR[of c] assms
  by auto

lemma rel_interior_convex_scaleR:
  fixes S :: "'n::euclidean_space set"
  assumes "convex S"
  shows "(op *\<^sub>R c) ` (rel_interior S) = rel_interior ((op *\<^sub>R c) ` S)"
  by (metis assms linear_scaleR rel_interior_convex_linear_image)

lemma convex_rel_open_scaleR:
  fixes S :: "'n::euclidean_space set"
  assumes "convex S"
    and "rel_open S"
  shows "convex ((op *\<^sub>R c) ` S) \<and> rel_open ((op *\<^sub>R c) ` S)"
  by (metis assms convex_scaling rel_interior_convex_scaleR rel_open_def)

lemma convex_rel_open_finite_inter:
  assumes "\<forall>S\<in>I. convex (S :: 'n::euclidean_space set) \<and> rel_open S"
    and "finite I"
  shows "convex (\<Inter>I) \<and> rel_open (\<Inter>I)"
proof (cases "\<Inter>{rel_interior S |S. S \<in> I} = {}")
  case True
  then have "\<Inter>I = {}"
    using assms unfolding rel_open_def by auto
  then show ?thesis
    unfolding rel_open_def using rel_interior_empty by auto
next
  case False
  then have "rel_open (\<Inter>I)"
    using assms unfolding rel_open_def
    using convex_rel_interior_finite_inter[of I]
    by auto
  then show ?thesis
    using convex_Inter assms by auto
qed

lemma convex_rel_open_linear_image:
  fixes f :: "'m::euclidean_space \<Rightarrow> 'n::euclidean_space"
  assumes "linear f"
    and "convex S"
    and "rel_open S"
  shows "convex (f ` S) \<and> rel_open (f ` S)"
  by (metis assms convex_linear_image rel_interior_convex_linear_image rel_open_def)

lemma convex_rel_open_linear_preimage:
  fixes f :: "'m::euclidean_space \<Rightarrow> 'n::euclidean_space"
  assumes "linear f"
    and "convex S"
    and "rel_open S"
  shows "convex (f -` S) \<and> rel_open (f -` S)"
proof (cases "f -` (rel_interior S) = {}")
  case True
  then have "f -` S = {}"
    using assms unfolding rel_open_def by auto
  then show ?thesis
    unfolding rel_open_def using rel_interior_empty by auto
next
  case False
  then have "rel_open (f -` S)"
    using assms unfolding rel_open_def
    using rel_interior_convex_linear_preimage[of f S]
    by auto
  then show ?thesis
    using convex_linear_vimage assms
    by auto
qed

lemma rel_interior_projection:
  fixes S :: "('m::euclidean_space \<times> 'n::euclidean_space) set"
    and f :: "'m::euclidean_space \<Rightarrow> 'n::euclidean_space set"
  assumes "convex S"
    and "f = (\<lambda>y. {z. (y, z) \<in> S})"
  shows "(y, z) \<in> rel_interior S \<longleftrightarrow> (y \<in> rel_interior {y. (f y \<noteq> {})} \<and> z \<in> rel_interior (f y))"
proof -
  {
    fix y
    assume "y \<in> {y. f y \<noteq> {}}"
    then obtain z where "(y, z) \<in> S"
      using assms by auto
    then have "\<exists>x. x \<in> S \<and> y = fst x"
      apply (rule_tac x="(y, z)" in exI)
      apply auto
      done
    then obtain x where "x \<in> S" "y = fst x"
      by blast
    then have "y \<in> fst ` S"
      unfolding image_def by auto
  }
  then have "fst ` S = {y. f y \<noteq> {}}"
    unfolding fst_def using assms by auto
  then have h1: "fst ` rel_interior S = rel_interior {y. f y \<noteq> {}}"
    using rel_interior_convex_linear_image[of fst S] assms fst_linear by auto
  {
    fix y
    assume "y \<in> rel_interior {y. f y \<noteq> {}}"
    then have "y \<in> fst ` rel_interior S"
      using h1 by auto
    then have *: "rel_interior S \<inter> fst -` {y} \<noteq> {}"
      by auto
    moreover have aff: "affine (fst -` {y})"
      unfolding affine_alt by (simp add: algebra_simps)
    ultimately have **: "rel_interior (S \<inter> fst -` {y}) = rel_interior S \<inter> fst -` {y}"
      using convex_affine_rel_interior_Int[of S "fst -` {y}"] assms by auto
    have conv: "convex (S \<inter> fst -` {y})"
      using convex_Int assms aff affine_imp_convex by auto
    {
      fix x
      assume "x \<in> f y"
      then have "(y, x) \<in> S \<inter> (fst -` {y})"
        using assms by auto
      moreover have "x = snd (y, x)" by auto
      ultimately have "x \<in> snd ` (S \<inter> fst -` {y})"
        by blast
    }
    then have "snd ` (S \<inter> fst -` {y}) = f y"
      using assms by auto
    then have ***: "rel_interior (f y) = snd ` rel_interior (S \<inter> fst -` {y})"
      using rel_interior_convex_linear_image[of snd "S \<inter> fst -` {y}"] snd_linear conv
      by auto
    {
      fix z
      assume "z \<in> rel_interior (f y)"
      then have "z \<in> snd ` rel_interior (S \<inter> fst -` {y})"
        using *** by auto
      moreover have "{y} = fst ` rel_interior (S \<inter> fst -` {y})"
        using * ** rel_interior_subset by auto
      ultimately have "(y, z) \<in> rel_interior (S \<inter> fst -` {y})"
        by force
      then have "(y,z) \<in> rel_interior S"
        using ** by auto
    }
    moreover
    {
      fix z
      assume "(y, z) \<in> rel_interior S"
      then have "(y, z) \<in> rel_interior (S \<inter> fst -` {y})"
        using ** by auto
      then have "z \<in> snd ` rel_interior (S \<inter> fst -` {y})"
        by (metis Range_iff snd_eq_Range)
      then have "z \<in> rel_interior (f y)"
        using *** by auto
    }
    ultimately have "\<And>z. (y, z) \<in> rel_interior S \<longleftrightarrow> z \<in> rel_interior (f y)"
      by auto
  }
  then have h2: "\<And>y z. y \<in> rel_interior {t. f t \<noteq> {}} \<Longrightarrow>
    (y, z) \<in> rel_interior S \<longleftrightarrow> z \<in> rel_interior (f y)"
    by auto
  {
    fix y z
    assume asm: "(y, z) \<in> rel_interior S"
    then have "y \<in> fst ` rel_interior S"
      by (metis Domain_iff fst_eq_Domain)
    then have "y \<in> rel_interior {t. f t \<noteq> {}}"
      using h1 by auto
    then have "y \<in> rel_interior {t. f t \<noteq> {}}" and "(z : rel_interior (f y))"
      using h2 asm by auto
  }
  then show ?thesis using h2 by blast
qed

lemma rel_frontier_Times:
  fixes S :: "'n::euclidean_space set"
    and T :: "'m::euclidean_space set"
  assumes "convex S"
    and "convex T"
  shows "rel_frontier S \<times> rel_frontier T \<subseteq> rel_frontier (S \<times> T)"
    by (force simp: rel_frontier_def rel_interior_Times assms closure_Times)


subsubsection \<open>Relative interior of convex cone\<close>

lemma cone_rel_interior:
  fixes S :: "'m::euclidean_space set"
  assumes "cone S"
  shows "cone ({0} \<union> rel_interior S)"
proof (cases "S = {}")
  case True
  then show ?thesis
    by (simp add: rel_interior_empty cone_0)
next
  case False
  then have *: "0 \<in> S \<and> (\<forall>c. c > 0 \<longrightarrow> op *\<^sub>R c ` S = S)"
    using cone_iff[of S] assms by auto
  then have *: "0 \<in> ({0} \<union> rel_interior S)"
    and "\<forall>c. c > 0 \<longrightarrow> op *\<^sub>R c ` ({0} \<union> rel_interior S) = ({0} \<union> rel_interior S)"
    by (auto simp add: rel_interior_scaleR)
  then show ?thesis
    using cone_iff[of "{0} \<union> rel_interior S"] by auto
qed

lemma rel_interior_convex_cone_aux:
  fixes S :: "'m::euclidean_space set"
  assumes "convex S"
  shows "(c, x) \<in> rel_interior (cone hull ({(1 :: real)} \<times> S)) \<longleftrightarrow>
    c > 0 \<and> x \<in> ((op *\<^sub>R c) ` (rel_interior S))"
proof (cases "S = {}")
  case True
  then show ?thesis
    by (simp add: rel_interior_empty cone_hull_empty)
next
  case False
  then obtain s where "s \<in> S" by auto
  have conv: "convex ({(1 :: real)} \<times> S)"
    using convex_Times[of "{(1 :: real)}" S] assms convex_singleton[of "1 :: real"]
    by auto
  define f where "f y = {z. (y, z) \<in> cone hull ({1 :: real} \<times> S)}" for y
  then have *: "(c, x) \<in> rel_interior (cone hull ({(1 :: real)} \<times> S)) =
    (c \<in> rel_interior {y. f y \<noteq> {}} \<and> x \<in> rel_interior (f c))"
    apply (subst rel_interior_projection[of "cone hull ({(1 :: real)} \<times> S)" f c x])
    using convex_cone_hull[of "{(1 :: real)} \<times> S"] conv
    apply auto
    done
  {
    fix y :: real
    assume "y \<ge> 0"
    then have "y *\<^sub>R (1,s) \<in> cone hull ({1 :: real} \<times> S)"
      using cone_hull_expl[of "{(1 :: real)} \<times> S"] \<open>s \<in> S\<close> by auto
    then have "f y \<noteq> {}"
      using f_def by auto
  }
  then have "{y. f y \<noteq> {}} = {0..}"
    using f_def cone_hull_expl[of "{1 :: real} \<times> S"] by auto
  then have **: "rel_interior {y. f y \<noteq> {}} = {0<..}"
    using rel_interior_real_semiline by auto
  {
    fix c :: real
    assume "c > 0"
    then have "f c = (op *\<^sub>R c ` S)"
      using f_def cone_hull_expl[of "{1 :: real} \<times> S"] by auto
    then have "rel_interior (f c) = op *\<^sub>R c ` rel_interior S"
      using rel_interior_convex_scaleR[of S c] assms by auto
  }
  then show ?thesis using * ** by auto
qed

lemma rel_interior_convex_cone:
  fixes S :: "'m::euclidean_space set"
  assumes "convex S"
  shows "rel_interior (cone hull ({1 :: real} \<times> S)) =
    {(c, c *\<^sub>R x) | c x. c > 0 \<and> x \<in> rel_interior S}"
  (is "?lhs = ?rhs")
proof -
  {
    fix z
    assume "z \<in> ?lhs"
    have *: "z = (fst z, snd z)"
      by auto
    have "z \<in> ?rhs"
      using rel_interior_convex_cone_aux[of S "fst z" "snd z"] assms \<open>z \<in> ?lhs\<close>
      apply auto
      apply (rule_tac x = "fst z" in exI)
      apply (rule_tac x = x in exI)
      using *
      apply auto
      done
  }
  moreover
  {
    fix z
    assume "z \<in> ?rhs"
    then have "z \<in> ?lhs"
      using rel_interior_convex_cone_aux[of S "fst z" "snd z"] assms
      by auto
  }
  ultimately show ?thesis by blast
qed

lemma convex_hull_finite_union:
  assumes "finite I"
  assumes "\<forall>i\<in>I. convex (S i) \<and> (S i) \<noteq> {}"
  shows "convex hull (\<Union>(S ` I)) =
    {sum (\<lambda>i. c i *\<^sub>R s i) I | c s. (\<forall>i\<in>I. c i \<ge> 0) \<and> sum c I = 1 \<and> (\<forall>i\<in>I. s i \<in> S i)}"
  (is "?lhs = ?rhs")
proof -
  have "?lhs \<supseteq> ?rhs"
  proof
    fix x
    assume "x : ?rhs"
    then obtain c s where *: "sum (\<lambda>i. c i *\<^sub>R s i) I = x" "sum c I = 1"
      "(\<forall>i\<in>I. c i \<ge> 0) \<and> (\<forall>i\<in>I. s i \<in> S i)" by auto
    then have "\<forall>i\<in>I. s i \<in> convex hull (\<Union>(S ` I))"
      using hull_subset[of "\<Union>(S ` I)" convex] by auto
    then show "x \<in> ?lhs"
      unfolding *(1)[symmetric]
      apply (subst convex_sum[of I "convex hull \<Union>(S ` I)" c s])
      using * assms convex_convex_hull
      apply auto
      done
  qed

  {
    fix i
    assume "i \<in> I"
    with assms have "\<exists>p. p \<in> S i" by auto
  }
  then obtain p where p: "\<forall>i\<in>I. p i \<in> S i" by metis

  {
    fix i
    assume "i \<in> I"
    {
      fix x
      assume "x \<in> S i"
      define c where "c j = (if j = i then 1::real else 0)" for j
      then have *: "sum c I = 1"
        using \<open>finite I\<close> \<open>i \<in> I\<close> sum.delta[of I i "\<lambda>j::'a. 1::real"]
        by auto
      define s where "s j = (if j = i then x else p j)" for j
      then have "\<forall>j. c j *\<^sub>R s j = (if j = i then x else 0)"
        using c_def by (auto simp add: algebra_simps)
      then have "x = sum (\<lambda>i. c i *\<^sub>R s i) I"
        using s_def c_def \<open>finite I\<close> \<open>i \<in> I\<close> sum.delta[of I i "\<lambda>j::'a. x"]
        by auto
      then have "x \<in> ?rhs"
        apply auto
        apply (rule_tac x = c in exI)
        apply (rule_tac x = s in exI)
        using * c_def s_def p \<open>x \<in> S i\<close>
        apply auto
        done
    }
    then have "?rhs \<supseteq> S i" by auto
  }
  then have *: "?rhs \<supseteq> \<Union>(S ` I)" by auto

  {
    fix u v :: real
    assume uv: "u \<ge> 0 \<and> v \<ge> 0 \<and> u + v = 1"
    fix x y
    assume xy: "x \<in> ?rhs \<and> y \<in> ?rhs"
    from xy obtain c s where
      xc: "x = sum (\<lambda>i. c i *\<^sub>R s i) I \<and> (\<forall>i\<in>I. c i \<ge> 0) \<and> sum c I = 1 \<and> (\<forall>i\<in>I. s i \<in> S i)"
      by auto
    from xy obtain d t where
      yc: "y = sum (\<lambda>i. d i *\<^sub>R t i) I \<and> (\<forall>i\<in>I. d i \<ge> 0) \<and> sum d I = 1 \<and> (\<forall>i\<in>I. t i \<in> S i)"
      by auto
    define e where "e i = u * c i + v * d i" for i
    have ge0: "\<forall>i\<in>I. e i \<ge> 0"
      using e_def xc yc uv by simp
    have "sum (\<lambda>i. u * c i) I = u * sum c I"
      by (simp add: sum_distrib_left)
    moreover have "sum (\<lambda>i. v * d i) I = v * sum d I"
      by (simp add: sum_distrib_left)
    ultimately have sum1: "sum e I = 1"
      using e_def xc yc uv by (simp add: sum.distrib)
    define q where "q i = (if e i = 0 then p i else (u * c i / e i) *\<^sub>R s i + (v * d i / e i) *\<^sub>R t i)"
      for i
    {
      fix i
      assume i: "i \<in> I"
      have "q i \<in> S i"
      proof (cases "e i = 0")
        case True
        then show ?thesis using i p q_def by auto
      next
        case False
        then show ?thesis
          using mem_convex_alt[of "S i" "s i" "t i" "u * (c i)" "v * (d i)"]
            mult_nonneg_nonneg[of u "c i"] mult_nonneg_nonneg[of v "d i"]
            assms q_def e_def i False xc yc uv
          by (auto simp del: mult_nonneg_nonneg)
      qed
    }
    then have qs: "\<forall>i\<in>I. q i \<in> S i" by auto
    {
      fix i
      assume i: "i \<in> I"
      have "(u * c i) *\<^sub>R s i + (v * d i) *\<^sub>R t i = e i *\<^sub>R q i"
      proof (cases "e i = 0")
        case True
        have ge: "u * (c i) \<ge> 0 \<and> v * d i \<ge> 0"
          using xc yc uv i by simp
        moreover from ge have "u * c i \<le> 0 \<and> v * d i \<le> 0"
          using True e_def i by simp
        ultimately have "u * c i = 0 \<and> v * d i = 0" by auto
        with True show ?thesis by auto
      next
        case False
        then have "(u * (c i)/(e i))*\<^sub>R (s i)+(v * (d i)/(e i))*\<^sub>R (t i) = q i"
          using q_def by auto
        then have "e i *\<^sub>R ((u * (c i)/(e i))*\<^sub>R (s i)+(v * (d i)/(e i))*\<^sub>R (t i))
               = (e i) *\<^sub>R (q i)" by auto
        with False show ?thesis by (simp add: algebra_simps)
      qed
    }
    then have *: "\<forall>i\<in>I. (u * c i) *\<^sub>R s i + (v * d i) *\<^sub>R t i = e i *\<^sub>R q i"
      by auto
    have "u *\<^sub>R x + v *\<^sub>R y = sum (\<lambda>i. (u * c i) *\<^sub>R s i + (v * d i) *\<^sub>R t i) I"
      using xc yc by (simp add: algebra_simps scaleR_right.sum sum.distrib)
    also have "\<dots> = sum (\<lambda>i. e i *\<^sub>R q i) I"
      using * by auto
    finally have "u *\<^sub>R x + v *\<^sub>R y = sum (\<lambda>i. (e i) *\<^sub>R (q i)) I"
      by auto
    then have "u *\<^sub>R x + v *\<^sub>R y \<in> ?rhs"
      using ge0 sum1 qs by auto
  }
  then have "convex ?rhs" unfolding convex_def by auto
  then show ?thesis
    using \<open>?lhs \<supseteq> ?rhs\<close> * hull_minimal[of "\<Union>(S ` I)" ?rhs convex]
    by blast
qed

lemma convex_hull_union_two:
  fixes S T :: "'m::euclidean_space set"
  assumes "convex S"
    and "S \<noteq> {}"
    and "convex T"
    and "T \<noteq> {}"
  shows "convex hull (S \<union> T) =
    {u *\<^sub>R s + v *\<^sub>R t | u v s t. u \<ge> 0 \<and> v \<ge> 0 \<and> u + v = 1 \<and> s \<in> S \<and> t \<in> T}"
  (is "?lhs = ?rhs")
proof
  define I :: "nat set" where "I = {1, 2}"
  define s where "s i = (if i = (1::nat) then S else T)" for i
  have "\<Union>(s ` I) = S \<union> T"
    using s_def I_def by auto
  then have "convex hull (\<Union>(s ` I)) = convex hull (S \<union> T)"
    by auto
  moreover have "convex hull \<Union>(s ` I) =
    {\<Sum> i\<in>I. c i *\<^sub>R sa i | c sa. (\<forall>i\<in>I. 0 \<le> c i) \<and> sum c I = 1 \<and> (\<forall>i\<in>I. sa i \<in> s i)}"
      apply (subst convex_hull_finite_union[of I s])
      using assms s_def I_def
      apply auto
      done
  moreover have
    "{\<Sum>i\<in>I. c i *\<^sub>R sa i | c sa. (\<forall>i\<in>I. 0 \<le> c i) \<and> sum c I = 1 \<and> (\<forall>i\<in>I. sa i \<in> s i)} \<le> ?rhs"
    using s_def I_def by auto
  ultimately show "?lhs \<subseteq> ?rhs" by auto
  {
    fix x
    assume "x \<in> ?rhs"
    then obtain u v s t where *: "x = u *\<^sub>R s + v *\<^sub>R t \<and> u \<ge> 0 \<and> v \<ge> 0 \<and> u + v = 1 \<and> s \<in> S \<and> t \<in> T"
      by auto
    then have "x \<in> convex hull {s, t}"
      using convex_hull_2[of s t] by auto
    then have "x \<in> convex hull (S \<union> T)"
      using * hull_mono[of "{s, t}" "S \<union> T"] by auto
  }
  then show "?lhs \<supseteq> ?rhs" by blast
qed


subsection \<open>Convexity on direct sums\<close>

lemma closure_sum:
  fixes S T :: "'a::real_normed_vector set"
  shows "closure S + closure T \<subseteq> closure (S + T)"
  unfolding set_plus_image closure_Times [symmetric] split_def
  by (intro closure_bounded_linear_image_subset bounded_linear_add
    bounded_linear_fst bounded_linear_snd)

lemma rel_interior_sum:
  fixes S T :: "'n::euclidean_space set"
  assumes "convex S"
    and "convex T"
  shows "rel_interior (S + T) = rel_interior S + rel_interior T"
proof -
  have "rel_interior S + rel_interior T = (\<lambda>(x,y). x + y) ` (rel_interior S \<times> rel_interior T)"
    by (simp add: set_plus_image)
  also have "\<dots> = (\<lambda>(x,y). x + y) ` rel_interior (S \<times> T)"
    using rel_interior_Times assms by auto
  also have "\<dots> = rel_interior (S + T)"
    using fst_snd_linear convex_Times assms
      rel_interior_convex_linear_image[of "(\<lambda>(x,y). x + y)" "S \<times> T"]
    by (auto simp add: set_plus_image)
  finally show ?thesis ..
qed

lemma rel_interior_sum_gen:
  fixes S :: "'a \<Rightarrow> 'n::euclidean_space set"
  assumes "\<forall>i\<in>I. convex (S i)"
  shows "rel_interior (sum S I) = sum (\<lambda>i. rel_interior (S i)) I"
  apply (subst sum_set_cond_linear[of convex])
  using rel_interior_sum rel_interior_sing[of "0"] assms
  apply (auto simp add: convex_set_plus)
  done

lemma convex_rel_open_direct_sum:
  fixes S T :: "'n::euclidean_space set"
  assumes "convex S"
    and "rel_open S"
    and "convex T"
    and "rel_open T"
  shows "convex (S \<times> T) \<and> rel_open (S \<times> T)"
  by (metis assms convex_Times rel_interior_Times rel_open_def)

lemma convex_rel_open_sum:
  fixes S T :: "'n::euclidean_space set"
  assumes "convex S"
    and "rel_open S"
    and "convex T"
    and "rel_open T"
  shows "convex (S + T) \<and> rel_open (S + T)"
  by (metis assms convex_set_plus rel_interior_sum rel_open_def)

lemma convex_hull_finite_union_cones:
  assumes "finite I"
    and "I \<noteq> {}"
  assumes "\<forall>i\<in>I. convex (S i) \<and> cone (S i) \<and> S i \<noteq> {}"
  shows "convex hull (\<Union>(S ` I)) = sum S I"
  (is "?lhs = ?rhs")
proof -
  {
    fix x
    assume "x \<in> ?lhs"
    then obtain c xs where
      x: "x = sum (\<lambda>i. c i *\<^sub>R xs i) I \<and> (\<forall>i\<in>I. c i \<ge> 0) \<and> sum c I = 1 \<and> (\<forall>i\<in>I. xs i \<in> S i)"
      using convex_hull_finite_union[of I S] assms by auto
    define s where "s i = c i *\<^sub>R xs i" for i
    {
      fix i
      assume "i \<in> I"
      then have "s i \<in> S i"
        using s_def x assms mem_cone[of "S i" "xs i" "c i"] by auto
    }
    then have "\<forall>i\<in>I. s i \<in> S i" by auto
    moreover have "x = sum s I" using x s_def by auto
    ultimately have "x \<in> ?rhs"
      using set_sum_alt[of I S] assms by auto
  }
  moreover
  {
    fix x
    assume "x \<in> ?rhs"
    then obtain s where x: "x = sum s I \<and> (\<forall>i\<in>I. s i \<in> S i)"
      using set_sum_alt[of I S] assms by auto
    define xs where "xs i = of_nat(card I) *\<^sub>R s i" for i
    then have "x = sum (\<lambda>i. ((1 :: real) / of_nat(card I)) *\<^sub>R xs i) I"
      using x assms by auto
    moreover have "\<forall>i\<in>I. xs i \<in> S i"
      using x xs_def assms by (simp add: cone_def)
    moreover have "\<forall>i\<in>I. (1 :: real) / of_nat (card I) \<ge> 0"
      by auto
    moreover have "sum (\<lambda>i. (1 :: real) / of_nat (card I)) I = 1"
      using assms by auto
    ultimately have "x \<in> ?lhs"
      apply (subst convex_hull_finite_union[of I S])
      using assms
      apply blast
      using assms
      apply blast
      apply rule
      apply (rule_tac x = "(\<lambda>i. (1 :: real) / of_nat (card I))" in exI)
      apply auto
      done
  }
  ultimately show ?thesis by auto
qed

lemma convex_hull_union_cones_two:
  fixes S T :: "'m::euclidean_space set"
  assumes "convex S"
    and "cone S"
    and "S \<noteq> {}"
  assumes "convex T"
    and "cone T"
    and "T \<noteq> {}"
  shows "convex hull (S \<union> T) = S + T"
proof -
  define I :: "nat set" where "I = {1, 2}"
  define A where "A i = (if i = (1::nat) then S else T)" for i
  have "\<Union>(A ` I) = S \<union> T"
    using A_def I_def by auto
  then have "convex hull (\<Union>(A ` I)) = convex hull (S \<union> T)"
    by auto
  moreover have "convex hull \<Union>(A ` I) = sum A I"
    apply (subst convex_hull_finite_union_cones[of I A])
    using assms A_def I_def
    apply auto
    done
  moreover have "sum A I = S + T"
    using A_def I_def
    unfolding set_plus_def
    apply auto
    unfolding set_plus_def
    apply auto
    done
  ultimately show ?thesis by auto
qed

lemma rel_interior_convex_hull_union:
  fixes S :: "'a \<Rightarrow> 'n::euclidean_space set"
  assumes "finite I"
    and "\<forall>i\<in>I. convex (S i) \<and> S i \<noteq> {}"
  shows "rel_interior (convex hull (\<Union>(S ` I))) =
    {sum (\<lambda>i. c i *\<^sub>R s i) I | c s. (\<forall>i\<in>I. c i > 0) \<and> sum c I = 1 \<and>
      (\<forall>i\<in>I. s i \<in> rel_interior(S i))}"
  (is "?lhs = ?rhs")
proof (cases "I = {}")
  case True
  then show ?thesis
    using convex_hull_empty rel_interior_empty by auto
next
  case False
  define C0 where "C0 = convex hull (\<Union>(S ` I))"
  have "\<forall>i\<in>I. C0 \<ge> S i"
    unfolding C0_def using hull_subset[of "\<Union>(S ` I)"] by auto
  define K0 where "K0 = cone hull ({1 :: real} \<times> C0)"
  define K where "K i = cone hull ({1 :: real} \<times> S i)" for i
  have "\<forall>i\<in>I. K i \<noteq> {}"
    unfolding K_def using assms
    by (simp add: cone_hull_empty_iff[symmetric])
  {
    fix i
    assume "i \<in> I"
    then have "convex (K i)"
      unfolding K_def
      apply (subst convex_cone_hull)
      apply (subst convex_Times)
      using assms
      apply auto
      done
  }
  then have convK: "\<forall>i\<in>I. convex (K i)"
    by auto
  {
    fix i
    assume "i \<in> I"
    then have "K0 \<supseteq> K i"
      unfolding K0_def K_def
      apply (subst hull_mono)
      using \<open>\<forall>i\<in>I. C0 \<ge> S i\<close>
      apply auto
      done
  }
  then have "K0 \<supseteq> \<Union>(K ` I)" by auto
  moreover have "convex K0"
    unfolding K0_def
    apply (subst convex_cone_hull)
    apply (subst convex_Times)
    unfolding C0_def
    using convex_convex_hull
    apply auto
    done
  ultimately have geq: "K0 \<supseteq> convex hull (\<Union>(K ` I))"
    using hull_minimal[of _ "K0" "convex"] by blast
  have "\<forall>i\<in>I. K i \<supseteq> {1 :: real} \<times> S i"
    using K_def by (simp add: hull_subset)
  then have "\<Union>(K ` I) \<supseteq> {1 :: real} \<times> \<Union>(S ` I)"
    by auto
  then have "convex hull \<Union>(K ` I) \<supseteq> convex hull ({1 :: real} \<times> \<Union>(S ` I))"
    by (simp add: hull_mono)
  then have "convex hull \<Union>(K ` I) \<supseteq> {1 :: real} \<times> C0"
    unfolding C0_def
    using convex_hull_Times[of "{(1 :: real)}" "\<Union>(S ` I)"] convex_hull_singleton
    by auto
  moreover have "cone (convex hull (\<Union>(K ` I)))"
    apply (subst cone_convex_hull)
    using cone_Union[of "K ` I"]
    apply auto
    unfolding K_def
    using cone_cone_hull
    apply auto
    done
  ultimately have "convex hull (\<Union>(K ` I)) \<supseteq> K0"
    unfolding K0_def
    using hull_minimal[of _ "convex hull (\<Union>(K ` I))" "cone"]
    by blast
  then have "K0 = convex hull (\<Union>(K ` I))"
    using geq by auto
  also have "\<dots> = sum K I"
    apply (subst convex_hull_finite_union_cones[of I K])
    using assms
    apply blast
    using False
    apply blast
    unfolding K_def
    apply rule
    apply (subst convex_cone_hull)
    apply (subst convex_Times)
    using assms cone_cone_hull \<open>\<forall>i\<in>I. K i \<noteq> {}\<close> K_def
    apply auto
    done
  finally have "K0 = sum K I" by auto
  then have *: "rel_interior K0 = sum (\<lambda>i. (rel_interior (K i))) I"
    using rel_interior_sum_gen[of I K] convK by auto
  {
    fix x
    assume "x \<in> ?lhs"
    then have "(1::real, x) \<in> rel_interior K0"
      using K0_def C0_def rel_interior_convex_cone_aux[of C0 "1::real" x] convex_convex_hull
      by auto
    then obtain k where k: "(1::real, x) = sum k I \<and> (\<forall>i\<in>I. k i \<in> rel_interior (K i))"
      using \<open>finite I\<close> * set_sum_alt[of I "\<lambda>i. rel_interior (K i)"] by auto
    {
      fix i
      assume "i \<in> I"
      then have "convex (S i) \<and> k i \<in> rel_interior (cone hull {1} \<times> S i)"
        using k K_def assms by auto
      then have "\<exists>ci si. k i = (ci, ci *\<^sub>R si) \<and> 0 < ci \<and> si \<in> rel_interior (S i)"
        using rel_interior_convex_cone[of "S i"] by auto
    }
    then obtain c s where
      cs: "\<forall>i\<in>I. k i = (c i, c i *\<^sub>R s i) \<and> 0 < c i \<and> s i \<in> rel_interior (S i)"
      by metis
    then have "x = (\<Sum>i\<in>I. c i *\<^sub>R s i) \<and> sum c I = 1"
      using k by (simp add: sum_prod)
    then have "x \<in> ?rhs"
      using k
      apply auto
      apply (rule_tac x = c in exI)
      apply (rule_tac x = s in exI)
      using cs
      apply auto
      done
  }
  moreover
  {
    fix x
    assume "x \<in> ?rhs"
    then obtain c s where cs: "x = sum (\<lambda>i. c i *\<^sub>R s i) I \<and>
        (\<forall>i\<in>I. c i > 0) \<and> sum c I = 1 \<and> (\<forall>i\<in>I. s i \<in> rel_interior (S i))"
      by auto
    define k where "k i = (c i, c i *\<^sub>R s i)" for i
    {
      fix i assume "i:I"
      then have "k i \<in> rel_interior (K i)"
        using k_def K_def assms cs rel_interior_convex_cone[of "S i"]
        by auto
    }
    then have "(1::real, x) \<in> rel_interior K0"
      using K0_def * set_sum_alt[of I "(\<lambda>i. rel_interior (K i))"] assms k_def cs
      apply auto
      apply (rule_tac x = k in exI)
      apply (simp add: sum_prod)
      done
    then have "x \<in> ?lhs"
      using K0_def C0_def rel_interior_convex_cone_aux[of C0 1 x]
      by (auto simp add: convex_convex_hull)
  }
  ultimately show ?thesis by blast
qed


lemma convex_le_Inf_differential:
  fixes f :: "real \<Rightarrow> real"
  assumes "convex_on I f"
    and "x \<in> interior I"
    and "y \<in> I"
  shows "f y \<ge> f x + Inf ((\<lambda>t. (f x - f t) / (x - t)) ` ({x<..} \<inter> I)) * (y - x)"
  (is "_ \<ge> _ + Inf (?F x) * (y - x)")
proof (cases rule: linorder_cases)
  assume "x < y"
  moreover
  have "open (interior I)" by auto
  from openE[OF this \<open>x \<in> interior I\<close>]
  obtain e where e: "0 < e" "ball x e \<subseteq> interior I" .
  moreover define t where "t = min (x + e / 2) ((x + y) / 2)"
  ultimately have "x < t" "t < y" "t \<in> ball x e"
    by (auto simp: dist_real_def field_simps split: split_min)
  with \<open>x \<in> interior I\<close> e interior_subset[of I] have "t \<in> I" "x \<in> I" by auto

  have "open (interior I)" by auto
  from openE[OF this \<open>x \<in> interior I\<close>]
  obtain e where "0 < e" "ball x e \<subseteq> interior I" .
  moreover define K where "K = x - e / 2"
  with \<open>0 < e\<close> have "K \<in> ball x e" "K < x"
    by (auto simp: dist_real_def)
  ultimately have "K \<in> I" "K < x" "x \<in> I"
    using interior_subset[of I] \<open>x \<in> interior I\<close> by auto

  have "Inf (?F x) \<le> (f x - f y) / (x - y)"
  proof (intro bdd_belowI cInf_lower2)
    show "(f x - f t) / (x - t) \<in> ?F x"
      using \<open>t \<in> I\<close> \<open>x < t\<close> by auto
    show "(f x - f t) / (x - t) \<le> (f x - f y) / (x - y)"
      using \<open>convex_on I f\<close> \<open>x \<in> I\<close> \<open>y \<in> I\<close> \<open>x < t\<close> \<open>t < y\<close>
      by (rule convex_on_diff)
  next
    fix y
    assume "y \<in> ?F x"
    with order_trans[OF convex_on_diff[OF \<open>convex_on I f\<close> \<open>K \<in> I\<close> _ \<open>K < x\<close> _]]
    show "(f K - f x) / (K - x) \<le> y" by auto
  qed
  then show ?thesis
    using \<open>x < y\<close> by (simp add: field_simps)
next
  assume "y < x"
  moreover
  have "open (interior I)" by auto
  from openE[OF this \<open>x \<in> interior I\<close>]
  obtain e where e: "0 < e" "ball x e \<subseteq> interior I" .
  moreover define t where "t = x + e / 2"
  ultimately have "x < t" "t \<in> ball x e"
    by (auto simp: dist_real_def field_simps)
  with \<open>x \<in> interior I\<close> e interior_subset[of I] have "t \<in> I" "x \<in> I" by auto

  have "(f x - f y) / (x - y) \<le> Inf (?F x)"
  proof (rule cInf_greatest)
    have "(f x - f y) / (x - y) = (f y - f x) / (y - x)"
      using \<open>y < x\<close> by (auto simp: field_simps)
    also
    fix z
    assume "z \<in> ?F x"
    with order_trans[OF convex_on_diff[OF \<open>convex_on I f\<close> \<open>y \<in> I\<close> _ \<open>y < x\<close>]]
    have "(f y - f x) / (y - x) \<le> z"
      by auto
    finally show "(f x - f y) / (x - y) \<le> z" .
  next
    have "open (interior I)" by auto
    from openE[OF this \<open>x \<in> interior I\<close>]
    obtain e where e: "0 < e" "ball x e \<subseteq> interior I" .
    then have "x + e / 2 \<in> ball x e"
      by (auto simp: dist_real_def)
    with e interior_subset[of I] have "x + e / 2 \<in> {x<..} \<inter> I"
      by auto
    then show "?F x \<noteq> {}"
      by blast
  qed
  then show ?thesis
    using \<open>y < x\<close> by (simp add: field_simps)
qed simp

subsection\<open>Explicit formulas for interior and relative interior of convex hull\<close>

lemma interior_atLeastAtMost [simp]:
  fixes a::real shows "interior {a..b} = {a<..<b}"
  using interior_cbox [of a b] by auto

lemma interior_atLeastLessThan [simp]:
  fixes a::real shows "interior {a..<b} = {a<..<b}"
  by (metis atLeastLessThan_def greaterThanLessThan_def interior_atLeastAtMost interior_Int interior_interior interior_real_semiline)

lemma interior_lessThanAtMost [simp]:
  fixes a::real shows "interior {a<..b} = {a<..<b}"
  by (metis atLeastAtMost_def greaterThanAtMost_def interior_atLeastAtMost interior_Int
            interior_interior interior_real_semiline)

lemma at_within_closed_interval:
    fixes x::real
    shows "a < x \<Longrightarrow> x < b \<Longrightarrow> (at x within {a..b}) = at x"
  by (metis at_within_interior greaterThanLessThan_iff interior_atLeastAtMost)

lemma affine_independent_convex_affine_hull:
  fixes s :: "'a::euclidean_space set"
  assumes "~affine_dependent s" "t \<subseteq> s"
    shows "convex hull t = affine hull t \<inter> convex hull s"
proof -
  have fin: "finite s" "finite t" using assms aff_independent_finite finite_subset by auto
    { fix u v x
      assume uv: "sum u t = 1" "\<forall>x\<in>s. 0 \<le> v x" "sum v s = 1"
                 "(\<Sum>x\<in>s. v x *\<^sub>R x) = (\<Sum>v\<in>t. u v *\<^sub>R v)" "x \<in> t"
      then have s: "s = (s - t) \<union> t" \<comment>\<open>split into separate cases\<close>
        using assms by auto
      have [simp]: "(\<Sum>x\<in>t. v x *\<^sub>R x) + (\<Sum>x\<in>s - t. v x *\<^sub>R x) = (\<Sum>x\<in>t. u x *\<^sub>R x)"
                   "sum v t + sum v (s - t) = 1"
        using uv fin s
        by (auto simp: sum.union_disjoint [symmetric] Un_commute)
      have "(\<Sum>x\<in>s. if x \<in> t then v x - u x else v x) = 0"
           "(\<Sum>x\<in>s. (if x \<in> t then v x - u x else v x) *\<^sub>R x) = 0"
        using uv fin
        by (subst s, subst sum.union_disjoint, auto simp: algebra_simps sum_subtractf)+
    } note [simp] = this
  have "convex hull t \<subseteq> affine hull t"
    using convex_hull_subset_affine_hull by blast
  moreover have "convex hull t \<subseteq> convex hull s"
    using assms hull_mono by blast
  moreover have "affine hull t \<inter> convex hull s \<subseteq> convex hull t"
    using assms
    apply (simp add: convex_hull_finite affine_hull_finite fin affine_dependent_explicit)
    apply (drule_tac x=s in spec)
    apply (auto simp: fin)
    apply (rule_tac x=u in exI)
    apply (rename_tac v)
    apply (drule_tac x="\<lambda>x. if x \<in> t then v x - u x else v x" in spec)
    apply (force)+
    done
  ultimately show ?thesis
    by blast
qed

lemma affine_independent_span_eq:
  fixes s :: "'a::euclidean_space set"
  assumes "~affine_dependent s" "card s = Suc (DIM ('a))"
    shows "affine hull s = UNIV"
proof (cases "s = {}")
  case True then show ?thesis
    using assms by simp
next
  case False
    then obtain a t where t: "a \<notin> t" "s = insert a t"
      by blast
    then have fin: "finite t" using assms
      by (metis finite_insert aff_independent_finite)
    show ?thesis
    using assms t fin
      apply (simp add: affine_dependent_iff_dependent affine_hull_insert_span_gen)
      apply (rule subset_antisym)
      apply force
      apply (rule Fun.vimage_subsetD)
      apply (metis add.commute diff_add_cancel surj_def)
      apply (rule card_ge_dim_independent)
      apply (auto simp: card_image inj_on_def dim_subset_UNIV)
      done
qed

lemma affine_independent_span_gt:
  fixes s :: "'a::euclidean_space set"
  assumes ind: "~ affine_dependent s" and dim: "DIM ('a) < card s"
    shows "affine hull s = UNIV"
  apply (rule affine_independent_span_eq [OF ind])
  apply (rule antisym)
  using assms
  apply auto
  apply (metis add_2_eq_Suc' not_less_eq_eq affine_dependent_biggerset aff_independent_finite)
  done

lemma empty_interior_affine_hull:
  fixes s :: "'a::euclidean_space set"
  assumes "finite s" and dim: "card s \<le> DIM ('a)"
    shows "interior(affine hull s) = {}"
  using assms
  apply (induct s rule: finite_induct)
  apply (simp_all add:  affine_dependent_iff_dependent affine_hull_insert_span_gen interior_translation)
  apply (rule empty_interior_lowdim)
  apply (simp add: affine_dependent_iff_dependent affine_hull_insert_span_gen)
  apply (metis Suc_le_lessD not_less order_trans card_image_le finite_imageI dim_le_card)
  done

lemma empty_interior_convex_hull:
  fixes s :: "'a::euclidean_space set"
  assumes "finite s" and dim: "card s \<le> DIM ('a)"
    shows "interior(convex hull s) = {}"
  by (metis Diff_empty Diff_eq_empty_iff convex_hull_subset_affine_hull
            interior_mono empty_interior_affine_hull [OF assms])

lemma explicit_subset_rel_interior_convex_hull:
  fixes s :: "'a::euclidean_space set"
  shows "finite s
         \<Longrightarrow> {y. \<exists>u. (\<forall>x \<in> s. 0 < u x \<and> u x < 1) \<and> sum u s = 1 \<and> sum (\<lambda>x. u x *\<^sub>R x) s = y}
             \<subseteq> rel_interior (convex hull s)"
  by (force simp add:  rel_interior_convex_hull_union [where S="\<lambda>x. {x}" and I=s, simplified])

lemma explicit_subset_rel_interior_convex_hull_minimal:
  fixes s :: "'a::euclidean_space set"
  shows "finite s
         \<Longrightarrow> {y. \<exists>u. (\<forall>x \<in> s. 0 < u x) \<and> sum u s = 1 \<and> sum (\<lambda>x. u x *\<^sub>R x) s = y}
             \<subseteq> rel_interior (convex hull s)"
  by (force simp add:  rel_interior_convex_hull_union [where S="\<lambda>x. {x}" and I=s, simplified])

lemma rel_interior_convex_hull_explicit:
  fixes s :: "'a::euclidean_space set"
  assumes "~ affine_dependent s"
  shows "rel_interior(convex hull s) =
         {y. \<exists>u. (\<forall>x \<in> s. 0 < u x) \<and> sum u s = 1 \<and> sum (\<lambda>x. u x *\<^sub>R x) s = y}"
         (is "?lhs = ?rhs")
proof
  show "?rhs \<le> ?lhs"
    by (simp add: aff_independent_finite explicit_subset_rel_interior_convex_hull_minimal assms)
next
  show "?lhs \<le> ?rhs"
  proof (cases "\<exists>a. s = {a}")
    case True then show "?lhs \<le> ?rhs"
      by force
  next
    case False
    have fs: "finite s"
      using assms by (simp add: aff_independent_finite)
    { fix a b and d::real
      assume ab: "a \<in> s" "b \<in> s" "a \<noteq> b"
      then have s: "s = (s - {a,b}) \<union> {a,b}" \<comment>\<open>split into separate cases\<close>
        by auto
      have "(\<Sum>x\<in>s. if x = a then - d else if x = b then d else 0) = 0"
           "(\<Sum>x\<in>s. (if x = a then - d else if x = b then d else 0) *\<^sub>R x) = d *\<^sub>R b - d *\<^sub>R a"
        using ab fs
        by (subst s, subst sum.union_disjoint, auto)+
    } note [simp] = this
    { fix y
      assume y: "y \<in> convex hull s" "y \<notin> ?rhs"
      { fix u T a
        assume ua: "\<forall>x\<in>s. 0 \<le> u x" "sum u s = 1" "\<not> 0 < u a" "a \<in> s"
           and yT: "y = (\<Sum>x\<in>s. u x *\<^sub>R x)" "y \<in> T" "open T"
           and sb: "T \<inter> affine hull s \<subseteq> {w. \<exists>u. (\<forall>x\<in>s. 0 \<le> u x) \<and> sum u s = 1 \<and> (\<Sum>x\<in>s. u x *\<^sub>R x) = w}"
        have ua0: "u a = 0"
          using ua by auto
        obtain b where b: "b\<in>s" "a \<noteq> b"
          using ua False by auto
        obtain e where e: "0 < e" "ball (\<Sum>x\<in>s. u x *\<^sub>R x) e \<subseteq> T"
          using yT by (auto elim: openE)
        with b obtain d where d: "0 < d" "norm(d *\<^sub>R (a-b)) < e"
          by (auto intro: that [of "e / 2 / norm(a-b)"])
        have "(\<Sum>x\<in>s. u x *\<^sub>R x) \<in> affine hull s"
          using yT y by (metis affine_hull_convex_hull hull_redundant_eq)
        then have "(\<Sum>x\<in>s. u x *\<^sub>R x) - d *\<^sub>R (a - b) \<in> affine hull s"
          using ua b by (auto simp: hull_inc intro: mem_affine_3_minus2)
        then have "y - d *\<^sub>R (a - b) \<in> T \<inter> affine hull s"
          using d e yT by auto
        then obtain v where "\<forall>x\<in>s. 0 \<le> v x"
                            "sum v s = 1"
                            "(\<Sum>x\<in>s. v x *\<^sub>R x) = (\<Sum>x\<in>s. u x *\<^sub>R x) - d *\<^sub>R (a - b)"
          using subsetD [OF sb] yT
          by auto
        then have False
          using assms
          apply (simp add: affine_dependent_explicit_finite fs)
          apply (drule_tac x="\<lambda>x. (v x - u x) - (if x = a then -d else if x = b then d else 0)" in spec)
          using ua b d
          apply (auto simp: algebra_simps sum_subtractf sum.distrib)
          done
      } note * = this
      have "y \<notin> rel_interior (convex hull s)"
        using y
        apply (simp add: mem_rel_interior affine_hull_convex_hull)
        apply (auto simp: convex_hull_finite [OF fs])
        apply (drule_tac x=u in spec)
        apply (auto intro: *)
        done
    } with rel_interior_subset show "?lhs \<le> ?rhs"
      by blast
  qed
qed

lemma interior_convex_hull_explicit_minimal:
  fixes s :: "'a::euclidean_space set"
  shows
   "~ affine_dependent s
        ==> interior(convex hull s) =
             (if card(s) \<le> DIM('a) then {}
              else {y. \<exists>u. (\<forall>x \<in> s. 0 < u x) \<and> sum u s = 1 \<and> (\<Sum>x\<in>s. u x *\<^sub>R x) = y})"
  apply (simp add: aff_independent_finite empty_interior_convex_hull, clarify)
  apply (rule trans [of _ "rel_interior(convex hull s)"])
  apply (simp add: affine_hull_convex_hull affine_independent_span_gt rel_interior_interior)
  by (simp add: rel_interior_convex_hull_explicit)

lemma interior_convex_hull_explicit:
  fixes s :: "'a::euclidean_space set"
  assumes "~ affine_dependent s"
  shows
   "interior(convex hull s) =
             (if card(s) \<le> DIM('a) then {}
              else {y. \<exists>u. (\<forall>x \<in> s. 0 < u x \<and> u x < 1) \<and> sum u s = 1 \<and> (\<Sum>x\<in>s. u x *\<^sub>R x) = y})"
proof -
  { fix u :: "'a \<Rightarrow> real" and a
    assume "card Basis < card s" and u: "\<And>x. x\<in>s \<Longrightarrow> 0 < u x" "sum u s = 1" and a: "a \<in> s"
    then have cs: "Suc 0 < card s"
      by (metis DIM_positive less_trans_Suc)
    obtain b where b: "b \<in> s" "a \<noteq> b"
    proof (cases "s \<le> {a}")
      case True
      then show thesis
        using cs subset_singletonD by fastforce
    next
      case False
      then show thesis
      by (blast intro: that)
    qed
    have "u a + u b \<le> sum u {a,b}"
      using a b by simp
    also have "... \<le> sum u s"
      apply (rule Groups_Big.sum_mono2)
      using a b u
      apply (auto simp: less_imp_le aff_independent_finite assms)
      done
    finally have "u a < 1"
      using \<open>b \<in> s\<close> u by fastforce
  } note [simp] = this
  show ?thesis
    using assms
    apply (auto simp: interior_convex_hull_explicit_minimal)
    apply (rule_tac x=u in exI)
    apply (auto simp: not_le)
    done
qed

lemma interior_closed_segment_ge2:
  fixes a :: "'a::euclidean_space"
  assumes "2 \<le> DIM('a)"
    shows  "interior(closed_segment a b) = {}"
using assms unfolding segment_convex_hull
proof -
  have "card {a, b} \<le> DIM('a)"
    using assms
    by (simp add: card_insert_if linear not_less_eq_eq numeral_2_eq_2)
  then show "interior (convex hull {a, b}) = {}"
    by (metis empty_interior_convex_hull finite.insertI finite.emptyI)
qed

lemma interior_open_segment:
  fixes a :: "'a::euclidean_space"
  shows  "interior(open_segment a b) =
                 (if 2 \<le> DIM('a) then {} else open_segment a b)"
proof (simp add: not_le, intro conjI impI)
  assume "2 \<le> DIM('a)"
  then show "interior (open_segment a b) = {}"
    apply (simp add: segment_convex_hull open_segment_def)
    apply (metis Diff_subset interior_mono segment_convex_hull subset_empty interior_closed_segment_ge2)
    done
next
  assume le2: "DIM('a) < 2"
  show "interior (open_segment a b) = open_segment a b"
  proof (cases "a = b")
    case True then show ?thesis by auto
  next
    case False
    with le2 have "affine hull (open_segment a b) = UNIV"
      apply simp
      apply (rule affine_independent_span_gt)
      apply (simp_all add: affine_dependent_def insert_Diff_if)
      done
    then show "interior (open_segment a b) = open_segment a b"
      using rel_interior_interior rel_interior_open_segment by blast
  qed
qed

lemma interior_closed_segment:
  fixes a :: "'a::euclidean_space"
  shows "interior(closed_segment a b) =
                 (if 2 \<le> DIM('a) then {} else open_segment a b)"
proof (cases "a = b")
  case True then show ?thesis by simp
next
  case False
  then have "closure (open_segment a b) = closed_segment a b"
    by simp
  then show ?thesis
    by (metis (no_types) convex_interior_closure convex_open_segment interior_open_segment)
qed

lemmas interior_segment = interior_closed_segment interior_open_segment

lemma closed_segment_eq [simp]:
  fixes a :: "'a::euclidean_space"
  shows "closed_segment a b = closed_segment c d \<longleftrightarrow> {a,b} = {c,d}"
proof
  assume abcd: "closed_segment a b = closed_segment c d"
  show "{a,b} = {c,d}"
  proof (cases "a=b \<or> c=d")
    case True with abcd show ?thesis by force
  next
    case False
    then have neq: "a \<noteq> b \<and> c \<noteq> d" by force
    have *: "closed_segment c d - {a, b} = rel_interior (closed_segment c d)"
      using neq abcd by (metis (no_types) open_segment_def rel_interior_closed_segment)
    have "b \<in> {c, d}"
    proof -
      have "insert b (closed_segment c d) = closed_segment c d"
        using abcd by blast
      then show ?thesis
        by (metis DiffD2 Diff_insert2 False * insertI1 insert_Diff_if open_segment_def rel_interior_closed_segment)
    qed
    moreover have "a \<in> {c, d}"
      by (metis Diff_iff False * abcd ends_in_segment(1) insertI1 open_segment_def rel_interior_closed_segment)
    ultimately show "{a, b} = {c, d}"
      using neq by fastforce
  qed
next
  assume "{a,b} = {c,d}"
  then show "closed_segment a b = closed_segment c d"
    by (simp add: segment_convex_hull)
qed

lemma closed_open_segment_eq [simp]:
  fixes a :: "'a::euclidean_space"
  shows "closed_segment a b \<noteq> open_segment c d"
by (metis DiffE closed_segment_neq_empty closure_closed_segment closure_open_segment ends_in_segment(1) insertI1 open_segment_def)

lemma open_closed_segment_eq [simp]:
  fixes a :: "'a::euclidean_space"
  shows "open_segment a b \<noteq> closed_segment c d"
using closed_open_segment_eq by blast

lemma open_segment_eq [simp]:
  fixes a :: "'a::euclidean_space"
  shows "open_segment a b = open_segment c d \<longleftrightarrow> a = b \<and> c = d \<or> {a,b} = {c,d}"
        (is "?lhs = ?rhs")
proof
  assume abcd: ?lhs
  show ?rhs
  proof (cases "a=b \<or> c=d")
    case True with abcd show ?thesis
      using finite_open_segment by fastforce
  next
    case False
    then have a2: "a \<noteq> b \<and> c \<noteq> d" by force
    with abcd show ?rhs
      unfolding open_segment_def
      by (metis (no_types) abcd closed_segment_eq closure_open_segment)
  qed
next
  assume ?rhs
  then show ?lhs
    by (metis Diff_cancel convex_hull_singleton insert_absorb2 open_segment_def segment_convex_hull)
qed

subsection\<open>Similar results for closure and (relative or absolute) frontier.\<close>

lemma closure_convex_hull [simp]:
  fixes s :: "'a::euclidean_space set"
  shows "compact s ==> closure(convex hull s) = convex hull s"
  by (simp add: compact_imp_closed compact_convex_hull)

lemma rel_frontier_convex_hull_explicit:
  fixes s :: "'a::euclidean_space set"
  assumes "~ affine_dependent s"
  shows "rel_frontier(convex hull s) =
         {y. \<exists>u. (\<forall>x \<in> s. 0 \<le> u x) \<and> (\<exists>x \<in> s. u x = 0) \<and> sum u s = 1 \<and> sum (\<lambda>x. u x *\<^sub>R x) s = y}"
proof -
  have fs: "finite s"
    using assms by (simp add: aff_independent_finite)
  show ?thesis
    apply (simp add: rel_frontier_def finite_imp_compact rel_interior_convex_hull_explicit assms fs)
    apply (auto simp: convex_hull_finite fs)
    apply (drule_tac x=u in spec)
    apply (rule_tac x=u in exI)
    apply force
    apply (rename_tac v)
    apply (rule notE [OF assms])
    apply (simp add: affine_dependent_explicit)
    apply (rule_tac x=s in exI)
    apply (auto simp: fs)
    apply (rule_tac x = "\<lambda>x. u x - v x" in exI)
    apply (force simp: sum_subtractf scaleR_diff_left)
    done
qed

lemma frontier_convex_hull_explicit:
  fixes s :: "'a::euclidean_space set"
  assumes "~ affine_dependent s"
  shows "frontier(convex hull s) =
         {y. \<exists>u. (\<forall>x \<in> s. 0 \<le> u x) \<and> (DIM ('a) < card s \<longrightarrow> (\<exists>x \<in> s. u x = 0)) \<and>
             sum u s = 1 \<and> sum (\<lambda>x. u x *\<^sub>R x) s = y}"
proof -
  have fs: "finite s"
    using assms by (simp add: aff_independent_finite)
  show ?thesis
  proof (cases "DIM ('a) < card s")
    case True
    with assms fs show ?thesis
      by (simp add: rel_frontier_def frontier_def rel_frontier_convex_hull_explicit [symmetric]
                    interior_convex_hull_explicit_minimal rel_interior_convex_hull_explicit)
  next
    case False
    then have "card s \<le> DIM ('a)"
      by linarith
    then show ?thesis
      using assms fs
      apply (simp add: frontier_def interior_convex_hull_explicit finite_imp_compact)
      apply (simp add: convex_hull_finite)
      done
  qed
qed

lemma rel_frontier_convex_hull_cases:
  fixes s :: "'a::euclidean_space set"
  assumes "~ affine_dependent s"
  shows "rel_frontier(convex hull s) = \<Union>{convex hull (s - {x}) |x. x \<in> s}"
proof -
  have fs: "finite s"
    using assms by (simp add: aff_independent_finite)
  { fix u a
  have "\<forall>x\<in>s. 0 \<le> u x \<Longrightarrow> a \<in> s \<Longrightarrow> u a = 0 \<Longrightarrow> sum u s = 1 \<Longrightarrow>
            \<exists>x v. x \<in> s \<and>
                  (\<forall>x\<in>s - {x}. 0 \<le> v x) \<and>
                      sum v (s - {x}) = 1 \<and> (\<Sum>x\<in>s - {x}. v x *\<^sub>R x) = (\<Sum>x\<in>s. u x *\<^sub>R x)"
    apply (rule_tac x=a in exI)
    apply (rule_tac x=u in exI)
    apply (simp add: Groups_Big.sum_diff1 fs)
    done }
  moreover
  { fix a u
    have "a \<in> s \<Longrightarrow> \<forall>x\<in>s - {a}. 0 \<le> u x \<Longrightarrow> sum u (s - {a}) = 1 \<Longrightarrow>
            \<exists>v. (\<forall>x\<in>s. 0 \<le> v x) \<and>
                 (\<exists>x\<in>s. v x = 0) \<and> sum v s = 1 \<and> (\<Sum>x\<in>s. v x *\<^sub>R x) = (\<Sum>x\<in>s - {a}. u x *\<^sub>R x)"
    apply (rule_tac x="\<lambda>x. if x = a then 0 else u x" in exI)
    apply (auto simp: sum.If_cases Diff_eq if_smult fs)
    done }
  ultimately show ?thesis
    using assms
    apply (simp add: rel_frontier_convex_hull_explicit)
    apply (simp add: convex_hull_finite fs Union_SetCompr_eq, auto)
    done
qed

lemma frontier_convex_hull_eq_rel_frontier:
  fixes s :: "'a::euclidean_space set"
  assumes "~ affine_dependent s"
  shows "frontier(convex hull s) =
           (if card s \<le> DIM ('a) then convex hull s else rel_frontier(convex hull s))"
  using assms
  unfolding rel_frontier_def frontier_def
  by (simp add: affine_independent_span_gt rel_interior_interior
                finite_imp_compact empty_interior_convex_hull aff_independent_finite)

lemma frontier_convex_hull_cases:
  fixes s :: "'a::euclidean_space set"
  assumes "~ affine_dependent s"
  shows "frontier(convex hull s) =
           (if card s \<le> DIM ('a) then convex hull s else \<Union>{convex hull (s - {x}) |x. x \<in> s})"
by (simp add: assms frontier_convex_hull_eq_rel_frontier rel_frontier_convex_hull_cases)

lemma in_frontier_convex_hull:
  fixes s :: "'a::euclidean_space set"
  assumes "finite s" "card s \<le> Suc (DIM ('a))" "x \<in> s"
  shows   "x \<in> frontier(convex hull s)"
proof (cases "affine_dependent s")
  case True
  with assms show ?thesis
    apply (auto simp: affine_dependent_def frontier_def finite_imp_compact hull_inc)
    by (metis card.insert_remove convex_hull_subset_affine_hull empty_interior_affine_hull finite_Diff hull_redundant insert_Diff insert_Diff_single insert_not_empty interior_mono not_less_eq_eq subset_empty)
next
  case False
  { assume "card s = Suc (card Basis)"
    then have cs: "Suc 0 < card s"
      by (simp add: DIM_positive)
    with subset_singletonD have "\<exists>y \<in> s. y \<noteq> x"
      by (cases "s \<le> {x}") fastforce+
  } note [dest!] = this
  show ?thesis using assms
    unfolding frontier_convex_hull_cases [OF False] Union_SetCompr_eq
    by (auto simp: le_Suc_eq hull_inc)
qed

lemma not_in_interior_convex_hull:
  fixes s :: "'a::euclidean_space set"
  assumes "finite s" "card s \<le> Suc (DIM ('a))" "x \<in> s"
  shows   "x \<notin> interior(convex hull s)"
using in_frontier_convex_hull [OF assms]
by (metis Diff_iff frontier_def)

lemma interior_convex_hull_eq_empty:
  fixes s :: "'a::euclidean_space set"
  assumes "card s = Suc (DIM ('a))"
  shows   "interior(convex hull s) = {} \<longleftrightarrow> affine_dependent s"
proof -
  { fix a b
    assume ab: "a \<in> interior (convex hull s)" "b \<in> s" "b \<in> affine hull (s - {b})"
    then have "interior(affine hull s) = {}" using assms
      by (metis DIM_positive One_nat_def Suc_mono card.remove card_infinite empty_interior_affine_hull eq_iff hull_redundant insert_Diff not_less zero_le_one)
    then have False using ab
      by (metis convex_hull_subset_affine_hull equals0D interior_mono subset_eq)
  } then
  show ?thesis
    using assms
    apply auto
    apply (metis UNIV_I affine_hull_convex_hull affine_hull_empty affine_independent_span_eq convex_convex_hull empty_iff rel_interior_interior rel_interior_same_affine_hull)
    apply (auto simp: affine_dependent_def)
    done
qed


subsection \<open>Coplanarity, and collinearity in terms of affine hull\<close>

definition coplanar  where
   "coplanar s \<equiv> \<exists>u v w. s \<subseteq> affine hull {u,v,w}"

lemma collinear_affine_hull:
  "collinear s \<longleftrightarrow> (\<exists>u v. s \<subseteq> affine hull {u,v})"
proof (cases "s={}")
  case True then show ?thesis
    by simp
next
  case False
  then obtain x where x: "x \<in> s" by auto
  { fix u
    assume *: "\<And>x y. \<lbrakk>x\<in>s; y\<in>s\<rbrakk> \<Longrightarrow> \<exists>c. x - y = c *\<^sub>R u"
    have "\<exists>u v. s \<subseteq> {a *\<^sub>R u + b *\<^sub>R v |a b. a + b = 1}"
      apply (rule_tac x=x in exI)
      apply (rule_tac x="x+u" in exI, clarify)
      apply (erule exE [OF * [OF x]])
      apply (rename_tac c)
      apply (rule_tac x="1+c" in exI)
      apply (rule_tac x="-c" in exI)
      apply (simp add: algebra_simps)
      done
  } moreover
  { fix u v x y
    assume *: "s \<subseteq> {a *\<^sub>R u + b *\<^sub>R v |a b. a + b = 1}"
    have "x\<in>s \<Longrightarrow> y\<in>s \<Longrightarrow> \<exists>c. x - y = c *\<^sub>R (v-u)"
      apply (drule subsetD [OF *])+
      apply simp
      apply clarify
      apply (rename_tac r1 r2)
      apply (rule_tac x="r1-r2" in exI)
      apply (simp add: algebra_simps)
      apply (metis scaleR_left.add)
      done
  } ultimately
  show ?thesis
  unfolding collinear_def affine_hull_2
    by blast
qed

lemma collinear_closed_segment [simp]: "collinear (closed_segment a b)"
by (metis affine_hull_convex_hull collinear_affine_hull hull_subset segment_convex_hull)

lemma collinear_open_segment [simp]: "collinear (open_segment a b)"
  unfolding open_segment_def
  by (metis convex_hull_subset_affine_hull segment_convex_hull dual_order.trans
    convex_hull_subset_affine_hull Diff_subset collinear_affine_hull)

lemma collinear_between_cases:
  fixes c :: "'a::euclidean_space"
  shows "collinear {a,b,c} \<longleftrightarrow> between (b,c) a \<or> between (c,a) b \<or> between (a,b) c"
         (is "?lhs = ?rhs")
proof
  assume ?lhs
  then obtain u v where uv: "\<And>x. x \<in> {a, b, c} \<Longrightarrow> \<exists>c. x = u + c *\<^sub>R v"
    by (auto simp: collinear_alt)
  show ?rhs
    using uv [of a] uv [of b] uv [of c] by (auto simp: between_1)
next
  assume ?rhs
  then show ?lhs
    unfolding between_mem_convex_hull
    by (metis (no_types, hide_lams) collinear_closed_segment collinear_subset hull_redundant hull_subset insert_commute segment_convex_hull)
qed


lemma subset_continuous_image_segment_1:
  fixes f :: "'a::euclidean_space \<Rightarrow> real"
  assumes "continuous_on (closed_segment a b) f"
  shows "closed_segment (f a) (f b) \<subseteq> image f (closed_segment a b)"
by (metis connected_segment convex_contains_segment ends_in_segment imageI
           is_interval_connected_1 is_interval_convex connected_continuous_image [OF assms])

lemma continuous_injective_image_segment_1:
  fixes f :: "'a::euclidean_space \<Rightarrow> real"
  assumes contf: "continuous_on (closed_segment a b) f"
      and injf: "inj_on f (closed_segment a b)"
  shows "f ` (closed_segment a b) = closed_segment (f a) (f b)"
proof
  show "closed_segment (f a) (f b) \<subseteq> f ` closed_segment a b"
    by (metis subset_continuous_image_segment_1 contf)
  show "f ` closed_segment a b \<subseteq> closed_segment (f a) (f b)"
  proof (cases "a = b")
    case True
    then show ?thesis by auto
  next
    case False
    then have fnot: "f a \<noteq> f b"
      using inj_onD injf by fastforce
    moreover
    have "f a \<notin> open_segment (f c) (f b)" if c: "c \<in> closed_segment a b" for c
    proof (clarsimp simp add: open_segment_def)
      assume fa: "f a \<in> closed_segment (f c) (f b)"
      moreover have "closed_segment (f c) (f b) \<subseteq> f ` closed_segment c b"
        by (meson closed_segment_subset contf continuous_on_subset convex_closed_segment ends_in_segment(2) subset_continuous_image_segment_1 that)
      ultimately have "f a \<in> f ` closed_segment c b"
        by blast
      then have a: "a \<in> closed_segment c b"
        by (meson ends_in_segment inj_on_image_mem_iff_alt injf subset_closed_segment that)
      have cb: "closed_segment c b \<subseteq> closed_segment a b"
        by (simp add: closed_segment_subset that)
      show "f a = f c"
      proof (rule between_antisym)
        show "between (f c, f b) (f a)"
          by (simp add: between_mem_segment fa)
        show "between (f a, f b) (f c)"
          by (metis a cb between_antisym between_mem_segment between_triv1 subset_iff)
      qed
    qed
    moreover
    have "f b \<notin> open_segment (f a) (f c)" if c: "c \<in> closed_segment a b" for c
    proof (clarsimp simp add: open_segment_def fnot eq_commute)
      assume fb: "f b \<in> closed_segment (f a) (f c)"
      moreover have "closed_segment (f a) (f c) \<subseteq> f ` closed_segment a c"
        by (meson contf continuous_on_subset ends_in_segment(1) subset_closed_segment subset_continuous_image_segment_1 that)
      ultimately have "f b \<in> f ` closed_segment a c"
        by blast
      then have b: "b \<in> closed_segment a c"
        by (meson ends_in_segment inj_on_image_mem_iff_alt injf subset_closed_segment that)
      have ca: "closed_segment a c \<subseteq> closed_segment a b"
        by (simp add: closed_segment_subset that)
      show "f b = f c"
      proof (rule between_antisym)
        show "between (f c, f a) (f b)"
          by (simp add: between_commute between_mem_segment fb)
        show "between (f b, f a) (f c)"
          by (metis b between_antisym between_commute between_mem_segment between_triv2 that)
      qed
    qed
    ultimately show ?thesis
      by (force simp: closed_segment_eq_real_ivl open_segment_eq_real_ivl split: if_split_asm)
  qed
qed

lemma continuous_injective_image_open_segment_1:
  fixes f :: "'a::euclidean_space \<Rightarrow> real"
  assumes contf: "continuous_on (closed_segment a b) f"
      and injf: "inj_on f (closed_segment a b)"
    shows "f ` (open_segment a b) = open_segment (f a) (f b)"
proof -
  have "f ` (open_segment a b) = f ` (closed_segment a b) - {f a, f b}"
    by (metis (no_types, hide_lams) empty_subsetI ends_in_segment image_insert image_is_empty inj_on_image_set_diff injf insert_subset open_segment_def segment_open_subset_closed)
  also have "... = open_segment (f a) (f b)"
    using continuous_injective_image_segment_1 [OF assms]
    by (simp add: open_segment_def inj_on_image_set_diff [OF injf])
  finally show ?thesis .
qed

lemma collinear_imp_coplanar:
  "collinear s ==> coplanar s"
by (metis collinear_affine_hull coplanar_def insert_absorb2)

lemma collinear_small:
  assumes "finite s" "card s \<le> 2"
    shows "collinear s"
proof -
  have "card s = 0 \<or> card s = 1 \<or> card s = 2"
    using assms by linarith
  then show ?thesis using assms
    using card_eq_SucD
    by auto (metis collinear_2 numeral_2_eq_2)
qed

lemma coplanar_small:
  assumes "finite s" "card s \<le> 3"
    shows "coplanar s"
proof -
  have "card s \<le> 2 \<or> card s = Suc (Suc (Suc 0))"
    using assms by linarith
  then show ?thesis using assms
    apply safe
    apply (simp add: collinear_small collinear_imp_coplanar)
    apply (safe dest!: card_eq_SucD)
    apply (auto simp: coplanar_def)
    apply (metis hull_subset insert_subset)
    done
qed

lemma coplanar_empty: "coplanar {}"
  by (simp add: coplanar_small)

lemma coplanar_sing: "coplanar {a}"
  by (simp add: coplanar_small)

lemma coplanar_2: "coplanar {a,b}"
  by (auto simp: card_insert_if coplanar_small)

lemma coplanar_3: "coplanar {a,b,c}"
  by (auto simp: card_insert_if coplanar_small)

lemma collinear_affine_hull_collinear: "collinear(affine hull s) \<longleftrightarrow> collinear s"
  unfolding collinear_affine_hull
  by (metis affine_affine_hull subset_hull hull_hull hull_mono)

lemma coplanar_affine_hull_coplanar: "coplanar(affine hull s) \<longleftrightarrow> coplanar s"
  unfolding coplanar_def
  by (metis affine_affine_hull subset_hull hull_hull hull_mono)

lemma coplanar_linear_image:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::real_normed_vector"
  assumes "coplanar s" "linear f" shows "coplanar(f ` s)"
proof -
  { fix u v w
    assume "s \<subseteq> affine hull {u, v, w}"
    then have "f ` s \<subseteq> f ` (affine hull {u, v, w})"
      by (simp add: image_mono)
    then have "f ` s \<subseteq> affine hull (f ` {u, v, w})"
      by (metis assms(2) linear_conv_bounded_linear affine_hull_linear_image)
  } then
  show ?thesis
    by auto (meson assms(1) coplanar_def)
qed

lemma coplanar_translation_imp: "coplanar s \<Longrightarrow> coplanar ((\<lambda>x. a + x) ` s)"
  unfolding coplanar_def
  apply clarify
  apply (rule_tac x="u+a" in exI)
  apply (rule_tac x="v+a" in exI)
  apply (rule_tac x="w+a" in exI)
  using affine_hull_translation [of a "{u,v,w}" for u v w]
  apply (force simp: add.commute)
  done

lemma coplanar_translation_eq: "coplanar((\<lambda>x. a + x) ` s) \<longleftrightarrow> coplanar s"
    by (metis (no_types) coplanar_translation_imp translation_galois)

lemma coplanar_linear_image_eq:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  assumes "linear f" "inj f" shows "coplanar(f ` s) = coplanar s"
proof
  assume "coplanar s"
  then show "coplanar (f ` s)"
    unfolding coplanar_def
    using affine_hull_linear_image [of f "{u,v,w}" for u v w]  assms
    by (meson coplanar_def coplanar_linear_image)
next
  obtain g where g: "linear g" "g \<circ> f = id"
    using linear_injective_left_inverse [OF assms]
    by blast
  assume "coplanar (f ` s)"
  then obtain u v w where "f ` s \<subseteq> affine hull {u, v, w}"
    by (auto simp: coplanar_def)
  then have "g ` f ` s \<subseteq> g ` (affine hull {u, v, w})"
    by blast
  then have "s \<subseteq> g ` (affine hull {u, v, w})"
    using g by (simp add: Fun.image_comp)
  then show "coplanar s"
    unfolding coplanar_def
    using affine_hull_linear_image [of g "{u,v,w}" for u v w]  \<open>linear g\<close> linear_conv_bounded_linear
    by fastforce
qed
(*The HOL Light proof is simply
    MATCH_ACCEPT_TAC(LINEAR_INVARIANT_RULE COPLANAR_LINEAR_IMAGE));;
*)

lemma coplanar_subset: "\<lbrakk>coplanar t; s \<subseteq> t\<rbrakk> \<Longrightarrow> coplanar s"
  by (meson coplanar_def order_trans)

lemma affine_hull_3_imp_collinear: "c \<in> affine hull {a,b} \<Longrightarrow> collinear {a,b,c}"
  by (metis collinear_2 collinear_affine_hull_collinear hull_redundant insert_commute)

lemma collinear_3_imp_in_affine_hull: "\<lbrakk>collinear {a,b,c}; a \<noteq> b\<rbrakk> \<Longrightarrow> c \<in> affine hull {a,b}"
  unfolding collinear_def
  apply clarify
  apply (frule_tac x=b in bspec, blast, drule_tac x=a in bspec, blast, erule exE)
  apply (drule_tac x=c in bspec, blast, drule_tac x=a in bspec, blast, erule exE)
  apply (rename_tac y x)
  apply (simp add: affine_hull_2)
  apply (rule_tac x="1 - x/y" in exI)
  apply (simp add: algebra_simps)
  done

lemma collinear_3_affine_hull:
  assumes "a \<noteq> b"
    shows "collinear {a,b,c} \<longleftrightarrow> c \<in> affine hull {a,b}"
using affine_hull_3_imp_collinear assms collinear_3_imp_in_affine_hull by blast

lemma collinear_3_eq_affine_dependent:
  "collinear{a,b,c} \<longleftrightarrow> a = b \<or> a = c \<or> b = c \<or> affine_dependent {a,b,c}"
apply (case_tac "a=b", simp)
apply (case_tac "a=c")
apply (simp add: insert_commute)
apply (case_tac "b=c")
apply (simp add: insert_commute)
apply (auto simp: affine_dependent_def collinear_3_affine_hull insert_Diff_if)
apply (metis collinear_3_affine_hull insert_commute)+
done

lemma affine_dependent_imp_collinear_3:
  "affine_dependent {a,b,c} \<Longrightarrow> collinear{a,b,c}"
by (simp add: collinear_3_eq_affine_dependent)

lemma collinear_3: "NO_MATCH 0 x \<Longrightarrow> collinear {x,y,z} \<longleftrightarrow> collinear {0, x-y, z-y}"
  by (auto simp add: collinear_def)

lemma collinear_3_expand:
   "collinear{a,b,c} \<longleftrightarrow> a = c \<or> (\<exists>u. b = u *\<^sub>R a + (1 - u) *\<^sub>R c)"
proof -
  have "collinear{a,b,c} = collinear{a,c,b}"
    by (simp add: insert_commute)
  also have "... = collinear {0, a - c, b - c}"
    by (simp add: collinear_3)
  also have "... \<longleftrightarrow> (a = c \<or> b = c \<or> (\<exists>ca. b - c = ca *\<^sub>R (a - c)))"
    by (simp add: collinear_lemma)
  also have "... \<longleftrightarrow> a = c \<or> (\<exists>u. b = u *\<^sub>R a + (1 - u) *\<^sub>R c)"
    by (cases "a = c \<or> b = c") (auto simp: algebra_simps)
  finally show ?thesis .
qed

lemma collinear_aff_dim: "collinear S \<longleftrightarrow> aff_dim S \<le> 1"
proof
  assume "collinear S"
  then obtain u and v :: "'a" where "aff_dim S \<le> aff_dim {u,v}"
    by (metis \<open>collinear S\<close> aff_dim_affine_hull aff_dim_subset collinear_affine_hull)
  then show "aff_dim S \<le> 1"
    using order_trans by fastforce
next
  assume "aff_dim S \<le> 1"
  then have le1: "aff_dim (affine hull S) \<le> 1"
    by simp
  obtain B where "B \<subseteq> S" and B: "\<not> affine_dependent B" "affine hull S = affine hull B"
    using affine_basis_exists [of S] by auto
  then have "finite B" "card B \<le> 2"
    using B le1 by (auto simp: affine_independent_iff_card)
  then have "collinear B"
    by (rule collinear_small)
  then show "collinear S"
    by (metis \<open>affine hull S = affine hull B\<close> collinear_affine_hull_collinear)
qed

lemma collinear_midpoint: "collinear{a,midpoint a b,b}"
  apply (auto simp: collinear_3 collinear_lemma)
  apply (drule_tac x="-1" in spec)
  apply (simp add: algebra_simps)
  done

lemma midpoint_collinear:
  fixes a b c :: "'a::real_normed_vector"
  assumes "a \<noteq> c"
    shows "b = midpoint a c \<longleftrightarrow> collinear{a,b,c} \<and> dist a b = dist b c"
proof -
  have *: "a - (u *\<^sub>R a + (1 - u) *\<^sub>R c) = (1 - u) *\<^sub>R (a - c)"
          "u *\<^sub>R a + (1 - u) *\<^sub>R c - c = u *\<^sub>R (a - c)"
          "\<bar>1 - u\<bar> = \<bar>u\<bar> \<longleftrightarrow> u = 1/2" for u::real
    by (auto simp: algebra_simps)
  have "b = midpoint a c \<Longrightarrow> collinear{a,b,c} "
    using collinear_midpoint by blast
  moreover have "collinear{a,b,c} \<Longrightarrow> b = midpoint a c \<longleftrightarrow> dist a b = dist b c"
    apply (auto simp: collinear_3_expand assms dist_midpoint)
    apply (simp add: dist_norm * assms midpoint_def del: divide_const_simps)
    apply (simp add: algebra_simps)
    done
  ultimately show ?thesis by blast
qed

lemma between_imp_collinear:
  fixes x :: "'a :: euclidean_space"
  assumes "between (a,b) x"
    shows "collinear {a,x,b}"
proof (cases "x = a \<or> x = b \<or> a = b")
  case True with assms show ?thesis
    by (auto simp: dist_commute)
next
  case False with assms show ?thesis
    apply (auto simp: collinear_3 collinear_lemma between_norm)
    apply (drule_tac x="-(norm(b - x) / norm(x - a))" in spec)
    apply (simp add: vector_add_divide_simps eq_vector_fraction_iff real_vector.scale_minus_right [symmetric])
    done
qed

lemma midpoint_between:
  fixes a b :: "'a::euclidean_space"
  shows "b = midpoint a c \<longleftrightarrow> between (a,c) b \<and> dist a b = dist b c"
proof (cases "a = c")
  case True then show ?thesis
    by (auto simp: dist_commute)
next
  case False
  show ?thesis
    apply (rule iffI)
    apply (simp add: between_midpoint(1) dist_midpoint)
    using False between_imp_collinear midpoint_collinear by blast
qed

lemma collinear_triples:
  assumes "a \<noteq> b"
    shows "collinear(insert a (insert b S)) \<longleftrightarrow> (\<forall>x \<in> S. collinear{a,b,x})"
          (is "?lhs = ?rhs")
proof safe
  fix x
  assume ?lhs and "x \<in> S"
  then show "collinear {a, b, x}"
    using collinear_subset by force
next
  assume ?rhs
  then have "\<forall>x \<in> S. collinear{a,x,b}"
    by (simp add: insert_commute)
  then have *: "\<exists>u. x = u *\<^sub>R a + (1 - u) *\<^sub>R b" if "x \<in> (insert a (insert b S))" for x
    using that assms collinear_3_expand by fastforce+
  show ?lhs
    unfolding collinear_def
    apply (rule_tac x="b-a" in exI)
    apply (clarify dest!: *)
    by (metis (no_types, hide_lams) add.commute diff_add_cancel diff_diff_eq2 real_vector.scale_right_diff_distrib scaleR_left.diff)
qed

lemma collinear_4_3:
  assumes "a \<noteq> b"
    shows "collinear {a,b,c,d} \<longleftrightarrow> collinear{a,b,c} \<and> collinear{a,b,d}"
  using collinear_triples [OF assms, of "{c,d}"] by (force simp:)

lemma collinear_3_trans:
  assumes "collinear{a,b,c}" "collinear{b,c,d}" "b \<noteq> c"
    shows "collinear{a,b,d}"
proof -
  have "collinear{b,c,a,d}"
    by (metis (full_types) assms collinear_4_3 insert_commute)
  then show ?thesis
    by (simp add: collinear_subset)
qed

lemma affine_hull_eq_empty [simp]: "affine hull S = {} \<longleftrightarrow> S = {}"
  using affine_hull_nonempty by blast

lemma affine_hull_2_alt:
  fixes a b :: "'a::real_vector"
  shows "affine hull {a,b} = range (\<lambda>u. a + u *\<^sub>R (b - a))"
apply (simp add: affine_hull_2, safe)
apply (rule_tac x=v in image_eqI)
apply (simp add: algebra_simps)
apply (metis scaleR_add_left scaleR_one, simp)
apply (rule_tac x="1-u" in exI)
apply (simp add: algebra_simps)
done

lemma interior_convex_hull_3_minimal:
  fixes a :: "'a::euclidean_space"
  shows "\<lbrakk>~ collinear{a,b,c}; DIM('a) = 2\<rbrakk>
         \<Longrightarrow> interior(convex hull {a,b,c}) =
                {v. \<exists>x y z. 0 < x \<and> 0 < y \<and> 0 < z \<and> x + y + z = 1 \<and>
                            x *\<^sub>R a + y *\<^sub>R b + z *\<^sub>R c = v}"
apply (simp add: collinear_3_eq_affine_dependent interior_convex_hull_explicit_minimal, safe)
apply (rule_tac x="u a" in exI, simp)
apply (rule_tac x="u b" in exI, simp)
apply (rule_tac x="u c" in exI, simp)
apply (rename_tac uu x y z)
apply (rule_tac x="\<lambda>r. (if r=a then x else if r=b then y else if r=c then z else 0)" in exI)
apply simp
done

subsection\<open>The infimum of the distance between two sets\<close>

definition setdist :: "'a::metric_space set \<Rightarrow> 'a set \<Rightarrow> real" where
  "setdist s t \<equiv>
       (if s = {} \<or> t = {} then 0
        else Inf {dist x y| x y. x \<in> s \<and> y \<in> t})"

lemma setdist_empty1 [simp]: "setdist {} t = 0"
  by (simp add: setdist_def)

lemma setdist_empty2 [simp]: "setdist t {} = 0"
  by (simp add: setdist_def)

lemma setdist_pos_le [simp]: "0 \<le> setdist s t"
  by (auto simp: setdist_def ex_in_conv [symmetric] intro: cInf_greatest)

lemma le_setdistI:
  assumes "s \<noteq> {}" "t \<noteq> {}" "\<And>x y. \<lbrakk>x \<in> s; y \<in> t\<rbrakk> \<Longrightarrow> d \<le> dist x y"
    shows "d \<le> setdist s t"
  using assms
  by (auto simp: setdist_def Set.ex_in_conv [symmetric] intro: cInf_greatest)

lemma setdist_le_dist: "\<lbrakk>x \<in> s; y \<in> t\<rbrakk> \<Longrightarrow> setdist s t \<le> dist x y"
  unfolding setdist_def
  by (auto intro!: bdd_belowI [where m=0] cInf_lower)

lemma le_setdist_iff:
        "d \<le> setdist s t \<longleftrightarrow>
        (\<forall>x \<in> s. \<forall>y \<in> t. d \<le> dist x y) \<and> (s = {} \<or> t = {} \<longrightarrow> d \<le> 0)"
  apply (cases "s = {} \<or> t = {}")
  apply (force simp add: setdist_def)
  apply (intro iffI conjI)
  using setdist_le_dist apply fastforce
  apply (auto simp: intro: le_setdistI)
  done

lemma setdist_ltE:
  assumes "setdist s t < b" "s \<noteq> {}" "t \<noteq> {}"
    obtains x y where "x \<in> s" "y \<in> t" "dist x y < b"
using assms
by (auto simp: not_le [symmetric] le_setdist_iff)

lemma setdist_refl: "setdist s s = 0"
  apply (cases "s = {}")
  apply (force simp add: setdist_def)
  apply (rule antisym [OF _ setdist_pos_le])
  apply (metis all_not_in_conv dist_self setdist_le_dist)
  done

lemma setdist_sym: "setdist s t = setdist t s"
  by (force simp: setdist_def dist_commute intro!: arg_cong [where f=Inf])

lemma setdist_triangle: "setdist s t \<le> setdist s {a} + setdist {a} t"
proof (cases "s = {} \<or> t = {}")
  case True then show ?thesis
    using setdist_pos_le by fastforce
next
  case False
  have "\<And>x. x \<in> s \<Longrightarrow> setdist s t - dist x a \<le> setdist {a} t"
    apply (rule le_setdistI, blast)
    using False apply (fastforce intro: le_setdistI)
    apply (simp add: algebra_simps)
    apply (metis dist_commute dist_triangle3 order_trans [OF setdist_le_dist])
    done
  then have "setdist s t - setdist {a} t \<le> setdist s {a}"
    using False by (fastforce intro: le_setdistI)
  then show ?thesis
    by (simp add: algebra_simps)
qed

lemma setdist_singletons [simp]: "setdist {x} {y} = dist x y"
  by (simp add: setdist_def)

lemma setdist_Lipschitz: "\<bar>setdist {x} s - setdist {y} s\<bar> \<le> dist x y"
  apply (subst setdist_singletons [symmetric])
  by (metis abs_diff_le_iff diff_le_eq setdist_triangle setdist_sym)

lemma continuous_at_setdist [continuous_intros]: "continuous (at x) (\<lambda>y. (setdist {y} s))"
  by (force simp: continuous_at_eps_delta dist_real_def intro: le_less_trans [OF setdist_Lipschitz])

lemma continuous_on_setdist [continuous_intros]: "continuous_on t (\<lambda>y. (setdist {y} s))"
  by (metis continuous_at_setdist continuous_at_imp_continuous_on)

lemma uniformly_continuous_on_setdist: "uniformly_continuous_on t (\<lambda>y. (setdist {y} s))"
  by (force simp: uniformly_continuous_on_def dist_real_def intro: le_less_trans [OF setdist_Lipschitz])

lemma setdist_subset_right: "\<lbrakk>t \<noteq> {}; t \<subseteq> u\<rbrakk> \<Longrightarrow> setdist s u \<le> setdist s t"
  apply (cases "s = {} \<or> u = {}", force)
  apply (auto simp: setdist_def intro!: bdd_belowI [where m=0] cInf_superset_mono)
  done

lemma setdist_subset_left: "\<lbrakk>s \<noteq> {}; s \<subseteq> t\<rbrakk> \<Longrightarrow> setdist t u \<le> setdist s u"
  by (metis setdist_subset_right setdist_sym)

lemma setdist_closure_1 [simp]: "setdist (closure s) t = setdist s t"
proof (cases "s = {} \<or> t = {}")
  case True then show ?thesis by force
next
  case False
  { fix y
    assume "y \<in> t"
    have "continuous_on (closure s) (\<lambda>a. dist a y)"
      by (auto simp: continuous_intros dist_norm)
    then have *: "\<And>x. x \<in> closure s \<Longrightarrow> setdist s t \<le> dist x y"
      apply (rule continuous_ge_on_closure)
      apply assumption
      apply (blast intro: setdist_le_dist \<open>y \<in> t\<close> )
      done
  } note * = this
  show ?thesis
    apply (rule antisym)
     using False closure_subset apply (blast intro: setdist_subset_left)
    using False *
    apply (force simp add: closure_eq_empty intro!: le_setdistI)
    done
qed

lemma setdist_closure_2 [simp]: "setdist t (closure s) = setdist t s"
by (metis setdist_closure_1 setdist_sym)

lemma setdist_compact_closed:
  fixes S :: "'a::euclidean_space set"
  assumes S: "compact S" and T: "closed T"
      and "S \<noteq> {}" "T \<noteq> {}"
    shows "\<exists>x \<in> S. \<exists>y \<in> T. dist x y = setdist S T"
proof -
  have "(\<Union>x\<in> S. \<Union>y \<in> T. {x - y}) \<noteq> {}"
    using assms by blast
  then have "\<exists>x \<in> S. \<exists>y \<in> T. dist x y \<le> setdist S T"
    apply (rule distance_attains_inf [where a=0, OF compact_closed_differences [OF S T]])
    apply (simp add: dist_norm le_setdist_iff)
    apply blast
    done
  then show ?thesis
    by (blast intro!: antisym [OF _ setdist_le_dist] )
qed

lemma setdist_closed_compact:
  fixes S :: "'a::euclidean_space set"
  assumes S: "closed S" and T: "compact T"
      and "S \<noteq> {}" "T \<noteq> {}"
    shows "\<exists>x \<in> S. \<exists>y \<in> T. dist x y = setdist S T"
  using setdist_compact_closed [OF T S \<open>T \<noteq> {}\<close> \<open>S \<noteq> {}\<close>]
  by (metis dist_commute setdist_sym)

lemma setdist_eq_0I: "\<lbrakk>x \<in> S; x \<in> T\<rbrakk> \<Longrightarrow> setdist S T = 0"
  by (metis antisym dist_self setdist_le_dist setdist_pos_le)

lemma setdist_eq_0_compact_closed:
  fixes S :: "'a::euclidean_space set"
  assumes S: "compact S" and T: "closed T"
    shows "setdist S T = 0 \<longleftrightarrow> S = {} \<or> T = {} \<or> S \<inter> T \<noteq> {}"
  apply (cases "S = {} \<or> T = {}", force)
  using setdist_compact_closed [OF S T]
  apply (force intro: setdist_eq_0I )
  done

corollary setdist_gt_0_compact_closed:
  fixes S :: "'a::euclidean_space set"
  assumes S: "compact S" and T: "closed T"
    shows "setdist S T > 0 \<longleftrightarrow> (S \<noteq> {} \<and> T \<noteq> {} \<and> S \<inter> T = {})"
  using setdist_pos_le [of S T] setdist_eq_0_compact_closed [OF assms]
  by linarith

lemma setdist_eq_0_closed_compact:
  fixes S :: "'a::euclidean_space set"
  assumes S: "closed S" and T: "compact T"
    shows "setdist S T = 0 \<longleftrightarrow> S = {} \<or> T = {} \<or> S \<inter> T \<noteq> {}"
  using setdist_eq_0_compact_closed [OF T S]
  by (metis Int_commute setdist_sym)

lemma setdist_eq_0_bounded:
  fixes S :: "'a::euclidean_space set"
  assumes "bounded S \<or> bounded T"
    shows "setdist S T = 0 \<longleftrightarrow> S = {} \<or> T = {} \<or> closure S \<inter> closure T \<noteq> {}"
  apply (cases "S = {} \<or> T = {}", force)
  using setdist_eq_0_compact_closed [of "closure S" "closure T"]
        setdist_eq_0_closed_compact [of "closure S" "closure T"] assms
  apply (force simp add:  bounded_closure compact_eq_bounded_closed)
  done

lemma setdist_unique:
  "\<lbrakk>a \<in> S; b \<in> T; \<And>x y. x \<in> S \<and> y \<in> T ==> dist a b \<le> dist x y\<rbrakk>
   \<Longrightarrow> setdist S T = dist a b"
  by (force simp add: setdist_le_dist le_setdist_iff intro: antisym)

lemma setdist_closest_point:
    "\<lbrakk>closed S; S \<noteq> {}\<rbrakk> \<Longrightarrow> setdist {a} S = dist a (closest_point S a)"
  apply (rule setdist_unique)
  using closest_point_le
  apply (auto simp: closest_point_in_set)
  done

lemma setdist_eq_0_sing_1:
    fixes S :: "'a::euclidean_space set"
    shows "setdist {x} S = 0 \<longleftrightarrow> S = {} \<or> x \<in> closure S"
  by (auto simp: setdist_eq_0_bounded)

lemma setdist_eq_0_sing_2:
    fixes S :: "'a::euclidean_space set"
    shows "setdist S {x} = 0 \<longleftrightarrow> S = {} \<or> x \<in> closure S"
  by (auto simp: setdist_eq_0_bounded)

lemma setdist_neq_0_sing_1:
    fixes S :: "'a::euclidean_space set"
    shows "\<lbrakk>setdist {x} S = a; a \<noteq> 0\<rbrakk> \<Longrightarrow> S \<noteq> {} \<and> x \<notin> closure S"
  by (auto simp: setdist_eq_0_sing_1)

lemma setdist_neq_0_sing_2:
    fixes S :: "'a::euclidean_space set"
    shows "\<lbrakk>setdist S {x} = a; a \<noteq> 0\<rbrakk> \<Longrightarrow> S \<noteq> {} \<and> x \<notin> closure S"
  by (auto simp: setdist_eq_0_sing_2)

lemma setdist_sing_in_set:
    fixes S :: "'a::euclidean_space set"
    shows "x \<in> S \<Longrightarrow> setdist {x} S = 0"
  using closure_subset by (auto simp: setdist_eq_0_sing_1)

lemma setdist_le_sing: "x \<in> S ==> setdist S T \<le> setdist {x} T"
  using setdist_subset_left by auto

lemma setdist_eq_0_closed:
  fixes S :: "'a::euclidean_space set"
  shows  "closed S \<Longrightarrow> (setdist {x} S = 0 \<longleftrightarrow> S = {} \<or> x \<in> S)"
by (simp add: setdist_eq_0_sing_1)

lemma setdist_eq_0_closedin:
  fixes S :: "'a::euclidean_space set"
  shows "\<lbrakk>closedin (subtopology euclidean u) S; x \<in> u\<rbrakk>
         \<Longrightarrow> (setdist {x} S = 0 \<longleftrightarrow> S = {} \<or> x \<in> S)"
  by (auto simp: closedin_limpt setdist_eq_0_sing_1 closure_def)

subsection\<open>Basic lemmas about hyperplanes and halfspaces\<close>

lemma hyperplane_eq_Ex:
  assumes "a \<noteq> 0" obtains x where "a \<bullet> x = b"
  by (rule_tac x = "(b / (a \<bullet> a)) *\<^sub>R a" in that) (simp add: assms)

lemma hyperplane_eq_empty:
     "{x. a \<bullet> x = b} = {} \<longleftrightarrow> a = 0 \<and> b \<noteq> 0"
  using hyperplane_eq_Ex apply auto[1]
  using inner_zero_right by blast

lemma hyperplane_eq_UNIV:
   "{x. a \<bullet> x = b} = UNIV \<longleftrightarrow> a = 0 \<and> b = 0"
proof -
  have "UNIV \<subseteq> {x. a \<bullet> x = b} \<Longrightarrow> a = 0 \<and> b = 0"
    apply (drule_tac c = "((b+1) / (a \<bullet> a)) *\<^sub>R a" in subsetD)
    apply simp_all
    by (metis add_cancel_right_right zero_neq_one)
  then show ?thesis by force
qed

lemma halfspace_eq_empty_lt:
   "{x. a \<bullet> x < b} = {} \<longleftrightarrow> a = 0 \<and> b \<le> 0"
proof -
  have "{x. a \<bullet> x < b} \<subseteq> {} \<Longrightarrow> a = 0 \<and> b \<le> 0"
    apply (rule ccontr)
    apply (drule_tac c = "((b-1) / (a \<bullet> a)) *\<^sub>R a" in subsetD)
    apply force+
    done
  then show ?thesis by force
qed

lemma halfspace_eq_empty_gt:
   "{x. a \<bullet> x > b} = {} \<longleftrightarrow> a = 0 \<and> b \<ge> 0"
using halfspace_eq_empty_lt [of "-a" "-b"]
by simp

lemma halfspace_eq_empty_le:
   "{x. a \<bullet> x \<le> b} = {} \<longleftrightarrow> a = 0 \<and> b < 0"
proof -
  have "{x. a \<bullet> x \<le> b} \<subseteq> {} \<Longrightarrow> a = 0 \<and> b < 0"
    apply (rule ccontr)
    apply (drule_tac c = "((b-1) / (a \<bullet> a)) *\<^sub>R a" in subsetD)
    apply force+
    done
  then show ?thesis by force
qed

lemma halfspace_eq_empty_ge:
   "{x. a \<bullet> x \<ge> b} = {} \<longleftrightarrow> a = 0 \<and> b > 0"
using halfspace_eq_empty_le [of "-a" "-b"]
by simp

subsection\<open>Use set distance for an easy proof of separation properties\<close>

proposition separation_closures:
  fixes S :: "'a::euclidean_space set"
  assumes "S \<inter> closure T = {}" "T \<inter> closure S = {}"
  obtains U V where "U \<inter> V = {}" "open U" "open V" "S \<subseteq> U" "T \<subseteq> V"
proof (cases "S = {} \<or> T = {}")
  case True with that show ?thesis by auto
next
  case False
  define f where "f \<equiv> \<lambda>x. setdist {x} T - setdist {x} S"
  have contf: "continuous_on UNIV f"
    unfolding f_def by (intro continuous_intros continuous_on_setdist)
  show ?thesis
  proof (rule_tac U = "{x. f x > 0}" and V = "{x. f x < 0}" in that)
    show "{x. 0 < f x} \<inter> {x. f x < 0} = {}"
      by auto
    show "open {x. 0 < f x}"
      by (simp add: open_Collect_less contf continuous_on_const)
    show "open {x. f x < 0}"
      by (simp add: open_Collect_less contf continuous_on_const)
    show "S \<subseteq> {x. 0 < f x}"
      apply (clarsimp simp add: f_def setdist_sing_in_set)
      using assms
      by (metis False IntI empty_iff le_less setdist_eq_0_sing_2 setdist_pos_le setdist_sym)
    show "T \<subseteq> {x. f x < 0}"
      apply (clarsimp simp add: f_def setdist_sing_in_set)
      using assms
      by (metis False IntI empty_iff le_less setdist_eq_0_sing_2 setdist_pos_le setdist_sym)
  qed
qed

lemma separation_normal:
  fixes S :: "'a::euclidean_space set"
  assumes "closed S" "closed T" "S \<inter> T = {}"
  obtains U V where "open U" "open V" "S \<subseteq> U" "T \<subseteq> V" "U \<inter> V = {}"
using separation_closures [of S T]
by (metis assms closure_closed disjnt_def inf_commute)


lemma separation_normal_local:
  fixes S :: "'a::euclidean_space set"
  assumes US: "closedin (subtopology euclidean U) S"
      and UT: "closedin (subtopology euclidean U) T"
      and "S \<inter> T = {}"
  obtains S' T' where "openin (subtopology euclidean U) S'"
                      "openin (subtopology euclidean U) T'"
                      "S \<subseteq> S'"  "T \<subseteq> T'"  "S' \<inter> T' = {}"
proof (cases "S = {} \<or> T = {}")
  case True with that show ?thesis
    apply safe
    using UT closedin_subset apply blast
    using US closedin_subset apply blast
    done
next
  case False
  define f where "f \<equiv> \<lambda>x. setdist {x} T - setdist {x} S"
  have contf: "continuous_on U f"
    unfolding f_def by (intro continuous_intros)
  show ?thesis
  proof (rule_tac S' = "{x\<in>U. f x > 0}" and T' = "{x\<in>U. f x < 0}" in that)
    show "{x \<in> U. 0 < f x} \<inter> {x \<in> U. f x < 0} = {}"
      by auto
    have "openin (subtopology euclidean U) {x \<in> U. f x \<in> {0<..}}"
      by (rule continuous_openin_preimage [where T=UNIV]) (simp_all add: contf)
    then show "openin (subtopology euclidean U) {x \<in> U. 0 < f x}" by simp
  next
    have "openin (subtopology euclidean U) {x \<in> U. f x \<in> {..<0}}"
      by (rule continuous_openin_preimage [where T=UNIV]) (simp_all add: contf)
    then show "openin (subtopology euclidean U) {x \<in> U. f x < 0}" by simp
  next
    show "S \<subseteq> {x \<in> U. 0 < f x}"
      apply (clarsimp simp add: f_def setdist_sing_in_set)
      using assms
      by (metis False Int_insert_right closedin_imp_subset empty_not_insert insert_absorb insert_subset linorder_neqE_linordered_idom not_le setdist_eq_0_closedin setdist_pos_le)
    show "T \<subseteq> {x \<in> U. f x < 0}"
      apply (clarsimp simp add: f_def setdist_sing_in_set)
      using assms
      by (metis False closedin_subset disjoint_iff_not_equal insert_absorb insert_subset linorder_neqE_linordered_idom not_less setdist_eq_0_closedin setdist_pos_le topspace_euclidean_subtopology)
  qed
qed

lemma separation_normal_compact:
  fixes S :: "'a::euclidean_space set"
  assumes "compact S" "closed T" "S \<inter> T = {}"
  obtains U V where "open U" "compact(closure U)" "open V" "S \<subseteq> U" "T \<subseteq> V" "U \<inter> V = {}"
proof -
  have "closed S" "bounded S"
    using assms by (auto simp: compact_eq_bounded_closed)
  then obtain r where "r>0" and r: "S \<subseteq> ball 0 r"
    by (auto dest!: bounded_subset_ballD)
  have **: "closed (T \<union> - ball 0 r)" "S \<inter> (T \<union> - ball 0 r) = {}"
    using assms r by blast+
  then show ?thesis
    apply (rule separation_normal [OF \<open>closed S\<close>])
    apply (rule_tac U=U and V=V in that)
    by auto (meson bounded_ball bounded_subset compl_le_swap2 disjoint_eq_subset_Compl)
qed

subsection\<open>Proper maps, including projections out of compact sets\<close>

lemma finite_indexed_bound:
  assumes A: "finite A" "\<And>x. x \<in> A \<Longrightarrow> \<exists>n::'a::linorder. P x n"
    shows "\<exists>m. \<forall>x \<in> A. \<exists>k\<le>m. P x k"
using A
proof (induction A)
  case empty then show ?case by force
next
  case (insert a A)
    then obtain m n where "\<forall>x \<in> A. \<exists>k\<le>m. P x k" "P a n"
      by force
    then show ?case
      apply (rule_tac x="max m n" in exI, safe)
      using max.cobounded2 apply blast
      by (meson le_max_iff_disj)
qed

proposition proper_map:
  fixes f :: "'a::heine_borel \<Rightarrow> 'b::heine_borel"
  assumes "closedin (subtopology euclidean S) K"
      and com: "\<And>U. \<lbrakk>U \<subseteq> T; compact U\<rbrakk> \<Longrightarrow> compact {x \<in> S. f x \<in> U}"
      and "f ` S \<subseteq> T"
    shows "closedin (subtopology euclidean T) (f ` K)"
proof -
  have "K \<subseteq> S"
    using assms closedin_imp_subset by metis
  obtain C where "closed C" and Keq: "K = S \<inter> C"
    using assms by (auto simp: closedin_closed)
  have *: "y \<in> f ` K" if "y \<in> T" and y: "y islimpt f ` K" for y
  proof -
    obtain h where "\<forall>n. (\<exists>x\<in>K. h n = f x) \<and> h n \<noteq> y" "inj h" and hlim: "(h \<longlongrightarrow> y) sequentially"
      using \<open>y \<in> T\<close> y by (force simp: limpt_sequential_inj)
    then obtain X where X: "\<And>n. X n \<in> K \<and> h n = f (X n) \<and> h n \<noteq> y"
      by metis
    then have fX: "\<And>n. f (X n) = h n"
      by metis
    have "compact (C \<inter> {a \<in> S. f a \<in> insert y (range (\<lambda>i. f(X(n + i))))})" for n
      apply (rule closed_Int_compact [OF \<open>closed C\<close>])
      apply (rule com)
       using X \<open>K \<subseteq> S\<close> \<open>f ` S \<subseteq> T\<close> \<open>y \<in> T\<close> apply blast
      apply (rule compact_sequence_with_limit)
      apply (simp add: fX add.commute [of n] LIMSEQ_ignore_initial_segment [OF hlim])
      done
    then have comf: "compact {a \<in> K. f a \<in> insert y (range (\<lambda>i. f(X(n + i))))}" for n
      by (simp add: Keq Int_def conj_commute)
    have ne: "\<Inter>\<F> \<noteq> {}"
             if "finite \<F>"
                and \<F>: "\<And>t. t \<in> \<F> \<Longrightarrow>
                           (\<exists>n. t = {a \<in> K. f a \<in> insert y (range (\<lambda>i. f (X (n + i))))})"
             for \<F>
    proof -
      obtain m where m: "\<And>t. t \<in> \<F> \<Longrightarrow> \<exists>k\<le>m. t = {a \<in> K. f a \<in> insert y (range (\<lambda>i. f (X (k + i))))}"
        apply (rule exE)
        apply (rule finite_indexed_bound [OF \<open>finite \<F>\<close> \<F>], assumption, force)
        done
      have "X m \<in> \<Inter>\<F>"
        using X le_Suc_ex by (fastforce dest: m)
      then show ?thesis by blast
    qed
    have "\<Inter>{{a. a \<in> K \<and> f a \<in> insert y (range (\<lambda>i. f(X(n + i))))} |n. n \<in> UNIV}
               \<noteq> {}"
      apply (rule compact_fip_heine_borel)
       using comf apply force
      using ne  apply (simp add: subset_iff del: insert_iff)
      done
    then have "\<exists>x. x \<in> (\<Inter>n. {a \<in> K. f a \<in> insert y (range (\<lambda>i. f (X (n + i))))})"
      by blast
    then show ?thesis
      apply (simp add: image_iff fX)
      by (metis \<open>inj h\<close> le_add1 not_less_eq_eq rangeI range_ex1_eq)
  qed
  with assms closedin_subset show ?thesis
    by (force simp: closedin_limpt)
qed


lemma compact_continuous_image_eq:
  fixes f :: "'a::heine_borel \<Rightarrow> 'b::heine_borel"
  assumes f: "inj_on f S"
  shows "continuous_on S f \<longleftrightarrow> (\<forall>T. compact T \<and> T \<subseteq> S \<longrightarrow> compact(f ` T))"
           (is "?lhs = ?rhs")
proof
  assume ?lhs then show ?rhs
    by (metis continuous_on_subset compact_continuous_image)
next
  assume RHS: ?rhs
  obtain g where gf: "\<And>x. x \<in> S \<Longrightarrow> g (f x) = x"
    by (metis inv_into_f_f f)
  then have *: "{x \<in> S. f x \<in> U} = g ` U" if "U \<subseteq> f ` S" for U
    using that by fastforce
  have gfim: "g ` f ` S \<subseteq> S" using gf by auto
  have **: "compact {x \<in> f ` S. g x \<in> C}" if C: "C \<subseteq> S" "compact C" for C
  proof -
    obtain h :: "'a set \<Rightarrow> 'a" where "h C \<in> C \<and> h C \<notin> S \<or> compact (f ` C)"
      by (force simp: C RHS)
    moreover have "f ` C = {b \<in> f ` S. g b \<in> C}"
      using C gf by auto
    ultimately show "compact {b \<in> f ` S. g b \<in> C}"
      using C by auto
  qed
  show ?lhs
    using proper_map [OF _ _ gfim] **
    by (simp add: continuous_on_closed * closedin_imp_subset)
qed

subsection\<open>Trivial fact: convexity equals connectedness for collinear sets\<close>

lemma convex_connected_collinear:
  fixes S :: "'a::euclidean_space set"
  assumes "collinear S"
    shows "convex S \<longleftrightarrow> connected S"
proof
  assume "convex S"
  then show "connected S"
    using convex_connected by blast
next
  assume S: "connected S"
  show "convex S"
  proof (cases "S = {}")
    case True
    then show ?thesis by simp
  next
    case False
    then obtain a where "a \<in> S" by auto
    have "collinear (affine hull S)"
      by (simp add: assms collinear_affine_hull_collinear)
    then obtain z where "z \<noteq> 0" "\<And>x. x \<in> affine hull S \<Longrightarrow> \<exists>c. x - a = c *\<^sub>R z"
      by (meson \<open>a \<in> S\<close> collinear hull_inc)
    then obtain f where f: "\<And>x. x \<in> affine hull S \<Longrightarrow> x - a = f x *\<^sub>R z"
      by metis
    then have inj_f: "inj_on f (affine hull S)"
      by (metis diff_add_cancel inj_onI)
    have diff: "x - y = (f x - f y) *\<^sub>R z" if x: "x \<in> affine hull S" and y: "y \<in> affine hull S" for x y
    proof -
      have "f x *\<^sub>R z = x - a"
        by (simp add: f hull_inc x)
      moreover have "f y *\<^sub>R z = y - a"
        by (simp add: f hull_inc y)
      ultimately show ?thesis
        by (simp add: scaleR_left.diff)
    qed
    have cont_f: "continuous_on (affine hull S) f"
      apply (clarsimp simp: dist_norm continuous_on_iff diff)
      by (metis \<open>z \<noteq> 0\<close> mult.commute mult_less_cancel_left_pos norm_minus_commute real_norm_def zero_less_mult_iff zero_less_norm_iff)
    then have conn_fS: "connected (f ` S)"
      by (meson S connected_continuous_image continuous_on_subset hull_subset)
    show ?thesis
    proof (clarsimp simp: convex_contains_segment)
      fix x y z
      assume "x \<in> S" "y \<in> S" "z \<in> closed_segment x y"
      have False if "z \<notin> S"
      proof -
        have "f ` (closed_segment x y) = closed_segment (f x) (f y)"
          apply (rule continuous_injective_image_segment_1)
          apply (meson \<open>x \<in> S\<close> \<open>y \<in> S\<close> convex_affine_hull convex_contains_segment hull_inc continuous_on_subset [OF cont_f])
          by (meson \<open>x \<in> S\<close> \<open>y \<in> S\<close> convex_affine_hull convex_contains_segment hull_inc inj_on_subset [OF inj_f])
        then have fz: "f z \<in> closed_segment (f x) (f y)"
          using \<open>z \<in> closed_segment x y\<close> by blast
        have "z \<in> affine hull S"
          by (meson \<open>x \<in> S\<close> \<open>y \<in> S\<close> \<open>z \<in> closed_segment x y\<close> convex_affine_hull convex_contains_segment hull_inc subset_eq)
        then have fz_notin: "f z \<notin> f ` S"
          using hull_subset inj_f inj_onD that by fastforce
        moreover have "{..<f z} \<inter> f ` S \<noteq> {}" "{f z<..} \<inter> f ` S \<noteq> {}"
        proof -
          have "{..<f z} \<inter> f ` {x,y} \<noteq> {}"  "{f z<..} \<inter> f ` {x,y} \<noteq> {}"
            using fz fz_notin \<open>x \<in> S\<close> \<open>y \<in> S\<close>
             apply (auto simp: closed_segment_eq_real_ivl split: if_split_asm)
             apply (metis image_eqI less_eq_real_def)+
            done
          then show "{..<f z} \<inter> f ` S \<noteq> {}" "{f z<..} \<inter> f ` S \<noteq> {}"
            using \<open>x \<in> S\<close> \<open>y \<in> S\<close> by blast+
        qed
        ultimately show False
          using connectedD [OF conn_fS, of "{..<f z}" "{f z<..}"] by force
      qed
      then show "z \<in> S" by meson
    qed
  qed
qed

lemma compact_convex_collinear_segment_alt:
  fixes S :: "'a::euclidean_space set"
  assumes "S \<noteq> {}" "compact S" "connected S" "collinear S"
  obtains a b where "S = closed_segment a b"
proof -
  obtain \<xi> where "\<xi> \<in> S" using \<open>S \<noteq> {}\<close> by auto
  have "collinear (affine hull S)"
    by (simp add: assms collinear_affine_hull_collinear)
  then obtain z where "z \<noteq> 0" "\<And>x. x \<in> affine hull S \<Longrightarrow> \<exists>c. x - \<xi> = c *\<^sub>R z"
    by (meson \<open>\<xi> \<in> S\<close> collinear hull_inc)
  then obtain f where f: "\<And>x. x \<in> affine hull S \<Longrightarrow> x - \<xi> = f x *\<^sub>R z"
    by metis
  let ?g = "\<lambda>r. r *\<^sub>R z + \<xi>"
  have gf: "?g (f x) = x" if "x \<in> affine hull S" for x
    by (metis diff_add_cancel f that)
  then have inj_f: "inj_on f (affine hull S)"
    by (metis inj_onI)
  have diff: "x - y = (f x - f y) *\<^sub>R z" if x: "x \<in> affine hull S" and y: "y \<in> affine hull S" for x y
  proof -
    have "f x *\<^sub>R z = x - \<xi>"
      by (simp add: f hull_inc x)
    moreover have "f y *\<^sub>R z = y - \<xi>"
      by (simp add: f hull_inc y)
    ultimately show ?thesis
      by (simp add: scaleR_left.diff)
  qed
  have cont_f: "continuous_on (affine hull S) f"
    apply (clarsimp simp: dist_norm continuous_on_iff diff)
    by (metis \<open>z \<noteq> 0\<close> mult.commute mult_less_cancel_left_pos norm_minus_commute real_norm_def zero_less_mult_iff zero_less_norm_iff)
  then have "connected (f ` S)"
    by (meson \<open>connected S\<close> connected_continuous_image continuous_on_subset hull_subset)
  moreover have "compact (f ` S)"
    by (meson \<open>compact S\<close> compact_continuous_image_eq cont_f hull_subset inj_f)
  ultimately obtain x y where "f ` S = {x..y}"
    by (meson connected_compact_interval_1)
  then have fS_eq: "f ` S = closed_segment x y"
    using \<open>S \<noteq> {}\<close> closed_segment_eq_real_ivl by auto
  obtain a b where "a \<in> S" "f a = x" "b \<in> S" "f b = y"
    by (metis (full_types) ends_in_segment fS_eq imageE)
  have "f ` (closed_segment a b) = closed_segment (f a) (f b)"
    apply (rule continuous_injective_image_segment_1)
     apply (meson \<open>a \<in> S\<close> \<open>b \<in> S\<close> convex_affine_hull convex_contains_segment hull_inc continuous_on_subset [OF cont_f])
    by (meson \<open>a \<in> S\<close> \<open>b \<in> S\<close> convex_affine_hull convex_contains_segment hull_inc inj_on_subset [OF inj_f])
  then have "f ` (closed_segment a b) = f ` S"
    by (simp add: \<open>f a = x\<close> \<open>f b = y\<close> fS_eq)
  then have "?g ` f ` (closed_segment a b) = ?g ` f ` S"
    by simp
  moreover have "(\<lambda>x. f x *\<^sub>R z + \<xi>) ` closed_segment a b = closed_segment a b"
    apply safe
     apply (metis (mono_tags, hide_lams) \<open>a \<in> S\<close> \<open>b \<in> S\<close> convex_affine_hull convex_contains_segment gf hull_inc subsetCE)
    by (metis (mono_tags, lifting) \<open>a \<in> S\<close> \<open>b \<in> S\<close> convex_affine_hull convex_contains_segment gf hull_subset image_iff subsetCE)
  ultimately have "closed_segment a b = S"
    using gf by (simp add: image_comp o_def hull_inc cong: image_cong)
  then show ?thesis
    using that by blast
qed

lemma compact_convex_collinear_segment:
  fixes S :: "'a::euclidean_space set"
  assumes "S \<noteq> {}" "compact S" "convex S" "collinear S"
  obtains a b where "S = closed_segment a b"
  using assms convex_connected_collinear compact_convex_collinear_segment_alt by blast


lemma proper_map_from_compact:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  assumes contf: "continuous_on S f" and imf: "f ` S \<subseteq> T" and "compact S"
          "closedin (subtopology euclidean T) K"
  shows "compact {x. x \<in> S \<and> f x \<in> K}"
by (rule closedin_compact [OF \<open>compact S\<close>] continuous_closedin_preimage_gen assms)+

lemma proper_map_fst:
  assumes "compact T" "K \<subseteq> S" "compact K"
    shows "compact {z \<in> S \<times> T. fst z \<in> K}"
proof -
  have "{z \<in> S \<times> T. fst z \<in> K} = K \<times> T"
    using assms by auto
  then show ?thesis by (simp add: assms compact_Times)
qed

lemma closed_map_fst:
  fixes S :: "'a::euclidean_space set" and T :: "'b::euclidean_space set"
  assumes "compact T" "closedin (subtopology euclidean (S \<times> T)) c"
   shows "closedin (subtopology euclidean S) (fst ` c)"
proof -
  have *: "fst ` (S \<times> T) \<subseteq> S"
    by auto
  show ?thesis
    using proper_map [OF _ _ *] by (simp add: proper_map_fst assms)
qed

lemma proper_map_snd:
  assumes "compact S" "K \<subseteq> T" "compact K"
    shows "compact {z \<in> S \<times> T. snd z \<in> K}"
proof -
  have "{z \<in> S \<times> T. snd z \<in> K} = S \<times> K"
    using assms by auto
  then show ?thesis by (simp add: assms compact_Times)
qed

lemma closed_map_snd:
  fixes S :: "'a::euclidean_space set" and T :: "'b::euclidean_space set"
  assumes "compact S" "closedin (subtopology euclidean (S \<times> T)) c"
   shows "closedin (subtopology euclidean T) (snd ` c)"
proof -
  have *: "snd ` (S \<times> T) \<subseteq> T"
    by auto
  show ?thesis
    using proper_map [OF _ _ *] by (simp add: proper_map_snd assms)
qed

lemma closedin_compact_projection:
  fixes S :: "'a::euclidean_space set" and T :: "'b::euclidean_space set"
  assumes "compact S" and clo: "closedin (subtopology euclidean (S \<times> T)) U"
    shows "closedin (subtopology euclidean T) {y. \<exists>x. x \<in> S \<and> (x, y) \<in> U}"
proof -
  have "U \<subseteq> S \<times> T"
    by (metis clo closedin_imp_subset)
  then have "{y. \<exists>x. x \<in> S \<and> (x, y) \<in> U} = snd ` U"
    by force
  moreover have "closedin (subtopology euclidean T) (snd ` U)"
    by (rule closed_map_snd [OF assms])
  ultimately show ?thesis
    by simp
qed


lemma closed_compact_projection:
  fixes S :: "'a::euclidean_space set"
    and T :: "('a * 'b::euclidean_space) set"
  assumes "compact S" and clo: "closed T"
    shows "closed {y. \<exists>x. x \<in> S \<and> (x, y) \<in> T}"
proof -
  have *: "{y. \<exists>x. x \<in> S \<and> Pair x y \<in> T} =
        {y. \<exists>x. x \<in> S \<and> Pair x y \<in> ((S \<times> UNIV) \<inter> T)}"
    by auto
  show ?thesis
    apply (subst *)
    apply (rule closedin_closed_trans [OF _ closed_UNIV])
    apply (rule closedin_compact_projection [OF \<open>compact S\<close>])
    by (simp add: clo closedin_closed_Int)
qed

subsubsection\<open>Representing affine hull as a finite intersection of hyperplanes\<close>

proposition affine_hull_convex_Int_nonempty_interior:
  fixes S :: "'a::real_normed_vector set"
  assumes "convex S" "S \<inter> interior T \<noteq> {}"
    shows "affine hull (S \<inter> T) = affine hull S"
proof
  show "affine hull (S \<inter> T) \<subseteq> affine hull S"
    by (simp add: hull_mono)
next
  obtain a where "a \<in> S" "a \<in> T" and at: "a \<in> interior T"
    using assms interior_subset by blast
  then obtain e where "e > 0" and e: "cball a e \<subseteq> T"
    using mem_interior_cball by blast
  have *: "x \<in> op + a ` span ((\<lambda>x. x - a) ` (S \<inter> T))" if "x \<in> S" for x
  proof (cases "x = a")
    case True with that span_0 eq_add_iff image_def mem_Collect_eq show ?thesis
      by blast
  next
    case False
    define k where "k = min (1/2) (e / norm (x-a))"
    have k: "0 < k" "k < 1"
      using \<open>e > 0\<close> False by (auto simp: k_def)
    then have xa: "(x-a) = inverse k *\<^sub>R k *\<^sub>R (x-a)"
      by simp
    have "e / norm (x - a) \<ge> k"
      using k_def by linarith
    then have "a + k *\<^sub>R (x - a) \<in> cball a e"
      using \<open>0 < k\<close> False by (simp add: dist_norm field_simps)
    then have T: "a + k *\<^sub>R (x - a) \<in> T"
      using e by blast
    have S: "a + k *\<^sub>R (x - a) \<in> S"
      using k \<open>a \<in> S\<close> convexD [OF \<open>convex S\<close> \<open>a \<in> S\<close> \<open>x \<in> S\<close>, of "1-k" k]
      by (simp add: algebra_simps)
    have "inverse k *\<^sub>R k *\<^sub>R (x-a) \<in> span ((\<lambda>x. x - a) ` (S \<inter> T))"
      apply (rule span_mul)
      apply (rule span_superset)
      apply (rule image_eqI [where x = "a + k *\<^sub>R (x - a)"])
      apply (auto simp: S T)
      done
    with xa image_iff show ?thesis  by fastforce
  qed
  show "affine hull S \<subseteq> affine hull (S \<inter> T)"
    apply (simp add: subset_hull)
    apply (simp add: \<open>a \<in> S\<close> \<open>a \<in> T\<close> hull_inc affine_hull_span_gen [of a])
    apply (force simp: *)
    done
qed

corollary affine_hull_convex_Int_open:
  fixes S :: "'a::real_normed_vector set"
  assumes "convex S" "open T" "S \<inter> T \<noteq> {}"
    shows "affine hull (S \<inter> T) = affine hull S"
using affine_hull_convex_Int_nonempty_interior assms interior_eq by blast

corollary affine_hull_affine_Int_nonempty_interior:
  fixes S :: "'a::real_normed_vector set"
  assumes "affine S" "S \<inter> interior T \<noteq> {}"
    shows "affine hull (S \<inter> T) = affine hull S"
by (simp add: affine_hull_convex_Int_nonempty_interior affine_imp_convex assms)

corollary affine_hull_affine_Int_open:
  fixes S :: "'a::real_normed_vector set"
  assumes "affine S" "open T" "S \<inter> T \<noteq> {}"
    shows "affine hull (S \<inter> T) = affine hull S"
by (simp add: affine_hull_convex_Int_open affine_imp_convex assms)

corollary affine_hull_convex_Int_openin:
  fixes S :: "'a::real_normed_vector set"
  assumes "convex S" "openin (subtopology euclidean (affine hull S)) T" "S \<inter> T \<noteq> {}"
    shows "affine hull (S \<inter> T) = affine hull S"
using assms unfolding openin_open
by (metis affine_hull_convex_Int_open hull_subset inf.orderE inf_assoc)

corollary affine_hull_openin:
  fixes S :: "'a::real_normed_vector set"
  assumes "openin (subtopology euclidean (affine hull T)) S" "S \<noteq> {}"
    shows "affine hull S = affine hull T"
using assms unfolding openin_open
by (metis affine_affine_hull affine_hull_affine_Int_open hull_hull)

corollary affine_hull_open:
  fixes S :: "'a::real_normed_vector set"
  assumes "open S" "S \<noteq> {}"
    shows "affine hull S = UNIV"
by (metis affine_hull_convex_Int_nonempty_interior assms convex_UNIV hull_UNIV inf_top.left_neutral interior_open)

lemma aff_dim_convex_Int_nonempty_interior:
  fixes S :: "'a::euclidean_space set"
  shows "\<lbrakk>convex S; S \<inter> interior T \<noteq> {}\<rbrakk> \<Longrightarrow> aff_dim(S \<inter> T) = aff_dim S"
using aff_dim_affine_hull2 affine_hull_convex_Int_nonempty_interior by blast

lemma aff_dim_convex_Int_open:
  fixes S :: "'a::euclidean_space set"
  shows "\<lbrakk>convex S; open T; S \<inter> T \<noteq> {}\<rbrakk> \<Longrightarrow>  aff_dim(S \<inter> T) = aff_dim S"
using aff_dim_convex_Int_nonempty_interior interior_eq by blast

lemma affine_hull_Diff:
  fixes S:: "'a::real_normed_vector set"
  assumes ope: "openin (subtopology euclidean (affine hull S)) S" and "finite F" "F \<subset> S"
    shows "affine hull (S - F) = affine hull S"
proof -
  have clo: "closedin (subtopology euclidean S) F"
    using assms finite_imp_closedin by auto
  moreover have "S - F \<noteq> {}"
    using assms by auto
  ultimately show ?thesis
    by (metis ope closedin_def topspace_euclidean_subtopology affine_hull_openin openin_trans)
qed

lemma affine_hull_halfspace_lt:
  fixes a :: "'a::euclidean_space"
  shows "affine hull {x. a \<bullet> x < r} = (if a = 0 \<and> r \<le> 0 then {} else UNIV)"
using halfspace_eq_empty_lt [of a r]
by (simp add: open_halfspace_lt affine_hull_open)

lemma affine_hull_halfspace_le:
  fixes a :: "'a::euclidean_space"
  shows "affine hull {x. a \<bullet> x \<le> r} = (if a = 0 \<and> r < 0 then {} else UNIV)"
proof (cases "a = 0")
  case True then show ?thesis by simp
next
  case False
  then have "affine hull closure {x. a \<bullet> x < r} = UNIV"
    using affine_hull_halfspace_lt closure_same_affine_hull by fastforce
  moreover have "{x. a \<bullet> x < r} \<subseteq> {x. a \<bullet> x \<le> r}"
    by (simp add: Collect_mono)
  ultimately show ?thesis using False antisym_conv hull_mono top_greatest
    by (metis affine_hull_halfspace_lt)
qed

lemma affine_hull_halfspace_gt:
  fixes a :: "'a::euclidean_space"
  shows "affine hull {x. a \<bullet> x > r} = (if a = 0 \<and> r \<ge> 0 then {} else UNIV)"
using halfspace_eq_empty_gt [of r a]
by (simp add: open_halfspace_gt affine_hull_open)

lemma affine_hull_halfspace_ge:
  fixes a :: "'a::euclidean_space"
  shows "affine hull {x. a \<bullet> x \<ge> r} = (if a = 0 \<and> r > 0 then {} else UNIV)"
using affine_hull_halfspace_le [of "-a" "-r"] by simp

lemma aff_dim_halfspace_lt:
  fixes a :: "'a::euclidean_space"
  shows "aff_dim {x. a \<bullet> x < r} =
        (if a = 0 \<and> r \<le> 0 then -1 else DIM('a))"
by simp (metis aff_dim_open halfspace_eq_empty_lt open_halfspace_lt)

lemma aff_dim_halfspace_le:
  fixes a :: "'a::euclidean_space"
  shows "aff_dim {x. a \<bullet> x \<le> r} =
        (if a = 0 \<and> r < 0 then -1 else DIM('a))"
proof -
  have "int (DIM('a)) = aff_dim (UNIV::'a set)"
    by (simp add: aff_dim_UNIV)
  then have "aff_dim (affine hull {x. a \<bullet> x \<le> r}) = DIM('a)" if "(a = 0 \<longrightarrow> r \<ge> 0)"
    using that by (simp add: affine_hull_halfspace_le not_less)
  then show ?thesis
    by (force simp: aff_dim_affine_hull)
qed

lemma aff_dim_halfspace_gt:
  fixes a :: "'a::euclidean_space"
  shows "aff_dim {x. a \<bullet> x > r} =
        (if a = 0 \<and> r \<ge> 0 then -1 else DIM('a))"
by simp (metis aff_dim_open halfspace_eq_empty_gt open_halfspace_gt)

lemma aff_dim_halfspace_ge:
  fixes a :: "'a::euclidean_space"
  shows "aff_dim {x. a \<bullet> x \<ge> r} =
        (if a = 0 \<and> r > 0 then -1 else DIM('a))"
using aff_dim_halfspace_le [of "-a" "-r"] by simp

subsection\<open>Properties of special hyperplanes\<close>

lemma subspace_hyperplane: "subspace {x. a \<bullet> x = 0}"
  by (simp add: subspace_def inner_right_distrib)

lemma subspace_hyperplane2: "subspace {x. x \<bullet> a = 0}"
  by (simp add: inner_commute inner_right_distrib subspace_def)

lemma special_hyperplane_span:
  fixes S :: "'n::euclidean_space set"
  assumes "k \<in> Basis"
  shows "{x. k \<bullet> x = 0} = span (Basis - {k})"
proof -
  have *: "x \<in> span (Basis - {k})" if "k \<bullet> x = 0" for x
  proof -
    have "x = (\<Sum>b\<in>Basis. (x \<bullet> b) *\<^sub>R b)"
      by (simp add: euclidean_representation)
    also have "... = (\<Sum>b \<in> Basis - {k}. (x \<bullet> b) *\<^sub>R b)"
      by (auto simp: sum.remove [of _ k] inner_commute assms that)
    finally have "x = (\<Sum>b\<in>Basis - {k}. (x \<bullet> b) *\<^sub>R b)" .
    then show ?thesis
      by (simp add: Linear_Algebra.span_finite) metis
  qed
  show ?thesis
    apply (rule span_subspace [symmetric])
    using assms
    apply (auto simp: inner_not_same_Basis intro: * subspace_hyperplane)
    done
qed

lemma dim_special_hyperplane:
  fixes k :: "'n::euclidean_space"
  shows "k \<in> Basis \<Longrightarrow> dim {x. k \<bullet> x = 0} = DIM('n) - 1"
apply (simp add: special_hyperplane_span)
apply (rule Linear_Algebra.dim_unique [OF subset_refl])
apply (auto simp: Diff_subset independent_substdbasis)
apply (metis member_remove remove_def span_clauses(1))
done

proposition dim_hyperplane:
  fixes a :: "'a::euclidean_space"
  assumes "a \<noteq> 0"
    shows "dim {x. a \<bullet> x = 0} = DIM('a) - 1"
proof -
  have span0: "span {x. a \<bullet> x = 0} = {x. a \<bullet> x = 0}"
    by (rule span_unique) (auto simp: subspace_hyperplane)
  then obtain B where "independent B"
              and Bsub: "B \<subseteq> {x. a \<bullet> x = 0}"
              and subspB: "{x. a \<bullet> x = 0} \<subseteq> span B"
              and card0: "(card B = dim {x. a \<bullet> x = 0})"
              and ortho: "pairwise orthogonal B"
    using orthogonal_basis_exists by metis
  with assms have "a \<notin> span B"
    by (metis (mono_tags, lifting) span_eq inner_eq_zero_iff mem_Collect_eq span0 span_subspace)
  then have ind: "independent (insert a B)"
    by (simp add: \<open>independent B\<close> independent_insert)
  have "finite B"
    using \<open>independent B\<close> independent_bound by blast
  have "UNIV \<subseteq> span (insert a B)"
  proof fix y::'a
    obtain r z where z: "y = r *\<^sub>R a + z" "a \<bullet> z = 0"
      apply (rule_tac r="(a \<bullet> y) / (a \<bullet> a)" and z = "y - ((a \<bullet> y) / (a \<bullet> a)) *\<^sub>R a" in that)
      using assms
      by (auto simp: algebra_simps)
    show "y \<in> span (insert a B)"
      by (metis (mono_tags, lifting) z Bsub Convex_Euclidean_Space.span_eq
         add_diff_cancel_left' mem_Collect_eq span0 span_breakdown_eq span_subspace subspB)
  qed
  then have dima: "DIM('a) = dim(insert a B)"
    by (metis antisym dim_UNIV dim_subset_UNIV subset_le_dim)
  then show ?thesis
    by (metis (mono_tags, lifting) Bsub Diff_insert_absorb \<open>a \<notin> span B\<close> ind card0 card_Diff_singleton dim_span indep_card_eq_dim_span insertI1 subsetCE subspB)
qed

lemma lowdim_eq_hyperplane:
  fixes S :: "'a::euclidean_space set"
  assumes "dim S = DIM('a) - 1"
  obtains a where "a \<noteq> 0" and "span S = {x. a \<bullet> x = 0}"
proof -
  have [simp]: "dim S < DIM('a)"
    by (simp add: DIM_positive assms)
  then obtain b where b: "b \<noteq> 0" "span S \<subseteq> {a. b \<bullet> a = 0}"
    using lowdim_subset_hyperplane [of S] by fastforce
  show ?thesis
    using b that real_vector_class.subspace_span [of S]
    by (simp add: assms dim_hyperplane subspace_dim_equal subspace_hyperplane)
qed

lemma dim_eq_hyperplane:
  fixes S :: "'n::euclidean_space set"
  shows "dim S = DIM('n) - 1 \<longleftrightarrow> (\<exists>a. a \<noteq> 0 \<and> span S = {x. a \<bullet> x = 0})"
by (metis One_nat_def dim_hyperplane dim_span lowdim_eq_hyperplane)

proposition aff_dim_eq_hyperplane:
  fixes S :: "'a::euclidean_space set"
  shows "aff_dim S = DIM('a) - 1 \<longleftrightarrow> (\<exists>a b. a \<noteq> 0 \<and> affine hull S = {x. a \<bullet> x = b})"
proof (cases "S = {}")
  case True then show ?thesis
    by (auto simp: dest: hyperplane_eq_Ex)
next
  case False
  then obtain c where "c \<in> S" by blast
  show ?thesis
  proof (cases "c = 0")
    case True show ?thesis
    apply (simp add: aff_dim_eq_dim [of c] affine_hull_span_gen [of c] \<open>c \<in> S\<close> hull_inc dim_eq_hyperplane
                del: One_nat_def)
    apply (rule ex_cong)
    apply (metis (mono_tags) span_0 \<open>c = 0\<close> image_add_0 inner_zero_right mem_Collect_eq)
    done
  next
    case False
    have xc_im: "x \<in> op + c ` {y. a \<bullet> y = 0}" if "a \<bullet> x = a \<bullet> c" for a x
    proof -
      have "\<exists>y. a \<bullet> y = 0 \<and> c + y = x"
        by (metis that add.commute diff_add_cancel inner_commute inner_diff_left right_minus_eq)
      then show "x \<in> op + c ` {y. a \<bullet> y = 0}"
        by blast
    qed
    have 2: "span ((\<lambda>x. x - c) ` S) = {x. a \<bullet> x = 0}"
         if "op + c ` span ((\<lambda>x. x - c) ` S) = {x. a \<bullet> x = b}" for a b
    proof -
      have "b = a \<bullet> c"
        using span_0 that by fastforce
      with that have "op + c ` span ((\<lambda>x. x - c) ` S) = {x. a \<bullet> x = a \<bullet> c}"
        by simp
      then have "span ((\<lambda>x. x - c) ` S) = (\<lambda>x. x - c) ` {x. a \<bullet> x = a \<bullet> c}"
        by (metis (no_types) image_cong translation_galois uminus_add_conv_diff)
      also have "... = {x. a \<bullet> x = 0}"
        by (force simp: inner_distrib inner_diff_right
             intro: image_eqI [where x="x+c" for x])
      finally show ?thesis .
    qed
    show ?thesis
      apply (simp add: aff_dim_eq_dim [of c] affine_hull_span_gen [of c] \<open>c \<in> S\<close> hull_inc dim_eq_hyperplane
                  del: One_nat_def, safe)
      apply (fastforce simp add: inner_distrib intro: xc_im)
      apply (force simp: intro!: 2)
      done
  qed
qed

corollary aff_dim_hyperplane [simp]:
  fixes a :: "'a::euclidean_space"
  shows "a \<noteq> 0 \<Longrightarrow> aff_dim {x. a \<bullet> x = r} = DIM('a) - 1"
by (metis aff_dim_eq_hyperplane affine_hull_eq affine_hyperplane)

subsection\<open>Some stepping theorems\<close>

lemma dim_empty [simp]: "dim ({} :: 'a::euclidean_space set) = 0"
  by (force intro!: dim_unique)

lemma dim_insert:
  fixes x :: "'a::euclidean_space"
  shows "dim (insert x S) = (if x \<in> span S then dim S else dim S + 1)"
proof -
  show ?thesis
  proof (cases "x \<in> span S")
    case True then show ?thesis
      by (metis dim_span span_redundant)
  next
    case False
    obtain B where B: "B \<subseteq> span S" "independent B" "span S \<subseteq> span B" "card B = dim (span S)"
      using basis_exists [of "span S"] by blast
    have 1: "insert x B \<subseteq> span (insert x S)"
      by (meson \<open>B \<subseteq> span S\<close> dual_order.trans insertI1 insert_subsetI span_mono span_superset subset_insertI)
    have 2: "span (insert x S) \<subseteq> span (insert x B)"
      by (metis \<open>B \<subseteq> span S\<close> \<open>span S \<subseteq> span B\<close> span_breakdown_eq span_subspace subsetI subspace_span)
    have 3: "independent (insert x B)"
      by (metis B independent_insert span_subspace subspace_span False)
    have "dim (span (insert x S)) = Suc (dim S)"
      apply (rule dim_unique [OF 1 2 3])
      by (metis B False card_insert_disjoint dim_span independent_imp_finite subsetCE)
    then show ?thesis
      by (simp add: False)
  qed
qed

lemma dim_singleton [simp]:
  fixes x :: "'a::euclidean_space"
  shows "dim{x} = (if x = 0 then 0 else 1)"
by (simp add: dim_insert)

lemma dim_eq_0 [simp]:
  fixes S :: "'a::euclidean_space set"
  shows "dim S = 0 \<longleftrightarrow> S \<subseteq> {0}"
apply safe
apply (metis DIM_positive DIM_real card_ge_dim_independent contra_subsetD dim_empty dim_insert dim_singleton empty_subsetI independent_empty less_not_refl zero_le)
by (metis dim_singleton dim_subset le_0_eq)
                  
lemma aff_dim_insert:
  fixes a :: "'a::euclidean_space"
  shows "aff_dim (insert a S) = (if a \<in> affine hull S then aff_dim S else aff_dim S + 1)"
proof (cases "S = {}")
  case True then show ?thesis
    by simp
next
  case False
  then obtain x s' where S: "S = insert x s'" "x \<notin> s'"
    by (meson Set.set_insert all_not_in_conv)
  show ?thesis using S
    apply (simp add: hull_redundant cong: aff_dim_affine_hull2)
    apply (simp add: affine_hull_insert_span_gen hull_inc)
    apply (simp add: insert_commute [of a] hull_inc aff_dim_eq_dim [of x] dim_insert span_0)
    apply (metis (no_types, lifting) add_minus_cancel image_iff uminus_add_conv_diff)
    done
qed

lemma subspace_bounded_eq_trivial:
  fixes S :: "'a::real_normed_vector set"
  assumes "subspace S"
    shows "bounded S \<longleftrightarrow> S = {0}"
proof -
  have "False" if "bounded S" "x \<in> S" "x \<noteq> 0" for x
  proof -
    obtain B where B: "\<And>y. y \<in> S \<Longrightarrow> norm y < B" "B > 0"
      using \<open>bounded S\<close> by (force simp: bounded_pos_less)
    have "(B / norm x) *\<^sub>R x \<in> S"
      using assms subspace_mul \<open>x \<in> S\<close> by auto
    moreover have "norm ((B / norm x) *\<^sub>R x) = B"
      using that B by (simp add: algebra_simps)
    ultimately show False using B by force
  qed
  then have "bounded S \<Longrightarrow> S = {0}"
    using assms subspace_0 by fastforce
  then show ?thesis
    by blast
qed

lemma affine_bounded_eq_trivial:
  fixes S :: "'a::real_normed_vector set"
  assumes "affine S"
    shows "bounded S \<longleftrightarrow> S = {} \<or> (\<exists>a. S = {a})"
proof (cases "S = {}")
  case True then show ?thesis
    by simp
next
  case False
  then obtain b where "b \<in> S" by blast
  with False assms show ?thesis
    apply safe
    using affine_diffs_subspace [OF assms \<open>b \<in> S\<close>]
    apply (metis (no_types, lifting) subspace_bounded_eq_trivial ab_left_minus bounded_translation
                image_empty image_insert translation_invert)
    apply force
    done
qed

lemma affine_bounded_eq_lowdim:
  fixes S :: "'a::euclidean_space set"
  assumes "affine S"
    shows "bounded S \<longleftrightarrow> aff_dim S \<le> 0"
apply safe
using affine_bounded_eq_trivial assms apply fastforce
by (metis aff_dim_sing aff_dim_subset affine_dim_equal affine_sing all_not_in_conv assms bounded_empty bounded_insert dual_order.antisym empty_subsetI insert_subset)


lemma bounded_hyperplane_eq_trivial_0:
  fixes a :: "'a::euclidean_space"
  assumes "a \<noteq> 0"
  shows "bounded {x. a \<bullet> x = 0} \<longleftrightarrow> DIM('a) = 1"
proof
  assume "bounded {x. a \<bullet> x = 0}"
  then have "aff_dim {x. a \<bullet> x = 0} \<le> 0"
    by (simp add: affine_bounded_eq_lowdim affine_hyperplane)
  with assms show "DIM('a) = 1"
    by (simp add: le_Suc_eq aff_dim_hyperplane)
next
  assume "DIM('a) = 1"
  then show "bounded {x. a \<bullet> x = 0}"
    by (simp add: aff_dim_hyperplane affine_bounded_eq_lowdim affine_hyperplane assms)
qed

lemma bounded_hyperplane_eq_trivial:
  fixes a :: "'a::euclidean_space"
  shows "bounded {x. a \<bullet> x = r} \<longleftrightarrow> (if a = 0 then r \<noteq> 0 else DIM('a) = 1)"
proof (simp add: bounded_hyperplane_eq_trivial_0, clarify)
  assume "r \<noteq> 0" "a \<noteq> 0"
  have "aff_dim {x. y \<bullet> x = 0} = aff_dim {x. a \<bullet> x = r}" if "y \<noteq> 0" for y::'a
    by (metis that \<open>a \<noteq> 0\<close> aff_dim_hyperplane)
  then show "bounded {x. a \<bullet> x = r} = (DIM('a) = Suc 0)"
    by (metis One_nat_def \<open>a \<noteq> 0\<close> affine_bounded_eq_lowdim affine_hyperplane bounded_hyperplane_eq_trivial_0)
qed

subsection\<open>General case without assuming closure and getting non-strict separation\<close>

proposition separating_hyperplane_closed_point_inset:
  fixes S :: "'a::euclidean_space set"
  assumes "convex S" "closed S" "S \<noteq> {}" "z \<notin> S"
  obtains a b where "a \<in> S" "(a - z) \<bullet> z < b" "\<And>x. x \<in> S \<Longrightarrow> b < (a - z) \<bullet> x"
proof -
  obtain y where "y \<in> S" and y: "\<And>u. u \<in> S \<Longrightarrow> dist z y \<le> dist z u"
    using distance_attains_inf [of S z] assms by auto
  then have *: "(y - z) \<bullet> z < (y - z) \<bullet> z + (norm (y - z))\<^sup>2 / 2"
    using \<open>y \<in> S\<close> \<open>z \<notin> S\<close> by auto
  show ?thesis
  proof (rule that [OF \<open>y \<in> S\<close> *])
    fix x
    assume "x \<in> S"
    have yz: "0 < (y - z) \<bullet> (y - z)"
      using \<open>y \<in> S\<close> \<open>z \<notin> S\<close> by auto
    { assume 0: "0 < ((z - y) \<bullet> (x - y))"
      with any_closest_point_dot [OF \<open>convex S\<close> \<open>closed S\<close>]
      have False
        using y \<open>x \<in> S\<close> \<open>y \<in> S\<close> not_less by blast
    }
    then have "0 \<le> ((y - z) \<bullet> (x - y))"
      by (force simp: not_less inner_diff_left)
    with yz have "0 < 2 * ((y - z) \<bullet> (x - y)) + (y - z) \<bullet> (y - z)"
      by (simp add: algebra_simps)
    then show "(y - z) \<bullet> z + (norm (y - z))\<^sup>2 / 2 < (y - z) \<bullet> x"
      by (simp add: field_simps inner_diff_left inner_diff_right dot_square_norm [symmetric])
  qed
qed

lemma separating_hyperplane_closed_0_inset:
  fixes S :: "'a::euclidean_space set"
  assumes "convex S" "closed S" "S \<noteq> {}" "0 \<notin> S"
  obtains a b where "a \<in> S" "a \<noteq> 0" "0 < b" "\<And>x. x \<in> S \<Longrightarrow> a \<bullet> x > b"
using separating_hyperplane_closed_point_inset [OF assms]
by simp (metis \<open>0 \<notin> S\<close>)


proposition separating_hyperplane_set_0_inspan:
  fixes S :: "'a::euclidean_space set"
  assumes "convex S" "S \<noteq> {}" "0 \<notin> S"
  obtains a where "a \<in> span S" "a \<noteq> 0" "\<And>x. x \<in> S \<Longrightarrow> 0 \<le> a \<bullet> x"
proof -
  define k where [abs_def]: "k c = {x. 0 \<le> c \<bullet> x}" for c :: 'a
  have *: "span S \<inter> frontier (cball 0 1) \<inter> \<Inter>f' \<noteq> {}"
          if f': "finite f'" "f' \<subseteq> k ` S" for f'
  proof -
    obtain C where "C \<subseteq> S" "finite C" and C: "f' = k ` C"
      using finite_subset_image [OF f'] by blast
    obtain a where "a \<in> S" "a \<noteq> 0"
      using \<open>S \<noteq> {}\<close> \<open>0 \<notin> S\<close> ex_in_conv by blast
    then have "norm (a /\<^sub>R (norm a)) = 1"
      by simp
    moreover have "a /\<^sub>R (norm a) \<in> span S"
      by (simp add: \<open>a \<in> S\<close> span_mul span_superset)
    ultimately have ass: "a /\<^sub>R (norm a) \<in> span S \<inter> sphere 0 1"
      by simp
    show ?thesis
    proof (cases "C = {}")
      case True with C ass show ?thesis
        by auto
    next
      case False
      have "closed (convex hull C)"
        using \<open>finite C\<close> compact_eq_bounded_closed finite_imp_compact_convex_hull by auto
      moreover have "convex hull C \<noteq> {}"
        by (simp add: False)
      moreover have "0 \<notin> convex hull C"
        by (metis \<open>C \<subseteq> S\<close> \<open>convex S\<close> \<open>0 \<notin> S\<close> convex_hull_subset hull_same insert_absorb insert_subset)
      ultimately obtain a b
            where "a \<in> convex hull C" "a \<noteq> 0" "0 < b"
                  and ab: "\<And>x. x \<in> convex hull C \<Longrightarrow> a \<bullet> x > b"
        using separating_hyperplane_closed_0_inset by blast
      then have "a \<in> S"
        by (metis \<open>C \<subseteq> S\<close> assms(1) subsetCE subset_hull)
      moreover have "norm (a /\<^sub>R (norm a)) = 1"
        using \<open>a \<noteq> 0\<close> by simp
      moreover have "a /\<^sub>R (norm a) \<in> span S"
        by (simp add: \<open>a \<in> S\<close> span_mul span_superset)
      ultimately have ass: "a /\<^sub>R (norm a) \<in> span S \<inter> sphere 0 1"
        by simp
      have aa: "a /\<^sub>R (norm a) \<in> (\<Inter>c\<in>C. {x. 0 \<le> c \<bullet> x})"
        apply (clarsimp simp add: divide_simps)
        using ab \<open>0 < b\<close>
        by (metis hull_inc inner_commute less_eq_real_def less_trans)
      show ?thesis
        apply (simp add: C k_def)
        using ass aa Int_iff empty_iff by blast
    qed
  qed
  have "(span S \<inter> frontier(cball 0 1)) \<inter> (\<Inter> (k ` S)) \<noteq> {}"
    apply (rule compact_imp_fip)
    apply (blast intro: compact_cball)
    using closed_halfspace_ge k_def apply blast
    apply (metis *)
    done
  then show ?thesis
    unfolding set_eq_iff k_def
    by simp (metis inner_commute norm_eq_zero that zero_neq_one)
qed


lemma separating_hyperplane_set_point_inaff:
  fixes S :: "'a::euclidean_space set"
  assumes "convex S" "S \<noteq> {}" and zno: "z \<notin> S"
  obtains a b where "(z + a) \<in> affine hull (insert z S)"
                and "a \<noteq> 0" and "a \<bullet> z \<le> b"
                and "\<And>x. x \<in> S \<Longrightarrow> a \<bullet> x \<ge> b"
proof -
from separating_hyperplane_set_0_inspan [of "image (\<lambda>x. -z + x) S"]
  have "convex (op + (- z) ` S)"
    by (simp add: \<open>convex S\<close>)
  moreover have "op + (- z) ` S \<noteq> {}"
    by (simp add: \<open>S \<noteq> {}\<close>)
  moreover have "0 \<notin> op + (- z) ` S"
    using zno by auto
  ultimately obtain a where "a \<in> span (op + (- z) ` S)" "a \<noteq> 0"
                  and a:  "\<And>x. x \<in> (op + (- z) ` S) \<Longrightarrow> 0 \<le> a \<bullet> x"
    using separating_hyperplane_set_0_inspan [of "image (\<lambda>x. -z + x) S"]
    by blast
  then have szx: "\<And>x. x \<in> S \<Longrightarrow> a \<bullet> z \<le> a \<bullet> x"
    by (metis (no_types, lifting) imageI inner_minus_right inner_right_distrib minus_add neg_le_0_iff_le neg_le_iff_le real_add_le_0_iff)
  show ?thesis
    apply (rule_tac a=a and b = "a  \<bullet> z" in that, simp_all)
    using \<open>a \<in> span (op + (- z) ` S)\<close> affine_hull_insert_span_gen apply blast
    apply (simp_all add: \<open>a \<noteq> 0\<close> szx)
    done
qed

proposition supporting_hyperplane_rel_boundary:
  fixes S :: "'a::euclidean_space set"
  assumes "convex S" "x \<in> S" and xno: "x \<notin> rel_interior S"
  obtains a where "a \<noteq> 0"
              and "\<And>y. y \<in> S \<Longrightarrow> a \<bullet> x \<le> a \<bullet> y"
              and "\<And>y. y \<in> rel_interior S \<Longrightarrow> a \<bullet> x < a \<bullet> y"
proof -
  obtain a b where aff: "(x + a) \<in> affine hull (insert x (rel_interior S))"
                  and "a \<noteq> 0" and "a \<bullet> x \<le> b"
                  and ageb: "\<And>u. u \<in> (rel_interior S) \<Longrightarrow> a \<bullet> u \<ge> b"
    using separating_hyperplane_set_point_inaff [of "rel_interior S" x] assms
    by (auto simp: rel_interior_eq_empty convex_rel_interior)
  have le_ay: "a \<bullet> x \<le> a \<bullet> y" if "y \<in> S" for y
  proof -
    have con: "continuous_on (closure (rel_interior S)) (op \<bullet> a)"
      by (rule continuous_intros continuous_on_subset | blast)+
    have y: "y \<in> closure (rel_interior S)"
      using \<open>convex S\<close> closure_def convex_closure_rel_interior \<open>y \<in> S\<close>
      by fastforce
    show ?thesis
      using continuous_ge_on_closure [OF con y] ageb \<open>a \<bullet> x \<le> b\<close>
      by fastforce
  qed
  have 3: "a \<bullet> x < a \<bullet> y" if "y \<in> rel_interior S" for y
  proof -
    obtain e where "0 < e" "y \<in> S" and e: "cball y e \<inter> affine hull S \<subseteq> S"
      using \<open>y \<in> rel_interior S\<close> by (force simp: rel_interior_cball)
    define y' where "y' = y - (e / norm a) *\<^sub>R ((x + a) - x)"
    have "y' \<in> cball y e"
      unfolding y'_def using \<open>0 < e\<close> by force
    moreover have "y' \<in> affine hull S"
      unfolding y'_def
      by (metis \<open>x \<in> S\<close> \<open>y \<in> S\<close> \<open>convex S\<close> aff affine_affine_hull hull_redundant
                rel_interior_same_affine_hull hull_inc mem_affine_3_minus2)
    ultimately have "y' \<in> S"
      using e by auto
    have "a \<bullet> x \<le> a \<bullet> y"
      using le_ay \<open>a \<noteq> 0\<close> \<open>y \<in> S\<close> by blast
    moreover have "a \<bullet> x \<noteq> a \<bullet> y"
      using le_ay [OF \<open>y' \<in> S\<close>] \<open>a \<noteq> 0\<close>
      apply (simp add: y'_def inner_diff dot_square_norm power2_eq_square)
      by (metis \<open>0 < e\<close> add_le_same_cancel1 inner_commute inner_real_def inner_zero_left le_diff_eq norm_le_zero_iff real_mult_le_cancel_iff2)
    ultimately show ?thesis by force
  qed
  show ?thesis
    by (rule that [OF \<open>a \<noteq> 0\<close> le_ay 3])
qed

lemma supporting_hyperplane_relative_frontier:
  fixes S :: "'a::euclidean_space set"
  assumes "convex S" "x \<in> closure S" "x \<notin> rel_interior S"
  obtains a where "a \<noteq> 0"
              and "\<And>y. y \<in> closure S \<Longrightarrow> a \<bullet> x \<le> a \<bullet> y"
              and "\<And>y. y \<in> rel_interior S \<Longrightarrow> a \<bullet> x < a \<bullet> y"
using supporting_hyperplane_rel_boundary [of "closure S" x]
by (metis assms convex_closure convex_rel_interior_closure)


subsection\<open> Some results on decomposing convex hulls: intersections, simplicial subdivision\<close>

lemma
  fixes s :: "'a::euclidean_space set"
  assumes "~ (affine_dependent(s \<union> t))"
    shows convex_hull_Int_subset: "convex hull s \<inter> convex hull t \<subseteq> convex hull (s \<inter> t)" (is ?C)
      and affine_hull_Int_subset: "affine hull s \<inter> affine hull t \<subseteq> affine hull (s \<inter> t)" (is ?A)
proof -
  have [simp]: "finite s" "finite t"
    using aff_independent_finite assms by blast+
    have "sum u (s \<inter> t) = 1 \<and>
          (\<Sum>v\<in>s \<inter> t. u v *\<^sub>R v) = (\<Sum>v\<in>s. u v *\<^sub>R v)"
      if [simp]:  "sum u s = 1"
                 "sum v t = 1"
         and eq: "(\<Sum>x\<in>t. v x *\<^sub>R x) = (\<Sum>x\<in>s. u x *\<^sub>R x)" for u v
    proof -
    define f where "f x = (if x \<in> s then u x else 0) - (if x \<in> t then v x else 0)" for x
    have "sum f (s \<union> t) = 0"
      apply (simp add: f_def sum_Un sum_subtractf)
      apply (simp add: sum.inter_restrict [symmetric] Int_commute)
      done
    moreover have "(\<Sum>x\<in>(s \<union> t). f x *\<^sub>R x) = 0"
      apply (simp add: f_def sum_Un scaleR_left_diff_distrib sum_subtractf)
      apply (simp add: if_smult sum.inter_restrict [symmetric] Int_commute eq
          cong del: if_weak_cong)
      done
    ultimately have "\<And>v. v \<in> s \<union> t \<Longrightarrow> f v = 0"
      using aff_independent_finite assms unfolding affine_dependent_explicit
      by blast
    then have u [simp]: "\<And>x. x \<in> s \<Longrightarrow> u x = (if x \<in> t then v x else 0)"
      by (simp add: f_def) presburger
    have "sum u (s \<inter> t) = sum u s"
      by (simp add: sum.inter_restrict)
    then have "sum u (s \<inter> t) = 1"
      using that by linarith
    moreover have "(\<Sum>v\<in>s \<inter> t. u v *\<^sub>R v) = (\<Sum>v\<in>s. u v *\<^sub>R v)"
      by (auto simp: if_smult sum.inter_restrict intro: sum.cong)
    ultimately show ?thesis
      by force
    qed
    then show ?A ?C
      by (auto simp: convex_hull_finite affine_hull_finite)
qed


proposition affine_hull_Int:
  fixes s :: "'a::euclidean_space set"
  assumes "~ (affine_dependent(s \<union> t))"
    shows "affine hull (s \<inter> t) = affine hull s \<inter> affine hull t"
apply (rule subset_antisym)
apply (simp add: hull_mono)
by (simp add: affine_hull_Int_subset assms)

proposition convex_hull_Int:
  fixes s :: "'a::euclidean_space set"
  assumes "~ (affine_dependent(s \<union> t))"
    shows "convex hull (s \<inter> t) = convex hull s \<inter> convex hull t"
apply (rule subset_antisym)
apply (simp add: hull_mono)
by (simp add: convex_hull_Int_subset assms)

proposition
  fixes s :: "'a::euclidean_space set set"
  assumes "~ (affine_dependent (\<Union>s))"
    shows affine_hull_Inter: "affine hull (\<Inter>s) = (\<Inter>t\<in>s. affine hull t)" (is "?A")
      and convex_hull_Inter: "convex hull (\<Inter>s) = (\<Inter>t\<in>s. convex hull t)" (is "?C")
proof -
  have "finite s"
    using aff_independent_finite assms finite_UnionD by blast
  then have "?A \<and> ?C" using assms
  proof (induction s rule: finite_induct)
    case empty then show ?case by auto
  next
    case (insert t F)
    then show ?case
    proof (cases "F={}")
      case True then show ?thesis by simp
    next
      case False
      with "insert.prems" have [simp]: "\<not> affine_dependent (t \<union> \<Inter>F)"
        by (auto intro: affine_dependent_subset)
      have [simp]: "\<not> affine_dependent (\<Union>F)"
        using affine_independent_subset insert.prems by fastforce
      show ?thesis
        by (simp add: affine_hull_Int convex_hull_Int insert.IH)
    qed
  qed
  then show "?A" "?C"
    by auto
qed

proposition in_convex_hull_exchange_unique:
  fixes S :: "'a::euclidean_space set"
  assumes naff: "~ affine_dependent S" and a: "a \<in> convex hull S"
      and S: "T \<subseteq> S" "T' \<subseteq> S"
      and x:  "x \<in> convex hull (insert a T)"
      and x': "x \<in> convex hull (insert a T')"
    shows "x \<in> convex hull (insert a (T \<inter> T'))"
proof (cases "a \<in> S")
  case True
  then have "\<not> affine_dependent (insert a T \<union> insert a T')"
    using affine_dependent_subset assms by auto
  then have "x \<in> convex hull (insert a T \<inter> insert a T')"
    by (metis IntI convex_hull_Int x x')
  then show ?thesis
    by simp
next
  case False
  then have anot: "a \<notin> T" "a \<notin> T'"
    using assms by auto
  have [simp]: "finite S"
    by (simp add: aff_independent_finite assms)
  then obtain b where b0: "\<And>s. s \<in> S \<Longrightarrow> 0 \<le> b s"
                  and b1: "sum b S = 1" and aeq: "a = (\<Sum>s\<in>S. b s *\<^sub>R s)"
    using a by (auto simp: convex_hull_finite)
  have fin [simp]: "finite T" "finite T'"
    using assms infinite_super \<open>finite S\<close> by blast+
  then obtain c c' where c0: "\<And>t. t \<in> insert a T \<Longrightarrow> 0 \<le> c t"
                     and c1: "sum c (insert a T) = 1"
                     and xeq: "x = (\<Sum>t \<in> insert a T. c t *\<^sub>R t)"
                     and c'0: "\<And>t. t \<in> insert a T' \<Longrightarrow> 0 \<le> c' t"
                     and c'1: "sum c' (insert a T') = 1"
                     and x'eq: "x = (\<Sum>t \<in> insert a T'. c' t *\<^sub>R t)"
    using x x' by (auto simp: convex_hull_finite)
  with fin anot
  have sumTT': "sum c T = 1 - c a" "sum c' T' = 1 - c' a"
   and wsumT: "(\<Sum>t \<in> T. c t *\<^sub>R t) = x - c a *\<^sub>R a"
    by simp_all
  have wsumT': "(\<Sum>t \<in> T'. c' t *\<^sub>R t) = x - c' a *\<^sub>R a"
    using x'eq fin anot by simp
  define cc  where "cc \<equiv> \<lambda>x. if x \<in> T then c x else 0"
  define cc' where "cc' \<equiv> \<lambda>x. if x \<in> T' then c' x else 0"
  define dd  where "dd \<equiv> \<lambda>x. cc x - cc' x + (c a - c' a) * b x"
  have sumSS': "sum cc S = 1 - c a" "sum cc' S = 1 - c' a"
    unfolding cc_def cc'_def  using S
    by (simp_all add: Int_absorb1 Int_absorb2 sum_subtractf sum.inter_restrict [symmetric] sumTT')
  have wsumSS: "(\<Sum>t \<in> S. cc t *\<^sub>R t) = x - c a *\<^sub>R a" "(\<Sum>t \<in> S. cc' t *\<^sub>R t) = x - c' a *\<^sub>R a"
    unfolding cc_def cc'_def  using S
    by (simp_all add: Int_absorb1 Int_absorb2 if_smult sum.inter_restrict [symmetric] wsumT wsumT' cong: if_cong)
  have sum_dd0: "sum dd S = 0"
    unfolding dd_def  using S
    by (simp add: sumSS' comm_monoid_add_class.sum.distrib sum_subtractf
                  algebra_simps sum_distrib_right [symmetric] b1)
  have "(\<Sum>v\<in>S. (b v * x) *\<^sub>R v) = x *\<^sub>R (\<Sum>v\<in>S. b v *\<^sub>R v)" for x
    by (simp add: pth_5 real_vector.scale_sum_right mult.commute)
  then have *: "(\<Sum>v\<in>S. (b v * x) *\<^sub>R v) = x *\<^sub>R a" for x
    using aeq by blast
  have "(\<Sum>v \<in> S. dd v *\<^sub>R v) = 0"
    unfolding dd_def using S
    by (simp add: * wsumSS sum.distrib sum_subtractf algebra_simps)
  then have dd0: "dd v = 0" if "v \<in> S" for v
    using naff that \<open>finite S\<close> sum_dd0 unfolding affine_dependent_explicit
    apply (simp only: not_ex)
    apply (drule_tac x=S in spec)
    apply (drule_tac x=dd in spec, simp)
    done
  consider "c' a \<le> c a" | "c a \<le> c' a" by linarith
  then show ?thesis
  proof cases
    case 1
    then have "sum cc S \<le> sum cc' S"
      by (simp add: sumSS')
    then have le: "cc x \<le> cc' x" if "x \<in> S" for x
      using dd0 [OF that] 1 b0 mult_left_mono that
      by (fastforce simp add: dd_def algebra_simps)
    have cc0: "cc x = 0" if "x \<in> S" "x \<notin> T \<inter> T'" for x
      using le [OF \<open>x \<in> S\<close>] that c0
      by (force simp: cc_def cc'_def split: if_split_asm)
    show ?thesis
    proof (simp add: convex_hull_finite, intro exI conjI)
      show "\<forall>x\<in>T \<inter> T'. 0 \<le> (cc(a := c a)) x"
        by (simp add: c0 cc_def)
      show "0 \<le> (cc(a := c a)) a"
        by (simp add: c0)
      have "sum (cc(a := c a)) (insert a (T \<inter> T')) = c a + sum (cc(a := c a)) (T \<inter> T')"
        by (simp add: anot)
      also have "... = c a + sum (cc(a := c a)) S"
        apply simp
        apply (rule sum.mono_neutral_left)
        using \<open>T \<subseteq> S\<close> apply (auto simp: \<open>a \<notin> S\<close> cc0)
        done
      also have "... = c a + (1 - c a)"
        by (metis \<open>a \<notin> S\<close> fun_upd_other sum.cong sumSS')
      finally show "sum (cc(a := c a)) (insert a (T \<inter> T')) = 1"
        by simp
      have "(\<Sum>x\<in>insert a (T \<inter> T'). (cc(a := c a)) x *\<^sub>R x) = c a *\<^sub>R a + (\<Sum>x \<in> T \<inter> T'. (cc(a := c a)) x *\<^sub>R x)"
        by (simp add: anot)
      also have "... = c a *\<^sub>R a + (\<Sum>x \<in> S. (cc(a := c a)) x *\<^sub>R x)"
        apply simp
        apply (rule sum.mono_neutral_left)
        using \<open>T \<subseteq> S\<close> apply (auto simp: \<open>a \<notin> S\<close> cc0)
        done
      also have "... = c a *\<^sub>R a + x - c a *\<^sub>R a"
        by (simp add: wsumSS \<open>a \<notin> S\<close> if_smult sum_delta_notmem)
      finally show "(\<Sum>x\<in>insert a (T \<inter> T'). (cc(a := c a)) x *\<^sub>R x) = x"
        by simp
    qed
  next
    case 2
    then have "sum cc' S \<le> sum cc S"
      by (simp add: sumSS')
    then have le: "cc' x \<le> cc x" if "x \<in> S" for x
      using dd0 [OF that] 2 b0 mult_left_mono that
      by (fastforce simp add: dd_def algebra_simps)
    have cc0: "cc' x = 0" if "x \<in> S" "x \<notin> T \<inter> T'" for x
      using le [OF \<open>x \<in> S\<close>] that c'0
      by (force simp: cc_def cc'_def split: if_split_asm)
    show ?thesis
    proof (simp add: convex_hull_finite, intro exI conjI)
      show "\<forall>x\<in>T \<inter> T'. 0 \<le> (cc'(a := c' a)) x"
        by (simp add: c'0 cc'_def)
      show "0 \<le> (cc'(a := c' a)) a"
        by (simp add: c'0)
      have "sum (cc'(a := c' a)) (insert a (T \<inter> T')) = c' a + sum (cc'(a := c' a)) (T \<inter> T')"
        by (simp add: anot)
      also have "... = c' a + sum (cc'(a := c' a)) S"
        apply simp
        apply (rule sum.mono_neutral_left)
        using \<open>T \<subseteq> S\<close> apply (auto simp: \<open>a \<notin> S\<close> cc0)
        done
      also have "... = c' a + (1 - c' a)"
        by (metis \<open>a \<notin> S\<close> fun_upd_other sum.cong sumSS')
      finally show "sum (cc'(a := c' a)) (insert a (T \<inter> T')) = 1"
        by simp
      have "(\<Sum>x\<in>insert a (T \<inter> T'). (cc'(a := c' a)) x *\<^sub>R x) = c' a *\<^sub>R a + (\<Sum>x \<in> T \<inter> T'. (cc'(a := c' a)) x *\<^sub>R x)"
        by (simp add: anot)
      also have "... = c' a *\<^sub>R a + (\<Sum>x \<in> S. (cc'(a := c' a)) x *\<^sub>R x)"
        apply simp
        apply (rule sum.mono_neutral_left)
        using \<open>T \<subseteq> S\<close> apply (auto simp: \<open>a \<notin> S\<close> cc0)
        done
      also have "... = c a *\<^sub>R a + x - c a *\<^sub>R a"
        by (simp add: wsumSS \<open>a \<notin> S\<close> if_smult sum_delta_notmem)
      finally show "(\<Sum>x\<in>insert a (T \<inter> T'). (cc'(a := c' a)) x *\<^sub>R x) = x"
        by simp
    qed
  qed
qed

corollary convex_hull_exchange_Int:
  fixes a  :: "'a::euclidean_space"
  assumes "~ affine_dependent S" "a \<in> convex hull S" "T \<subseteq> S" "T' \<subseteq> S"
  shows "(convex hull (insert a T)) \<inter> (convex hull (insert a T')) =
         convex hull (insert a (T \<inter> T'))"
apply (rule subset_antisym)
  using in_convex_hull_exchange_unique assms apply blast
  by (metis hull_mono inf_le1 inf_le2 insert_inter_insert le_inf_iff)

lemma Int_closed_segment:
  fixes b :: "'a::euclidean_space"
  assumes "b \<in> closed_segment a c \<or> ~collinear{a,b,c}"
    shows "closed_segment a b \<inter> closed_segment b c = {b}"
proof (cases "c = a")
  case True
  then show ?thesis
    using assms collinear_3_eq_affine_dependent by fastforce
next
  case False
  from assms show ?thesis
  proof
    assume "b \<in> closed_segment a c"
    moreover have "\<not> affine_dependent {a, c}"
      by (simp add: affine_independent_2)
    ultimately show ?thesis
      using False convex_hull_exchange_Int [of "{a,c}" b "{a}" "{c}"]
      by (simp add: segment_convex_hull insert_commute)
  next
    assume ncoll: "\<not> collinear {a, b, c}"
    have False if "closed_segment a b \<inter> closed_segment b c \<noteq> {b}"
    proof -
      have "b \<in> closed_segment a b" and "b \<in> closed_segment b c"
        by auto
      with that obtain d where "b \<noteq> d" "d \<in> closed_segment a b" "d \<in> closed_segment b c"
        by force
      then have d: "collinear {a, d, b}"  "collinear {b, d, c}"
        by (auto simp:  between_mem_segment between_imp_collinear)
      have "collinear {a, b, c}"
        apply (rule collinear_3_trans [OF _ _ \<open>b \<noteq> d\<close>])
        using d  by (auto simp: insert_commute)
      with ncoll show False ..
    qed
    then show ?thesis
      by blast
  qed
qed

lemma affine_hull_finite_intersection_hyperplanes:
  fixes s :: "'a::euclidean_space set"
  obtains f where
     "finite f"
     "of_nat (card f) + aff_dim s = DIM('a)"
     "affine hull s = \<Inter>f"
     "\<And>h. h \<in> f \<Longrightarrow> \<exists>a b. a \<noteq> 0 \<and> h = {x. a \<bullet> x = b}"
proof -
  obtain b where "b \<subseteq> s"
             and indb: "\<not> affine_dependent b"
             and eq: "affine hull s = affine hull b"
    using affine_basis_exists by blast
  obtain c where indc: "\<not> affine_dependent c" and "b \<subseteq> c"
             and affc: "affine hull c = UNIV"
    by (metis extend_to_affine_basis affine_UNIV hull_same indb subset_UNIV)
  then have "finite c"
    by (simp add: aff_independent_finite)
  then have fbc: "finite b" "card b \<le> card c"
    using \<open>b \<subseteq> c\<close> infinite_super by (auto simp: card_mono)
  have imeq: "(\<lambda>x. affine hull x) ` ((\<lambda>a. c - {a}) ` (c - b)) = ((\<lambda>a. affine hull (c - {a})) ` (c - b))"
    by blast
  have card1: "card ((\<lambda>a. affine hull (c - {a})) ` (c - b)) = card (c - b)"
    apply (rule card_image [OF inj_onI])
    by (metis Diff_eq_empty_iff Diff_iff indc affine_dependent_def hull_subset insert_iff)
  have card2: "(card (c - b)) + aff_dim s = DIM('a)"
  proof -
    have aff: "aff_dim (UNIV::'a set) = aff_dim c"
      by (metis aff_dim_affine_hull affc)
    have "aff_dim b = aff_dim s"
      by (metis (no_types) aff_dim_affine_hull eq)
    then have "int (card b) = 1 + aff_dim s"
      by (simp add: aff_dim_affine_independent indb)
    then show ?thesis
      using fbc aff
      by (simp add: \<open>\<not> affine_dependent c\<close> \<open>b \<subseteq> c\<close> aff_dim_affine_independent aff_dim_UNIV card_Diff_subset of_nat_diff)
  qed
  show ?thesis
  proof (cases "c = b")
    case True show ?thesis
      apply (rule_tac f="{}" in that)
      using True affc
      apply (simp_all add: eq [symmetric])
      by (metis aff_dim_UNIV aff_dim_affine_hull)
  next
    case False
    have ind: "\<not> affine_dependent (\<Union>a\<in>c - b. c - {a})"
      by (rule affine_independent_subset [OF indc]) auto
    have affeq: "affine hull s = (\<Inter>x\<in>(\<lambda>a. c - {a}) ` (c - b). affine hull x)"
      using \<open>b \<subseteq> c\<close> False
      apply (subst affine_hull_Inter [OF ind, symmetric])
      apply (simp add: eq double_diff)
      done
    have *: "1 + aff_dim (c - {t}) = int (DIM('a))"
            if t: "t \<in> c" for t
    proof -
      have "insert t c = c"
        using t by blast
      then show ?thesis
        by (metis (full_types) add.commute aff_dim_affine_hull aff_dim_insert aff_dim_UNIV affc affine_dependent_def indc insert_Diff_single t)
    qed
    show ?thesis
      apply (rule_tac f = "(\<lambda>x. affine hull x) ` ((\<lambda>a. c - {a}) ` (c - b))" in that)
         using \<open>finite c\<close> apply blast
        apply (simp add: imeq card1 card2)
      apply (simp add: affeq, clarify)
      apply (metis DIM_positive One_nat_def Suc_leI add_diff_cancel_left' of_nat_1 aff_dim_eq_hyperplane of_nat_diff *)
      done
  qed
qed

subsection\<open>Misc results about span\<close>

lemma eq_span_insert_eq:
  assumes "(x - y) \<in> span S"
    shows "span(insert x S) = span(insert y S)"
proof -
  have *: "span(insert x S) \<subseteq> span(insert y S)" if "(x - y) \<in> span S" for x y
  proof -
    have 1: "(r *\<^sub>R x - r *\<^sub>R y) \<in> span S" for r
      by (metis real_vector.scale_right_diff_distrib span_mul that)
    have 2: "(z - k *\<^sub>R y) - k *\<^sub>R (x - y) = z - k *\<^sub>R x" for  z k
      by (simp add: real_vector.scale_right_diff_distrib)
  show ?thesis
    apply (clarsimp simp add: span_breakdown_eq)
    by (metis 1 2 diff_add_cancel real_vector.scale_right_diff_distrib span_add_eq)
  qed
  show ?thesis
    apply (intro subset_antisym * assms)
    using assms subspace_neg subspace_span minus_diff_eq by force
qed

lemma dim_psubset:
    fixes S :: "'a :: euclidean_space set"
    shows "span S \<subset> span T \<Longrightarrow> dim S < dim T"
by (metis (no_types, hide_lams) dim_span less_le not_le subspace_dim_equal subspace_span)


lemma basis_subspace_exists:
  fixes S :: "'a::euclidean_space set"
  shows
   "subspace S
        \<Longrightarrow> \<exists>b. finite b \<and> b \<subseteq> S \<and>
                independent b \<and> span b = S \<and> card b = dim S"
by (metis span_subspace basis_exists independent_imp_finite)

lemma affine_hyperplane_sums_eq_UNIV_0:
  fixes S :: "'a :: euclidean_space set"
  assumes "affine S"
     and "0 \<in> S" and "w \<in> S"
     and "a \<bullet> w \<noteq> 0"
   shows "{x + y| x y. x \<in> S \<and> a \<bullet> y = 0} = UNIV"
proof -
  have "subspace S"
    by (simp add: assms subspace_affine)
  have span1: "span {y. a \<bullet> y = 0} \<subseteq> span {x + y |x y. x \<in> S \<and> a \<bullet> y = 0}"
    apply (rule span_mono)
    using \<open>0 \<in> S\<close> add.left_neutral by force
  have "w \<notin> span {y. a \<bullet> y = 0}"
    using \<open>a \<bullet> w \<noteq> 0\<close> span_induct subspace_hyperplane by auto
  moreover have "w \<in> span {x + y |x y. x \<in> S \<and> a \<bullet> y = 0}"
    using \<open>w \<in> S\<close>
    by (metis (mono_tags, lifting) inner_zero_right mem_Collect_eq pth_d span_superset)
  ultimately have span2: "span {y. a \<bullet> y = 0} \<noteq> span {x + y |x y. x \<in> S \<and> a \<bullet> y = 0}"
    by blast
  have "a \<noteq> 0" using assms inner_zero_left by blast
  then have "DIM('a) - 1 = dim {y. a \<bullet> y = 0}"
    by (simp add: dim_hyperplane)
  also have "... < dim {x + y |x y. x \<in> S \<and> a \<bullet> y = 0}"
    using span1 span2 by (blast intro: dim_psubset)
  finally have DIM_lt: "DIM('a) - 1 < dim {x + y |x y. x \<in> S \<and> a \<bullet> y = 0}" .
  have subs: "subspace {x + y| x y. x \<in> S \<and> a \<bullet> y = 0}"
    using subspace_sums [OF \<open>subspace S\<close> subspace_hyperplane] by simp
  moreover have "span {x + y| x y. x \<in> S \<and> a \<bullet> y = 0} = UNIV"
    apply (rule dim_eq_full [THEN iffD1])
    apply (rule antisym [OF dim_subset_UNIV])
    using DIM_lt apply simp
    done
  ultimately show ?thesis
    by (simp add: subs) (metis (lifting) span_eq subs)
qed

proposition affine_hyperplane_sums_eq_UNIV:
  fixes S :: "'a :: euclidean_space set"
  assumes "affine S"
      and "S \<inter> {v. a \<bullet> v = b} \<noteq> {}"
      and "S - {v. a \<bullet> v = b} \<noteq> {}"
    shows "{x + y| x y. x \<in> S \<and> a \<bullet> y = b} = UNIV"
proof (cases "a = 0")
  case True with assms show ?thesis
    by (auto simp: if_splits)
next
  case False
  obtain c where "c \<in> S" and c: "a \<bullet> c = b"
    using assms by force
  with affine_diffs_subspace [OF \<open>affine S\<close>]
  have "subspace (op + (- c) ` S)" by blast
  then have aff: "affine (op + (- c) ` S)"
    by (simp add: subspace_imp_affine)
  have 0: "0 \<in> op + (- c) ` S"
    by (simp add: \<open>c \<in> S\<close>)
  obtain d where "d \<in> S" and "a \<bullet> d \<noteq> b" and dc: "d-c \<in> op + (- c) ` S"
    using assms by auto
  then have adc: "a \<bullet> (d - c) \<noteq> 0"
    by (simp add: c inner_diff_right)
  let ?U = "op + (c+c) ` {x + y |x y. x \<in> op + (- c) ` S \<and> a \<bullet> y = 0}"
  have "u + v \<in> op + (c + c) ` {x + v |x v. x \<in> op + (- c) ` S \<and> a \<bullet> v = 0}"
              if "u \<in> S" "b = a \<bullet> v" for u v
    apply (rule_tac x="u+v-c-c" in image_eqI)
    apply (simp_all add: algebra_simps)
    apply (rule_tac x="u-c" in exI)
    apply (rule_tac x="v-c" in exI)
    apply (simp add: algebra_simps that c)
    done
  moreover have "\<lbrakk>a \<bullet> v = 0; u \<in> S\<rbrakk>
       \<Longrightarrow> \<exists>x ya. v + (u + c) = x + ya \<and> x \<in> S \<and> a \<bullet> ya = b" for v u
    by (metis add.left_commute c inner_right_distrib pth_d)
  ultimately have "{x + y |x y. x \<in> S \<and> a \<bullet> y = b} = ?U"
    by (fastforce simp: algebra_simps)
  also have "... = op + (c+c) ` UNIV"
    by (simp add: affine_hyperplane_sums_eq_UNIV_0 [OF aff 0 dc adc])
  also have "... = UNIV"
    by (simp add: translation_UNIV)
  finally show ?thesis .
qed

proposition dim_sums_Int:
    fixes S :: "'a :: euclidean_space set"
  assumes "subspace S" "subspace T"
  shows "dim {x + y |x y. x \<in> S \<and> y \<in> T} + dim(S \<inter> T) = dim S + dim T"
proof -
  obtain B where B: "B \<subseteq> S \<inter> T" "S \<inter> T \<subseteq> span B"
             and indB: "independent B"
             and cardB: "card B = dim (S \<inter> T)"
    using basis_exists by blast
  then obtain C D where "B \<subseteq> C" "C \<subseteq> S" "independent C" "S \<subseteq> span C"
                    and "B \<subseteq> D" "D \<subseteq> T" "independent D" "T \<subseteq> span D"
    using maximal_independent_subset_extend
    by (metis Int_subset_iff \<open>B \<subseteq> S \<inter> T\<close> indB)
  then have "finite B" "finite C" "finite D"
    by (simp_all add: independent_imp_finite indB independent_bound)
  have Beq: "B = C \<inter> D"
    apply (rule sym)
    apply (rule spanning_subset_independent)
    using \<open>B \<subseteq> C\<close> \<open>B \<subseteq> D\<close> apply blast
    apply (meson \<open>independent C\<close> independent_mono inf.cobounded1)
    using B \<open>C \<subseteq> S\<close> \<open>D \<subseteq> T\<close> apply auto
    done
  then have Deq: "D = B \<union> (D - C)"
    by blast
  have CUD: "C \<union> D \<subseteq> {x + y |x y. x \<in> S \<and> y \<in> T}"
    apply safe
    apply (metis add.right_neutral subsetCE \<open>C \<subseteq> S\<close> \<open>subspace T\<close> set_eq_subset span_0 span_minimal)
    apply (metis add.left_neutral subsetCE \<open>D \<subseteq> T\<close> \<open>subspace S\<close> set_eq_subset span_0 span_minimal)
    done
  have "a v = 0" if 0: "(\<Sum>v\<in>C. a v *\<^sub>R v) + (\<Sum>v\<in>D - C. a v *\<^sub>R v) = 0"
                 and v: "v \<in> C \<union> (D-C)" for a v
  proof -
    have eq: "(\<Sum>v\<in>D - C. a v *\<^sub>R v) = - (\<Sum>v\<in>C. a v *\<^sub>R v)"
      using that add_eq_0_iff by blast
    have "(\<Sum>v\<in>D - C. a v *\<^sub>R v) \<in> S"
      apply (subst eq)
      apply (rule subspace_neg [OF \<open>subspace S\<close>])
      apply (rule subspace_sum [OF \<open>subspace S\<close>])
      by (meson subsetCE subspace_mul \<open>C \<subseteq> S\<close> \<open>subspace S\<close>)
    moreover have "(\<Sum>v\<in>D - C. a v *\<^sub>R v) \<in> T"
      apply (rule subspace_sum [OF \<open>subspace T\<close>])
      by (meson DiffD1 \<open>D \<subseteq> T\<close> \<open>subspace T\<close> subset_eq subspace_def)
    ultimately have "(\<Sum>v \<in> D-C. a v *\<^sub>R v) \<in> span B"
      using B by blast
    then obtain e where e: "(\<Sum>v\<in>B. e v *\<^sub>R v) = (\<Sum>v \<in> D-C. a v *\<^sub>R v)"
      using span_finite [OF \<open>finite B\<close>] by blast
    have "\<And>c v. \<lbrakk>(\<Sum>v\<in>C. c v *\<^sub>R v) = 0; v \<in> C\<rbrakk> \<Longrightarrow> c v = 0"
      using independent_explicit \<open>independent C\<close> by blast
    define cc where "cc x = (if x \<in> B then a x + e x else a x)" for x
    have [simp]: "C \<inter> B = B" "D \<inter> B = B" "C \<inter> - B = C-D" "B \<inter> (D - C) = {}"
      using \<open>B \<subseteq> C\<close> \<open>B \<subseteq> D\<close> Beq by blast+
    have f2: "(\<Sum>v\<in>C \<inter> D. e v *\<^sub>R v) = (\<Sum>v\<in>D - C. a v *\<^sub>R v)"
      using Beq e by presburger
    have f3: "(\<Sum>v\<in>C \<union> D. a v *\<^sub>R v) = (\<Sum>v\<in>C - D. a v *\<^sub>R v) + (\<Sum>v\<in>D - C. a v *\<^sub>R v) + (\<Sum>v\<in>C \<inter> D. a v *\<^sub>R v)"
      using \<open>finite C\<close> \<open>finite D\<close> sum.union_diff2 by blast
    have f4: "(\<Sum>v\<in>C \<union> (D - C). a v *\<^sub>R v) = (\<Sum>v\<in>C. a v *\<^sub>R v) + (\<Sum>v\<in>D - C. a v *\<^sub>R v)"
      by (meson Diff_disjoint \<open>finite C\<close> \<open>finite D\<close> finite_Diff sum.union_disjoint)
    have "(\<Sum>v\<in>C. cc v *\<^sub>R v) = 0"
      using 0 f2 f3 f4
      apply (simp add: cc_def Beq if_smult \<open>finite C\<close> sum.If_cases algebra_simps sum.distrib)
      apply (simp add: add.commute add.left_commute diff_eq)
      done
    then have "\<And>v. v \<in> C \<Longrightarrow> cc v = 0"
      using independent_explicit \<open>independent C\<close> by blast
    then have C0: "\<And>v. v \<in> C - B \<Longrightarrow> a v = 0"
      by (simp add: cc_def Beq) meson
    then have [simp]: "(\<Sum>x\<in>C - B. a x *\<^sub>R x) = 0"
      by simp
    have "(\<Sum>x\<in>C. a x *\<^sub>R x) = (\<Sum>x\<in>B. a x *\<^sub>R x)"
    proof -
      have "C - D = C - B"
        using Beq by blast
      then show ?thesis
        using Beq \<open>(\<Sum>x\<in>C - B. a x *\<^sub>R x) = 0\<close> f3 f4 by auto
    qed
    with 0 have Dcc0: "(\<Sum>v\<in>D. a v *\<^sub>R v) = 0"
      apply (subst Deq)
      by (simp add: \<open>finite B\<close> \<open>finite D\<close> sum_Un)
    then have D0: "\<And>v. v \<in> D \<Longrightarrow> a v = 0"
      using independent_explicit \<open>independent D\<close> by blast
    show ?thesis
      using v C0 D0 Beq by blast
  qed
  then have "independent (C \<union> (D - C))"
    by (simp add: independent_explicit \<open>finite C\<close> \<open>finite D\<close> sum_Un del: Un_Diff_cancel)
  then have indCUD: "independent (C \<union> D)" by simp
  have "dim (S \<inter> T) = card B"
    by (rule dim_unique [OF B indB refl])
  moreover have "dim S = card C"
    by (metis \<open>C \<subseteq> S\<close> \<open>independent C\<close> \<open>S \<subseteq> span C\<close> basis_card_eq_dim)
  moreover have "dim T = card D"
    by (metis \<open>D \<subseteq> T\<close> \<open>independent D\<close> \<open>T \<subseteq> span D\<close> basis_card_eq_dim)
  moreover have "dim {x + y |x y. x \<in> S \<and> y \<in> T} = card(C \<union> D)"
    apply (rule dim_unique [OF CUD _ indCUD refl], clarify)
    apply (meson \<open>S \<subseteq> span C\<close> \<open>T \<subseteq> span D\<close> span_add span_inc span_minimal subsetCE subspace_span sup.bounded_iff)
    done
  ultimately show ?thesis
    using \<open>B = C \<inter> D\<close> [symmetric]
    by (simp add:  \<open>independent C\<close> \<open>independent D\<close> card_Un_Int independent_finite)
qed


lemma aff_dim_sums_Int_0:
  assumes "affine S"
      and "affine T"
      and "0 \<in> S" "0 \<in> T"
    shows "aff_dim {x + y| x y. x \<in> S \<and> y \<in> T} = (aff_dim S + aff_dim T) - aff_dim(S \<inter> T)"
proof -
  have "0 \<in> {x + y |x y. x \<in> S \<and> y \<in> T}"
    using assms by force
  then have 0: "0 \<in> affine hull {x + y |x y. x \<in> S \<and> y \<in> T}"
    by (metis (lifting) hull_inc)
  have sub: "subspace S"  "subspace T"
    using assms by (auto simp: subspace_affine)
  show ?thesis
    using dim_sums_Int [OF sub] by (simp add: aff_dim_zero assms 0 hull_inc)
qed

proposition aff_dim_sums_Int:
  assumes "affine S"
      and "affine T"
      and "S \<inter> T \<noteq> {}"
    shows "aff_dim {x + y| x y. x \<in> S \<and> y \<in> T} = (aff_dim S + aff_dim T) - aff_dim(S \<inter> T)"
proof -
  obtain a where a: "a \<in> S" "a \<in> T" using assms by force
  have aff: "affine (op+ (-a) ` S)"  "affine (op+ (-a) ` T)"
    using assms by (auto simp: affine_translation [symmetric])
  have zero: "0 \<in> (op+ (-a) ` S)"  "0 \<in> (op+ (-a) ` T)"
    using a assms by auto
  have [simp]: "{x + y |x y. x \<in> op + (- a) ` S \<and> y \<in> op + (- a) ` T} =
        op + (- 2 *\<^sub>R a) ` {x + y| x y. x \<in> S \<and> y \<in> T}"
    by (force simp: algebra_simps scaleR_2)
  have [simp]: "op + (- a) ` S \<inter> op + (- a) ` T = op + (- a) ` (S \<inter> T)"
    by auto
  show ?thesis
    using aff_dim_sums_Int_0 [OF aff zero]
    by (auto simp: aff_dim_translation_eq)
qed

lemma aff_dim_affine_Int_hyperplane:
  fixes a :: "'a::euclidean_space"
  assumes "affine S"
    shows "aff_dim(S \<inter> {x. a \<bullet> x = b}) =
             (if S \<inter> {v. a \<bullet> v = b} = {} then - 1
              else if S \<subseteq> {v. a \<bullet> v = b} then aff_dim S
              else aff_dim S - 1)"
proof (cases "a = 0")
  case True with assms show ?thesis
    by auto
next
  case False
  then have "aff_dim (S \<inter> {x. a \<bullet> x = b}) = aff_dim S - 1"
            if "x \<in> S" "a \<bullet> x \<noteq> b" and non: "S \<inter> {v. a \<bullet> v = b} \<noteq> {}" for x
  proof -
    have [simp]: "{x + y| x y. x \<in> S \<and> a \<bullet> y = b} = UNIV"
      using affine_hyperplane_sums_eq_UNIV [OF assms non] that  by blast
    show ?thesis
      using aff_dim_sums_Int [OF assms affine_hyperplane non]
      by (simp add: of_nat_diff False)
  qed
  then show ?thesis
    by (metis (mono_tags, lifting) inf.orderE aff_dim_empty_eq mem_Collect_eq subsetI)
qed

lemma aff_dim_lt_full:
  fixes S :: "'a::euclidean_space set"
  shows "aff_dim S < DIM('a) \<longleftrightarrow> (affine hull S \<noteq> UNIV)"
by (metis (no_types) aff_dim_affine_hull aff_dim_le_DIM aff_dim_UNIV affine_hull_UNIV less_le)


lemma dim_Times:
  fixes S :: "'a :: euclidean_space set" and T :: "'a set"
  assumes "subspace S" "subspace T"
  shows "dim(S \<times> T) = dim S + dim T"
proof -
  have ss: "subspace ((\<lambda>x. (x, 0)) ` S)" "subspace (Pair 0 ` T)"
    by (rule subspace_linear_image, unfold_locales, auto simp: assms)+
  have "dim(S \<times> T) = dim({u + v |u v. u \<in> (\<lambda>x. (x, 0)) ` S \<and> v \<in> Pair 0 ` T})"
    by (simp add: Times_eq_image_sum)
  moreover have "dim ((\<lambda>x. (x, 0::'a)) ` S) = dim S" "dim (Pair (0::'a) ` T) = dim T"
    by (auto simp: additive.intro linear.intro linear_axioms.intro inj_on_def intro: dim_image_eq)
  moreover have "dim ((\<lambda>x. (x, 0)) ` S \<inter> Pair 0 ` T) = 0"
    by (subst dim_eq_0) (force simp: zero_prod_def)
  ultimately show ?thesis
    using dim_sums_Int [OF ss] by linarith
qed

subsection\<open> Orthogonal bases, Gram-Schmidt process, and related theorems\<close>

lemma span_delete_0 [simp]: "span(S - {0}) = span S"
proof
  show "span (S - {0}) \<subseteq> span S"
    by (blast intro!: span_mono)
next
  have "span S \<subseteq> span(insert 0 (S - {0}))"
    by (blast intro!: span_mono)
  also have "... \<subseteq> span(S - {0})"
    using span_insert_0 by blast
  finally show "span S \<subseteq> span (S - {0})" .
qed

lemma span_image_scale:
  assumes "finite S" and nz: "\<And>x. x \<in> S \<Longrightarrow> c x \<noteq> 0"
    shows "span ((\<lambda>x. c x *\<^sub>R x) ` S) = span S"
using assms
proof (induction S arbitrary: c)
  case (empty c) show ?case by simp
next
  case (insert x F c)
  show ?case
  proof (intro set_eqI iffI)
    fix y
      assume "y \<in> span ((\<lambda>x. c x *\<^sub>R x) ` insert x F)"
      then show "y \<in> span (insert x F)"
        using insert by (force simp: span_breakdown_eq)
  next
    fix y
      assume "y \<in> span (insert x F)"
      then show "y \<in> span ((\<lambda>x. c x *\<^sub>R x) ` insert x F)"
        using insert
        apply (clarsimp simp: span_breakdown_eq)
        apply (rule_tac x="k / c x" in exI)
        by simp
  qed
qed

lemma pairwise_orthogonal_independent:
  assumes "pairwise orthogonal S" and "0 \<notin> S"
    shows "independent S"
proof -
  have 0: "\<And>x y. \<lbrakk>x \<noteq> y; x \<in> S; y \<in> S\<rbrakk> \<Longrightarrow> x \<bullet> y = 0"
    using assms by (simp add: pairwise_def orthogonal_def)
  have "False" if "a \<in> S" and a: "a \<in> span (S - {a})" for a
  proof -
    obtain T U where "T \<subseteq> S - {a}" "a = (\<Sum>v\<in>T. U v *\<^sub>R v)"
      using a by (force simp: span_explicit)
    then have "a \<bullet> a = a \<bullet> (\<Sum>v\<in>T. U v *\<^sub>R v)"
      by simp
    also have "... = 0"
      apply (simp add: inner_sum_right)
      apply (rule comm_monoid_add_class.sum.neutral)
      by (metis "0" DiffE \<open>T \<subseteq> S - {a}\<close> mult_not_zero singletonI subsetCE \<open>a \<in> S\<close>)
    finally show ?thesis
      using \<open>0 \<notin> S\<close> \<open>a \<in> S\<close> by auto
  qed
  then show ?thesis
    by (force simp: dependent_def)
qed

lemma pairwise_orthogonal_imp_finite:
  fixes S :: "'a::euclidean_space set"
  assumes "pairwise orthogonal S"
    shows "finite S"
proof -
  have "independent (S - {0})"
    apply (rule pairwise_orthogonal_independent)
     apply (metis Diff_iff assms pairwise_def)
    by blast
  then show ?thesis
    by (meson independent_imp_finite infinite_remove)
qed

lemma subspace_orthogonal_to_vector: "subspace {y. orthogonal x y}"
  by (simp add: subspace_def orthogonal_clauses)

lemma subspace_orthogonal_to_vectors: "subspace {y. \<forall>x \<in> S. orthogonal x y}"
  by (simp add: subspace_def orthogonal_clauses)

lemma orthogonal_to_span:
  assumes a: "a \<in> span S" and x: "\<And>y. y \<in> S \<Longrightarrow> orthogonal x y"
    shows "orthogonal x a"
apply (rule span_induct [OF a subspace_orthogonal_to_vector])
apply (simp add: x)
done

proposition Gram_Schmidt_step:
  fixes S :: "'a::euclidean_space set"
  assumes S: "pairwise orthogonal S" and x: "x \<in> span S"
    shows "orthogonal x (a - (\<Sum>b\<in>S. (b \<bullet> a / (b \<bullet> b)) *\<^sub>R b))"
proof -
  have "finite S"
    by (simp add: S pairwise_orthogonal_imp_finite)
  have "orthogonal (a - (\<Sum>b\<in>S. (b \<bullet> a / (b \<bullet> b)) *\<^sub>R b)) x"
       if "x \<in> S" for x
  proof -
    have "a \<bullet> x = (\<Sum>y\<in>S. if y = x then y \<bullet> a else 0)"
      by (simp add: \<open>finite S\<close> inner_commute sum.delta that)
    also have "... =  (\<Sum>b\<in>S. b \<bullet> a * (b \<bullet> x) / (b \<bullet> b))"
      apply (rule sum.cong [OF refl], simp)
      by (meson S orthogonal_def pairwise_def that)
   finally show ?thesis
     by (simp add: orthogonal_def algebra_simps inner_sum_left)
  qed
  then show ?thesis
    using orthogonal_to_span orthogonal_commute x by blast
qed


lemma orthogonal_extension_aux:
  fixes S :: "'a::euclidean_space set"
  assumes "finite T" "finite S" "pairwise orthogonal S"
    shows "\<exists>U. pairwise orthogonal (S \<union> U) \<and> span (S \<union> U) = span (S \<union> T)"
using assms
proof (induction arbitrary: S)
  case empty then show ?case
    by simp (metis sup_bot_right)
next
  case (insert a T)
  have 0: "\<And>x y. \<lbrakk>x \<noteq> y; x \<in> S; y \<in> S\<rbrakk> \<Longrightarrow> x \<bullet> y = 0"
    using insert by (simp add: pairwise_def orthogonal_def)
  define a' where "a' = a - (\<Sum>b\<in>S. (b \<bullet> a / (b \<bullet> b)) *\<^sub>R b)"
  obtain U where orthU: "pairwise orthogonal (S \<union> insert a' U)"
             and spanU: "span (insert a' S \<union> U) = span (insert a' S \<union> T)"
    apply (rule exE [OF insert.IH [of "insert a' S"]])
    apply (auto simp: Gram_Schmidt_step a'_def insert.prems orthogonal_commute pairwise_orthogonal_insert span_clauses)
    done
  have orthS: "\<And>x. x \<in> S \<Longrightarrow> a' \<bullet> x = 0"
    apply (simp add: a'_def)
    using Gram_Schmidt_step [OF \<open>pairwise orthogonal S\<close>]
    apply (force simp: orthogonal_def inner_commute span_inc [THEN subsetD])
    done
  have "span (S \<union> insert a' U) = span (insert a' (S \<union> T))"
    using spanU by simp
  also have "... = span (insert a (S \<union> T))"
    apply (rule eq_span_insert_eq)
    apply (simp add: a'_def span_neg span_sum span_clauses(1) span_mul)
    done
  also have "... = span (S \<union> insert a T)"
    by simp
  finally show ?case
    apply (rule_tac x="insert a' U" in exI)
    using orthU apply auto
    done
qed


proposition orthogonal_extension:
  fixes S :: "'a::euclidean_space set"
  assumes S: "pairwise orthogonal S"
  obtains U where "pairwise orthogonal (S \<union> U)" "span (S \<union> U) = span (S \<union> T)"
proof -
  obtain B where "finite B" "span B = span T"
    using basis_subspace_exists [of "span T"] subspace_span by auto
  with orthogonal_extension_aux [of B S]
  obtain U where "pairwise orthogonal (S \<union> U)" "span (S \<union> U) = span (S \<union> B)"
    using assms pairwise_orthogonal_imp_finite by auto
  show ?thesis
    apply (rule_tac U=U in that)
     apply (simp add: \<open>pairwise orthogonal (S \<union> U)\<close>)
    by (metis \<open>span (S \<union> U) = span (S \<union> B)\<close> \<open>span B = span T\<close> span_Un)
qed

corollary orthogonal_extension_strong:
  fixes S :: "'a::euclidean_space set"
  assumes S: "pairwise orthogonal S"
  obtains U where "U \<inter> (insert 0 S) = {}" "pairwise orthogonal (S \<union> U)"
                   "span (S \<union> U) = span (S \<union> T)"
proof -
  obtain U where "pairwise orthogonal (S \<union> U)" "span (S \<union> U) = span (S \<union> T)"
    using orthogonal_extension assms by blast
  then show ?thesis
    apply (rule_tac U = "U - (insert 0 S)" in that)
      apply blast
     apply (force simp: pairwise_def)
    apply (metis (no_types, lifting) Un_Diff_cancel span_insert_0 span_Un)
  done
qed

subsection\<open>Decomposing a vector into parts in orthogonal subspaces.\<close>

text\<open>existence of orthonormal basis for a subspace.\<close>

lemma orthogonal_spanningset_subspace:
  fixes S :: "'a :: euclidean_space set"
  assumes "subspace S"
  obtains B where "B \<subseteq> S" "pairwise orthogonal B" "span B = S"
proof -
  obtain B where "B \<subseteq> S" "independent B" "S \<subseteq> span B" "card B = dim S"
    using basis_exists by blast
  with orthogonal_extension [of "{}" B]
  show ?thesis
    by (metis Un_empty_left assms pairwise_empty span_inc span_subspace that)
qed

lemma orthogonal_basis_subspace:
  fixes S :: "'a :: euclidean_space set"
  assumes "subspace S"
  obtains B where "0 \<notin> B" "B \<subseteq> S" "pairwise orthogonal B" "independent B"
                  "card B = dim S" "span B = S"
proof -
  obtain B where "B \<subseteq> S" "pairwise orthogonal B" "span B = S"
    using assms orthogonal_spanningset_subspace by blast
  then show ?thesis
    apply (rule_tac B = "B - {0}" in that)
    apply (auto simp: indep_card_eq_dim_span pairwise_subset Diff_subset pairwise_orthogonal_independent elim: pairwise_subset)
    done
qed

proposition orthonormal_basis_subspace:
  fixes S :: "'a :: euclidean_space set"
  assumes "subspace S"
  obtains B where "B \<subseteq> S" "pairwise orthogonal B"
              and "\<And>x. x \<in> B \<Longrightarrow> norm x = 1"
              and "independent B" "card B = dim S" "span B = S"
proof -
  obtain B where "0 \<notin> B" "B \<subseteq> S"
             and orth: "pairwise orthogonal B"
             and "independent B" "card B = dim S" "span B = S"
    by (blast intro: orthogonal_basis_subspace [OF assms])
  have 1: "(\<lambda>x. x /\<^sub>R norm x) ` B \<subseteq> S"
    using \<open>span B = S\<close> span_clauses(1) span_mul by fastforce
  have 2: "pairwise orthogonal ((\<lambda>x. x /\<^sub>R norm x) ` B)"
    using orth by (force simp: pairwise_def orthogonal_clauses)
  have 3: "\<And>x. x \<in> (\<lambda>x. x /\<^sub>R norm x) ` B \<Longrightarrow> norm x = 1"
    by (metis (no_types, lifting) \<open>0 \<notin> B\<close> image_iff norm_sgn sgn_div_norm)
  have 4: "independent ((\<lambda>x. x /\<^sub>R norm x) ` B)"
    by (metis "2" "3" norm_zero pairwise_orthogonal_independent zero_neq_one)
  have "inj_on (\<lambda>x. x /\<^sub>R norm x) B"
  proof
    fix x y
    assume "x \<in> B" "y \<in> B" "x /\<^sub>R norm x = y /\<^sub>R norm y"
    moreover have "\<And>i. i \<in> B \<Longrightarrow> norm (i /\<^sub>R norm i) = 1"
      using 3 by blast
    ultimately show "x = y"
      by (metis norm_eq_1 orth orthogonal_clauses(7) orthogonal_commute orthogonal_def pairwise_def zero_neq_one)
  qed
  then have 5: "card ((\<lambda>x. x /\<^sub>R norm x) ` B) = dim S"
    by (metis \<open>card B = dim S\<close> card_image)
  have 6: "span ((\<lambda>x. x /\<^sub>R norm x) ` B) = S"
    by (metis "1" "4" "5" assms card_eq_dim independent_finite span_subspace)
  show ?thesis
    by (rule that [OF 1 2 3 4 5 6])
qed

proposition orthogonal_subspace_decomp_exists:
  fixes S :: "'a :: euclidean_space set"
  obtains y z where "y \<in> span S" "\<And>w. w \<in> span S \<Longrightarrow> orthogonal z w" "x = y + z"
proof -
  obtain T where "0 \<notin> T" "T \<subseteq> span S" "pairwise orthogonal T" "independent T" "card T = dim (span S)" "span T = span S"
    using orthogonal_basis_subspace subspace_span by blast
  let ?a = "\<Sum>b\<in>T. (b \<bullet> x / (b \<bullet> b)) *\<^sub>R b"
  have orth: "orthogonal (x - ?a) w" if "w \<in> span S" for w
    by (simp add: Gram_Schmidt_step \<open>pairwise orthogonal T\<close> \<open>span T = span S\<close> orthogonal_commute that)
  show ?thesis
    apply (rule_tac y = "?a" and z = "x - ?a" in that)
      apply (meson \<open>T \<subseteq> span S\<close> span_mul span_sum subsetCE)
     apply (fact orth, simp)
    done
qed

lemma orthogonal_subspace_decomp_unique:
  fixes S :: "'a :: euclidean_space set"
  assumes "x + y = x' + y'"
      and ST: "x \<in> span S" "x' \<in> span S" "y \<in> span T" "y' \<in> span T"
      and orth: "\<And>a b. \<lbrakk>a \<in> S; b \<in> T\<rbrakk> \<Longrightarrow> orthogonal a b"
  shows "x = x' \<and> y = y'"
proof -
  have "x + y - y' = x'"
    by (simp add: assms)
  moreover have "\<And>a b. \<lbrakk>a \<in> span S; b \<in> span T\<rbrakk> \<Longrightarrow> orthogonal a b"
    by (meson orth orthogonal_commute orthogonal_to_span)
  ultimately have "0 = x' - x"
    by (metis (full_types) add_diff_cancel_left' ST diff_right_commute orthogonal_clauses(10) orthogonal_clauses(5) orthogonal_self)
  with assms show ?thesis by auto
qed

proposition dim_orthogonal_sum:
  fixes A :: "'a::euclidean_space set"
  assumes "\<And>x y. \<lbrakk>x \<in> A; y \<in> B\<rbrakk> \<Longrightarrow> x \<bullet> y = 0"
    shows "dim(A \<union> B) = dim A + dim B"
proof -
  have 1: "\<And>x y. \<lbrakk>x \<in> span A; y \<in> B\<rbrakk> \<Longrightarrow> x \<bullet> y = 0"
    by (erule span_induct [OF _ subspace_hyperplane2]; simp add: assms)
  have "\<And>x y. \<lbrakk>x \<in> span A; y \<in> span B\<rbrakk> \<Longrightarrow> x \<bullet> y = 0"
    apply (erule span_induct [OF _ subspace_hyperplane])
    using 1 by (simp add: )
  then have 0: "\<And>x y. \<lbrakk>x \<in> span A; y \<in> span B\<rbrakk> \<Longrightarrow> x \<bullet> y = 0"
    by simp
  have "dim(A \<union> B) = dim (span (A \<union> B))"
    by simp
  also have "... = dim ((\<lambda>(a, b). a + b) ` (span A \<times> span B))"
    by (simp add: span_Un)
  also have "... = dim {x + y |x y. x \<in> span A \<and> y \<in> span B}"
    by (auto intro!: arg_cong [where f=dim])
  also have "... = dim {x + y |x y. x \<in> span A \<and> y \<in> span B} + dim(span A \<inter> span B)"
    by (auto simp: dest: 0)
  also have "... = dim (span A) + dim (span B)"
    by (rule dim_sums_Int) auto
  also have "... = dim A + dim B"
    by simp
  finally show ?thesis .
qed

lemma dim_subspace_orthogonal_to_vectors:
  fixes A :: "'a::euclidean_space set"
  assumes "subspace A" "subspace B" "A \<subseteq> B"
    shows "dim {y \<in> B. \<forall>x \<in> A. orthogonal x y} + dim A = dim B"
proof -
  have "dim (span ({y \<in> B. \<forall>x\<in>A. orthogonal x y} \<union> A)) = dim (span B)"
  proof (rule arg_cong [where f=dim, OF subset_antisym])
    show "span ({y \<in> B. \<forall>x\<in>A. orthogonal x y} \<union> A) \<subseteq> span B"
      by (simp add: \<open>A \<subseteq> B\<close> Collect_restrict span_mono)
  next
    have *: "x \<in> span ({y \<in> B. \<forall>x\<in>A. orthogonal x y} \<union> A)"
         if "x \<in> B" for x
    proof -
      obtain y z where "x = y + z" "y \<in> span A" and orth: "\<And>w. w \<in> span A \<Longrightarrow> orthogonal z w"
        using orthogonal_subspace_decomp_exists [of A x] that by auto
      have "y \<in> span B"
        by (metis span_eq \<open>y \<in> span A\<close> assms subset_iff)
      then have "z \<in> {a \<in> B. \<forall>x. x \<in> A \<longrightarrow> orthogonal x a}"
        by simp (metis (no_types) span_eq \<open>x = y + z\<close> \<open>subspace A\<close> \<open>subspace B\<close> orth orthogonal_commute span_add_eq that)
      then have z: "z \<in> span {y \<in> B. \<forall>x\<in>A. orthogonal x y}"
        by (meson span_inc subset_iff)
      then show ?thesis
        apply (simp add: span_Un image_def)
        apply (rule bexI [OF _ z])
        apply (simp add: \<open>x = y + z\<close> \<open>y \<in> span A\<close>)
        done
    qed
    show "span B \<subseteq> span ({y \<in> B. \<forall>x\<in>A. orthogonal x y} \<union> A)"
      by (rule span_minimal) (auto intro: * span_minimal elim: )
  qed
  then show ?thesis
    by (metis (no_types, lifting) dim_orthogonal_sum dim_span mem_Collect_eq orthogonal_commute orthogonal_def)
qed

lemma aff_dim_openin:
  fixes S :: "'a::euclidean_space set"
  assumes ope: "openin (subtopology euclidean T) S" and "affine T" "S \<noteq> {}"
  shows "aff_dim S = aff_dim T"
proof -
  show ?thesis
  proof (rule order_antisym)
    show "aff_dim S \<le> aff_dim T"
      by (blast intro: aff_dim_subset [OF openin_imp_subset] ope)
  next
    obtain a where "a \<in> S"
      using \<open>S \<noteq> {}\<close> by blast
    have "S \<subseteq> T"
      using ope openin_imp_subset by auto
    then have "a \<in> T"
      using \<open>a \<in> S\<close> by auto
    then have subT': "subspace ((\<lambda>x. - a + x) ` T)"
      using affine_diffs_subspace \<open>affine T\<close> by auto
    then obtain B where Bsub: "B \<subseteq> ((\<lambda>x. - a + x) ` T)" and po: "pairwise orthogonal B"
                    and eq1: "\<And>x. x \<in> B \<Longrightarrow> norm x = 1" and "independent B"
                    and cardB: "card B = dim ((\<lambda>x. - a + x) ` T)"
                    and spanB: "span B = ((\<lambda>x. - a + x) ` T)"
      by (rule orthonormal_basis_subspace) auto
    obtain e where "0 < e" and e: "cball a e \<inter> T \<subseteq> S"
      by (meson \<open>a \<in> S\<close> openin_contains_cball ope)
    have "aff_dim T = aff_dim ((\<lambda>x. - a + x) ` T)"
      by (metis aff_dim_translation_eq)
    also have "... = dim ((\<lambda>x. - a + x) ` T)"
      using aff_dim_subspace subT' by blast
    also have "... = card B"
      by (simp add: cardB)
    also have "... = card ((\<lambda>x. e *\<^sub>R x) ` B)"
      using \<open>0 < e\<close>  by (force simp: inj_on_def card_image)
    also have "... \<le> dim ((\<lambda>x. - a + x) ` S)"
    proof (simp, rule independent_card_le_dim)
      have e': "cball 0 e \<inter> (\<lambda>x. x - a) ` T \<subseteq> (\<lambda>x. x - a) ` S"
        using e by (auto simp: dist_norm norm_minus_commute subset_eq)
      have "(\<lambda>x. e *\<^sub>R x) ` B \<subseteq> cball 0 e \<inter> (\<lambda>x. x - a) ` T"
        using Bsub \<open>0 < e\<close> eq1 subT' \<open>a \<in> T\<close> by (auto simp: subspace_def)
      then show "(\<lambda>x. e *\<^sub>R x) ` B \<subseteq> (\<lambda>x. x - a) ` S"
        using e' by blast
      show "independent ((\<lambda>x. e *\<^sub>R x) ` B)"
        using \<open>independent B\<close>
        apply (rule independent_injective_image, simp)
        by (metis \<open>0 < e\<close> injective_scaleR less_irrefl)
    qed
    also have "... = aff_dim S"
      using \<open>a \<in> S\<close> aff_dim_eq_dim hull_inc by force
    finally show "aff_dim T \<le> aff_dim S" .
  qed
qed

lemma dim_openin:
  fixes S :: "'a::euclidean_space set"
  assumes ope: "openin (subtopology euclidean T) S" and "subspace T" "S \<noteq> {}"
  shows "dim S = dim T"
proof (rule order_antisym)
  show "dim S \<le> dim T"
    by (metis ope dim_subset openin_subset topspace_euclidean_subtopology)
next
  have "dim T = aff_dim S"
    using aff_dim_openin
    by (metis aff_dim_subspace \<open>subspace T\<close> \<open>S \<noteq> {}\<close> ope subspace_affine)
  also have "... \<le> dim S"
    by (metis aff_dim_subset aff_dim_subspace dim_span span_inc subspace_span)
  finally show "dim T \<le> dim S" by simp
qed

subsection\<open>Parallel slices, etc.\<close>

text\<open> If we take a slice out of a set, we can do it perpendicularly,
  with the normal vector to the slice parallel to the affine hull.\<close>

proposition affine_parallel_slice:
  fixes S :: "'a :: euclidean_space set"
  assumes "affine S"
      and "S \<inter> {x. a \<bullet> x \<le> b} \<noteq> {}"
      and "~ (S \<subseteq> {x. a \<bullet> x \<le> b})"
  obtains a' b' where "a' \<noteq> 0"
                   "S \<inter> {x. a' \<bullet> x \<le> b'} = S \<inter> {x. a \<bullet> x \<le> b}"
                   "S \<inter> {x. a' \<bullet> x = b'} = S \<inter> {x. a \<bullet> x = b}"
                   "\<And>w. w \<in> S \<Longrightarrow> (w + a') \<in> S"
proof (cases "S \<inter> {x. a \<bullet> x = b} = {}")
  case True
  then obtain u v where "u \<in> S" "v \<in> S" "a \<bullet> u \<le> b" "a \<bullet> v > b"
    using assms by (auto simp: not_le)
  define \<eta> where "\<eta> = u + ((b - a \<bullet> u) / (a \<bullet> v - a \<bullet> u)) *\<^sub>R (v - u)"
  have "\<eta> \<in> S"
    by (simp add: \<eta>_def \<open>u \<in> S\<close> \<open>v \<in> S\<close> \<open>affine S\<close> mem_affine_3_minus)
  moreover have "a \<bullet> \<eta> = b"
    using \<open>a \<bullet> u \<le> b\<close> \<open>b < a \<bullet> v\<close>
    by (simp add: \<eta>_def algebra_simps) (simp add: field_simps)
  ultimately have False
    using True by force
  then show ?thesis ..
next
  case False
  then obtain z where "z \<in> S" and z: "a \<bullet> z = b"
    using assms by auto
  with affine_diffs_subspace [OF \<open>affine S\<close>]
  have sub: "subspace (op + (- z) ` S)" by blast
  then have aff: "affine (op + (- z) ` S)" and span: "span (op + (- z) ` S) = (op + (- z) ` S)"
    by (auto simp: subspace_imp_affine)
  obtain a' a'' where a': "a' \<in> span (op + (- z) ` S)" and a: "a = a' + a''"
                  and "\<And>w. w \<in> span (op + (- z) ` S) \<Longrightarrow> orthogonal a'' w"
      using orthogonal_subspace_decomp_exists [of "op + (- z) ` S" "a"] by metis
  then have "\<And>w. w \<in> S \<Longrightarrow> a'' \<bullet> (w-z) = 0"
    by (simp add: imageI orthogonal_def span)
  then have a'': "\<And>w. w \<in> S \<Longrightarrow> a'' \<bullet> w = (a - a') \<bullet> z"
    by (simp add: a inner_diff_right)
  then have ba'': "\<And>w. w \<in> S \<Longrightarrow> a'' \<bullet> w = b - a' \<bullet> z"
    by (simp add: inner_diff_left z)
  have "\<And>w. w \<in> op + (- z) ` S \<Longrightarrow> (w + a') \<in> op + (- z) ` S"
    by (metis subspace_add a' span_eq sub)
  then have Sclo: "\<And>w. w \<in> S \<Longrightarrow> (w + a') \<in> S"
    by fastforce
  show ?thesis
  proof (cases "a' = 0")
    case True
    with a assms True a'' diff_zero less_irrefl show ?thesis
      by auto
  next
    case False
    show ?thesis
      apply (rule_tac a' = "a'" and b' = "a' \<bullet> z" in that)
      apply (auto simp: a ba'' inner_left_distrib False Sclo)
      done
  qed
qed

lemma diffs_affine_hull_span:
  assumes "a \<in> S"
    shows "{x - a |x. x \<in> affine hull S} = span {x - a |x. x \<in> S}"
proof -
  have *: "((\<lambda>x. x - a) ` (S - {a})) = {x. x + a \<in> S} - {0}"
    by (auto simp: algebra_simps)
  show ?thesis
    apply (simp add: affine_hull_span2 [OF assms] *)
    apply (auto simp: algebra_simps)
    done
qed

lemma aff_dim_dim_affine_diffs:
  fixes S :: "'a :: euclidean_space set"
  assumes "affine S" "a \<in> S"
    shows "aff_dim S = dim {x - a |x. x \<in> S}"
proof -
  obtain B where aff: "affine hull B = affine hull S"
             and ind: "\<not> affine_dependent B"
             and card: "of_nat (card B) = aff_dim S + 1"
    using aff_dim_basis_exists by blast
  then have "B \<noteq> {}" using assms
    by (metis affine_hull_eq_empty ex_in_conv)
  then obtain c where "c \<in> B" by auto
  then have "c \<in> S"
    by (metis aff affine_hull_eq \<open>affine S\<close> hull_inc)
  have xy: "x - c = y - a \<longleftrightarrow> y = x + 1 *\<^sub>R (a - c)" for x y c and a::'a
    by (auto simp: algebra_simps)
  have *: "{x - c |x. x \<in> S} = {x - a |x. x \<in> S}"
    apply safe
    apply (simp_all only: xy)
    using mem_affine_3_minus [OF \<open>affine S\<close>] \<open>a \<in> S\<close> \<open>c \<in> S\<close> apply blast+
    done
  have affS: "affine hull S = S"
    by (simp add: \<open>affine S\<close>)
  have "aff_dim S = of_nat (card B) - 1"
    using card by simp
  also have "... = dim {x - c |x. x \<in> B}"
    by (simp add: affine_independent_card_dim_diffs [OF ind \<open>c \<in> B\<close>])
  also have "... = dim {x - c | x. x \<in> affine hull B}"
     by (simp add: diffs_affine_hull_span \<open>c \<in> B\<close>)
  also have "... = dim {x - a |x. x \<in> S}"
     by (simp add: affS aff *)
   finally show ?thesis .
qed

lemma aff_dim_linear_image_le:
  assumes "linear f"
    shows "aff_dim(f ` S) \<le> aff_dim S"
proof -
  have "aff_dim (f ` T) \<le> aff_dim T" if "affine T" for T
  proof (cases "T = {}")
    case True then show ?thesis by (simp add: aff_dim_geq)
  next
    case False
    then obtain a where "a \<in> T" by auto
    have 1: "((\<lambda>x. x - f a) ` f ` T) = {x - f a |x. x \<in> f ` T}"
      by auto
    have 2: "{x - f a| x. x \<in> f ` T} = f ` {x - a| x. x \<in> T}"
      by (force simp: linear_diff [OF assms])
    have "aff_dim (f ` T) = int (dim {x - f a |x. x \<in> f ` T})"
      by (simp add: \<open>a \<in> T\<close> hull_inc aff_dim_eq_dim [of "f a"] 1)
    also have "... = int (dim (f ` {x - a| x. x \<in> T}))"
      by (force simp: linear_diff [OF assms] 2)
    also have "... \<le> int (dim {x - a| x. x \<in> T})"
      by (simp add: dim_image_le [OF assms])
    also have "... \<le> aff_dim T"
      by (simp add: aff_dim_dim_affine_diffs [symmetric] \<open>a \<in> T\<close> \<open>affine T\<close>)
    finally show ?thesis .
  qed
  then
  have "aff_dim (f ` (affine hull S)) \<le> aff_dim (affine hull S)"
    using affine_affine_hull [of S] by blast
  then show ?thesis
    using affine_hull_linear_image assms linear_conv_bounded_linear by fastforce
qed

lemma aff_dim_injective_linear_image [simp]:
  assumes "linear f" "inj f"
    shows "aff_dim (f ` S) = aff_dim S"
proof (rule antisym)
  show "aff_dim (f ` S) \<le> aff_dim S"
    by (simp add: aff_dim_linear_image_le assms(1))
next
  obtain g where "linear g" "g \<circ> f = id"
    using linear_injective_left_inverse assms by blast
  then have "aff_dim S \<le> aff_dim(g ` f ` S)"
    by (simp add: image_comp)
  also have "... \<le> aff_dim (f ` S)"
    by (simp add: \<open>linear g\<close> aff_dim_linear_image_le)
  finally show "aff_dim S \<le> aff_dim (f ` S)" .
qed


text\<open>Choosing a subspace of a given dimension\<close>
proposition choose_subspace_of_subspace:
  fixes S :: "'n::euclidean_space set"
  assumes "n \<le> dim S"
  obtains T where "subspace T" "T \<subseteq> span S" "dim T = n"
proof -
  have "\<exists>T. subspace T \<and> T \<subseteq> span S \<and> dim T = n"
  using assms
  proof (induction n)
    case 0 then show ?case by force
  next
    case (Suc n)
    then obtain T where "subspace T" "T \<subseteq> span S" "dim T = n"
      by force
    then show ?case
    proof (cases "span S \<subseteq> span T")
      case True
      have "dim S = dim T"
        apply (rule span_eq_dim [OF subset_antisym [OF True]])
        by (simp add: \<open>T \<subseteq> span S\<close> span_minimal subspace_span)
      then show ?thesis
        using Suc.prems \<open>dim T = n\<close> by linarith
    next
      case False
      then obtain y where y: "y \<in> S" "y \<notin> T"
        by (meson span_mono subsetI)
      then have "span (insert y T) \<subseteq> span S"
        by (metis (no_types) \<open>T \<subseteq> span S\<close> subsetD insert_subset span_inc span_mono span_span)
      with \<open>dim T = n\<close>  \<open>subspace T\<close> y show ?thesis
        apply (rule_tac x="span(insert y T)" in exI)
        apply (auto simp: dim_insert)
        using span_eq by blast
    qed
  qed
  with that show ?thesis by blast
qed

lemma choose_affine_subset:
  assumes "affine S" "-1 \<le> d" and dle: "d \<le> aff_dim S"
  obtains T where "affine T" "T \<subseteq> S" "aff_dim T = d"
proof (cases "d = -1 \<or> S={}")
  case True with assms show ?thesis
    by (metis aff_dim_empty affine_empty bot.extremum that eq_iff)
next
  case False
  with assms obtain a where "a \<in> S" "0 \<le> d" by auto
  with assms have ss: "subspace (op + (- a) ` S)"
    by (simp add: affine_diffs_subspace)
  have "nat d \<le> dim (op + (- a) ` S)"
    by (metis aff_dim_subspace aff_dim_translation_eq dle nat_int nat_mono ss)
  then obtain T where "subspace T" and Tsb: "T \<subseteq> span (op + (- a) ` S)"
                  and Tdim: "dim T = nat d"
    using choose_subspace_of_subspace [of "nat d" "op + (- a) ` S"] by blast
  then have "affine T"
    using subspace_affine by blast
  then have "affine (op + a ` T)"
    by (metis affine_hull_eq affine_hull_translation)
  moreover have "op + a ` T \<subseteq> S"
  proof -
    have "T \<subseteq> op + (- a) ` S"
      by (metis (no_types) span_eq Tsb ss)
    then show "op + a ` T \<subseteq> S"
      using add_ac by auto
  qed
  moreover have "aff_dim (op + a ` T) = d"
    by (simp add: aff_dim_subspace Tdim \<open>0 \<le> d\<close> \<open>subspace T\<close> aff_dim_translation_eq)
  ultimately show ?thesis
    by (rule that)
qed

subsection\<open>Several Variants of Paracompactness\<close>

proposition paracompact:
  fixes S :: "'a :: euclidean_space set"
  assumes "S \<subseteq> \<Union>\<C>" and opC: "\<And>T. T \<in> \<C> \<Longrightarrow> open T"
  obtains \<C>' where "S \<subseteq> \<Union> \<C>'"
               and "\<And>U. U \<in> \<C>' \<Longrightarrow> open U \<and> (\<exists>T. T \<in> \<C> \<and> U \<subseteq> T)"
               and "\<And>x. x \<in> S
                       \<Longrightarrow> \<exists>V. open V \<and> x \<in> V \<and>
                               finite {U. U \<in> \<C>' \<and> (U \<inter> V \<noteq> {})}"
proof (cases "S = {}")
  case True with that show ?thesis by blast
next
  case False
  have "\<exists>T U. x \<in> U \<and> open U \<and> closure U \<subseteq> T \<and> T \<in> \<C>" if "x \<in> S" for x
  proof -
    obtain T where "x \<in> T" "T \<in> \<C>" "open T"
      using assms \<open>x \<in> S\<close> by blast
    then obtain e where "e > 0" "cball x e \<subseteq> T"
      by (force simp: open_contains_cball)
    then show ?thesis
      apply (rule_tac x = T in exI)
      apply (rule_tac x = "ball x e" in exI)
      using  \<open>T \<in> \<C>\<close>
      apply (simp add: closure_minimal)
      done
  qed
  then obtain F G where Gin: "x \<in> G x" and oG: "open (G x)"
                    and clos: "closure (G x) \<subseteq> F x" and Fin: "F x \<in> \<C>"
         if "x \<in> S" for x
    by metis
  then obtain \<F> where "\<F> \<subseteq> G ` S" "countable \<F>" "\<Union>\<F> = UNION S G"
    using Lindelof [of "G ` S"] by (metis image_iff)
  then obtain K where K: "K \<subseteq> S" "countable K" and eq: "UNION K G = UNION S G"
    by (metis countable_subset_image)
  with False Gin have "K \<noteq> {}" by force
  then obtain a :: "nat \<Rightarrow> 'a" where "range a = K"
    by (metis range_from_nat_into \<open>countable K\<close>)
  then have odif: "\<And>n. open (F (a n) - \<Union>{closure (G (a m)) |m. m < n})"
    using \<open>K \<subseteq> S\<close> Fin opC by (fastforce simp add:)
  let ?C = "range (\<lambda>n. F(a n) - \<Union>{closure(G(a m)) |m. m < n})"
  have enum_S: "\<exists>n. x \<in> F(a n) \<and> x \<in> G(a n)" if "x \<in> S" for x
  proof -
    have "\<exists>y \<in> K. x \<in> G y" using eq that Gin by fastforce
    then show ?thesis
      using clos K \<open>range a = K\<close> closure_subset by blast
  qed
  have 1: "S \<subseteq> Union ?C"
  proof
    fix x assume "x \<in> S"
    define n where "n \<equiv> LEAST n. x \<in> F(a n)"
    have n: "x \<in> F(a n)"
      using enum_S [OF \<open>x \<in> S\<close>] by (force simp: n_def intro: LeastI)
    have notn: "x \<notin> F(a m)" if "m < n" for m
      using that not_less_Least by (force simp: n_def)
    then have "x \<notin> \<Union>{closure (G (a m)) |m. m < n}"
      using n \<open>K \<subseteq> S\<close> \<open>range a = K\<close> clos notn by fastforce
    with n show "x \<in> Union ?C"
      by blast
  qed
  have 3: "\<exists>V. open V \<and> x \<in> V \<and> finite {U. U \<in> ?C \<and> (U \<inter> V \<noteq> {})}" if "x \<in> S" for x
  proof -
    obtain n where n: "x \<in> F(a n)" "x \<in> G(a n)"
      using \<open>x \<in> S\<close> enum_S by auto
    have "{U \<in> ?C. U \<inter> G (a n) \<noteq> {}} \<subseteq> (\<lambda>n. F(a n) - \<Union>{closure(G(a m)) |m. m < n}) ` atMost n"
    proof clarsimp
      fix k  assume "(F (a k) - \<Union>{closure (G (a m)) |m. m < k}) \<inter> G (a n) \<noteq> {}"
      then have "k \<le> n"
        by auto (metis closure_subset not_le subsetCE)
      then show "F (a k) - \<Union>{closure (G (a m)) |m. m < k}
                 \<in> (\<lambda>n. F (a n) - \<Union>{closure (G (a m)) |m. m < n}) ` {..n}"
        by force
    qed
    moreover have "finite ((\<lambda>n. F(a n) - \<Union>{closure(G(a m)) |m. m < n}) ` atMost n)"
      by force
    ultimately have *: "finite {U \<in> ?C. U \<inter> G (a n) \<noteq> {}}"
      using finite_subset by blast
    show ?thesis
      apply (rule_tac x="G (a n)" in exI)
      apply (intro conjI oG n *)
      using \<open>K \<subseteq> S\<close> \<open>range a = K\<close> apply blast
      done
  qed
  show ?thesis
    apply (rule that [OF 1 _ 3])
    using Fin \<open>K \<subseteq> S\<close> \<open>range a = K\<close>  apply (auto simp: odif)
    done
qed

corollary paracompact_closedin:
  fixes S :: "'a :: euclidean_space set"
  assumes cin: "closedin (subtopology euclidean U) S"
      and oin: "\<And>T. T \<in> \<C> \<Longrightarrow> openin (subtopology euclidean U) T"
      and "S \<subseteq> \<Union>\<C>"
  obtains \<C>' where "S \<subseteq> \<Union> \<C>'"
               and "\<And>V. V \<in> \<C>' \<Longrightarrow> openin (subtopology euclidean U) V \<and> (\<exists>T. T \<in> \<C> \<and> V \<subseteq> T)"
               and "\<And>x. x \<in> U
                       \<Longrightarrow> \<exists>V. openin (subtopology euclidean U) V \<and> x \<in> V \<and>
                               finite {X. X \<in> \<C>' \<and> (X \<inter> V \<noteq> {})}"
proof -
  have "\<exists>Z. open Z \<and> (T = U \<inter> Z)" if "T \<in> \<C>" for T
    using oin [OF that] by (auto simp: openin_open)
  then obtain F where opF: "open (F T)" and intF: "U \<inter> F T = T" if "T \<in> \<C>" for T
    by metis
  obtain K where K: "closed K" "U \<inter> K = S"
    using cin by (auto simp: closedin_closed)
  have 1: "U \<subseteq> \<Union>insert (- K) (F ` \<C>)"
    by clarsimp (metis Int_iff Union_iff \<open>U \<inter> K = S\<close> \<open>S \<subseteq> \<Union>\<C>\<close> subsetD intF)
  have 2: "\<And>T. T \<in> insert (- K) (F ` \<C>) \<Longrightarrow> open T"
    using \<open>closed K\<close> by (auto simp: opF)
  obtain \<D> where "U \<subseteq> \<Union>\<D>"
             and D1: "\<And>U. U \<in> \<D> \<Longrightarrow> open U \<and> (\<exists>T. T \<in> insert (- K) (F ` \<C>) \<and> U \<subseteq> T)"
             and D2: "\<And>x. x \<in> U \<Longrightarrow> \<exists>V. open V \<and> x \<in> V \<and> finite {U \<in> \<D>. U \<inter> V \<noteq> {}}"
    using paracompact [OF 1 2] by auto
  let ?C = "{U \<inter> V |V. V \<in> \<D> \<and> (V \<inter> K \<noteq> {})}"
  show ?thesis
  proof (rule_tac \<C>' = "{U \<inter> V |V. V \<in> \<D> \<and> (V \<inter> K \<noteq> {})}" in that)
    show "S \<subseteq> \<Union>?C"
      using \<open>U \<inter> K = S\<close> \<open>U \<subseteq> \<Union>\<D>\<close> K by (blast dest!: subsetD)
    show "\<And>V. V \<in> ?C \<Longrightarrow> openin (subtopology euclidean U) V \<and> (\<exists>T. T \<in> \<C> \<and> V \<subseteq> T)"
      using D1 intF by fastforce
    have *: "{X. (\<exists>V. X = U \<inter> V \<and> V \<in> \<D> \<and> V \<inter> K \<noteq> {}) \<and> X \<inter> (U \<inter> V) \<noteq> {}} \<subseteq>
             (\<lambda>x. U \<inter> x) ` {U \<in> \<D>. U \<inter> V \<noteq> {}}" for V
      by blast
    show "\<exists>V. openin (subtopology euclidean U) V \<and> x \<in> V \<and> finite {X \<in> ?C. X \<inter> V \<noteq> {}}"
         if "x \<in> U" for x
      using D2 [OF that]
      apply clarify
      apply (rule_tac x="U \<inter> V" in exI)
      apply (auto intro: that finite_subset [OF *])
      done
    qed
qed

corollary paracompact_closed:
  fixes S :: "'a :: euclidean_space set"
  assumes "closed S"
      and opC: "\<And>T. T \<in> \<C> \<Longrightarrow> open T"
      and "S \<subseteq> \<Union>\<C>"
  obtains \<C>' where "S \<subseteq> \<Union>\<C>'"
               and "\<And>U. U \<in> \<C>' \<Longrightarrow> open U \<and> (\<exists>T. T \<in> \<C> \<and> U \<subseteq> T)"
               and "\<And>x. \<exists>V. open V \<and> x \<in> V \<and>
                               finite {U. U \<in> \<C>' \<and> (U \<inter> V \<noteq> {})}"
using paracompact_closedin [of UNIV S \<C>] assms
by (auto simp: open_openin [symmetric] closed_closedin [symmetric])

  
subsection\<open>Closed-graph characterization of continuity\<close>

lemma continuous_closed_graph_gen:
  fixes T :: "'b::real_normed_vector set"
  assumes contf: "continuous_on S f" and fim: "f ` S \<subseteq> T"
    shows "closedin (subtopology euclidean (S \<times> T)) ((\<lambda>x. Pair x (f x)) ` S)"
proof -
  have eq: "((\<lambda>x. Pair x (f x)) ` S) = {z. z \<in> S \<times> T \<and> (f \<circ> fst)z - snd z \<in> {0}}"
    using fim by auto
  show ?thesis
    apply (subst eq)
    apply (intro continuous_intros continuous_closedin_preimage continuous_on_subset [OF contf])
    by auto
qed

lemma continuous_closed_graph_eq:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  assumes "compact T" and fim: "f ` S \<subseteq> T"
  shows "continuous_on S f \<longleftrightarrow>
         closedin (subtopology euclidean (S \<times> T)) ((\<lambda>x. Pair x (f x)) ` S)"
         (is "?lhs = ?rhs")
proof -
  have "?lhs" if ?rhs
  proof (clarsimp simp add: continuous_on_closed_gen [OF fim])
    fix U
    assume U: "closedin (subtopology euclidean T) U"
    have eq: "{x. x \<in> S \<and> f x \<in> U} = fst ` (((\<lambda>x. Pair x (f x)) ` S) \<inter> (S \<times> U))"
      by (force simp: image_iff)
    show "closedin (subtopology euclidean S) {x \<in> S. f x \<in> U}"
      by (simp add: U closedin_Int closedin_Times closed_map_fst [OF \<open>compact T\<close>] that eq)
  qed
  with continuous_closed_graph_gen assms show ?thesis by blast
qed

lemma continuous_closed_graph:
  fixes f :: "'a::topological_space \<Rightarrow> 'b::real_normed_vector"
  assumes "closed S" and contf: "continuous_on S f"
  shows "closed ((\<lambda>x. Pair x (f x)) ` S)"
  apply (rule closedin_closed_trans)
   apply (rule continuous_closed_graph_gen [OF contf subset_UNIV])
  by (simp add: \<open>closed S\<close> closed_Times)

lemma continuous_from_closed_graph:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  assumes "compact T" and fim: "f ` S \<subseteq> T" and clo: "closed ((\<lambda>x. Pair x (f x)) ` S)"
  shows "continuous_on S f"
    using fim clo
    by (auto intro: closed_subset simp: continuous_closed_graph_eq [OF \<open>compact T\<close> fim])

lemma continuous_on_Un_local_open:
  assumes opS: "openin (subtopology euclidean (S \<union> T)) S"
      and opT: "openin (subtopology euclidean (S \<union> T)) T"
      and contf: "continuous_on S f" and contg: "continuous_on T f"
    shows "continuous_on (S \<union> T) f"
using pasting_lemma [of "{S,T}" "S \<union> T" "\<lambda>i. i" "\<lambda>i. f" f] contf contg opS opT by blast

lemma continuous_on_cases_local_open:
  assumes opS: "openin (subtopology euclidean (S \<union> T)) S"
      and opT: "openin (subtopology euclidean (S \<union> T)) T"
      and contf: "continuous_on S f" and contg: "continuous_on T g"
      and fg: "\<And>x. x \<in> S \<and> ~P x \<or> x \<in> T \<and> P x \<Longrightarrow> f x = g x"
    shows "continuous_on (S \<union> T) (\<lambda>x. if P x then f x else g x)"
proof -
  have "\<And>x. x \<in> S \<Longrightarrow> (if P x then f x else g x) = f x"  "\<And>x. x \<in> T \<Longrightarrow> (if P x then f x else g x) = g x"
    by (simp_all add: fg)
  then have "continuous_on S (\<lambda>x. if P x then f x else g x)" "continuous_on T (\<lambda>x. if P x then f x else g x)"
    by (simp_all add: contf contg cong: continuous_on_cong)
  then show ?thesis
    by (rule continuous_on_Un_local_open [OF opS opT])
qed
  
subsection\<open>The union of two collinear segments is another segment\<close>

proposition in_convex_hull_exchange:
  fixes a :: "'a::euclidean_space"
  assumes a: "a \<in> convex hull S" and xS: "x \<in> convex hull S"
  obtains b where "b \<in> S" "x \<in> convex hull (insert a (S - {b}))"
proof (cases "a \<in> S")
  case True
  with xS insert_Diff that  show ?thesis by fastforce
next
  case False
  show ?thesis
  proof (cases "finite S \<and> card S \<le> Suc (DIM('a))")
    case True
    then obtain u where u0: "\<And>i. i \<in> S \<Longrightarrow> 0 \<le> u i" and u1: "sum u S = 1"
                    and ua: "(\<Sum>i\<in>S. u i *\<^sub>R i) = a"
        using a by (auto simp: convex_hull_finite)
    obtain v where v0: "\<And>i. i \<in> S \<Longrightarrow> 0 \<le> v i" and v1: "sum v S = 1"
               and vx: "(\<Sum>i\<in>S. v i *\<^sub>R i) = x"
      using True xS by (auto simp: convex_hull_finite)
    show ?thesis
    proof (cases "\<exists>b. b \<in> S \<and> v b = 0")
      case True
      then obtain b where b: "b \<in> S" "v b = 0"
        by blast
      show ?thesis
      proof
        have fin: "finite (insert a (S - {b}))"
          using sum.infinite v1 by fastforce
        show "x \<in> convex hull insert a (S - {b})"
          unfolding convex_hull_finite [OF fin] mem_Collect_eq
        proof (intro conjI exI ballI)
          have "(\<Sum>x \<in> insert a (S - {b}). if x = a then 0 else v x) =
                (\<Sum>x \<in> S - {b}. if x = a then 0 else v x)"
            apply (rule sum.mono_neutral_right)
            using fin by auto
          also have "... = (\<Sum>x \<in> S - {b}. v x)"
            using b False by (auto intro!: sum.cong split: if_split_asm)
          also have "... = (\<Sum>x\<in>S. v x)"
            by (metis \<open>v b = 0\<close> diff_zero sum.infinite sum_diff1 u1 zero_neq_one)
          finally show "(\<Sum>x\<in>insert a (S - {b}). if x = a then 0 else v x) = 1"
            by (simp add: v1)
          show "\<And>x. x \<in> insert a (S - {b}) \<Longrightarrow> 0 \<le> (if x = a then 0 else v x)"
            by (auto simp: v0)
          have "(\<Sum>x \<in> insert a (S - {b}). (if x = a then 0 else v x) *\<^sub>R x) =
                (\<Sum>x \<in> S - {b}. (if x = a then 0 else v x) *\<^sub>R x)"
            apply (rule sum.mono_neutral_right)
            using fin by auto
          also have "... = (\<Sum>x \<in> S - {b}. v x *\<^sub>R x)"
            using b False by (auto intro!: sum.cong split: if_split_asm)
          also have "... = (\<Sum>x\<in>S. v x *\<^sub>R x)"
            by (metis (no_types, lifting) b(2) diff_zero fin finite.emptyI finite_Diff2 finite_insert real_vector.scale_eq_0_iff sum_diff1)
          finally show "(\<Sum>x\<in>insert a (S - {b}). (if x = a then 0 else v x) *\<^sub>R x) = x"
            by (simp add: vx)
        qed
      qed (rule \<open>b \<in> S\<close>)
    next
      case False
      have le_Max: "u i / v i \<le> Max ((\<lambda>i. u i / v i) ` S)" if "i \<in> S" for i
        by (simp add: True that)
      have "Max ((\<lambda>i. u i / v i) ` S) \<in> (\<lambda>i. u i / v i) ` S"
        using True v1 by (auto intro: Max_in)
      then obtain b where "b \<in> S" and beq: "Max ((\<lambda>b. u b / v b) ` S) = u b / v b"
        by blast
      then have "0 \<noteq> u b / v b"
        using le_Max beq divide_le_0_iff le_numeral_extra(2) sum_nonpos u1
        by (metis False eq_iff v0)
      then have  "0 < u b" "0 < v b"
        using False \<open>b \<in> S\<close> u0 v0 by force+
      have fin: "finite (insert a (S - {b}))"
        using sum.infinite v1 by fastforce
      show ?thesis
      proof
        show "x \<in> convex hull insert a (S - {b})"
          unfolding convex_hull_finite [OF fin] mem_Collect_eq
        proof (intro conjI exI ballI)
          have "(\<Sum>x \<in> insert a (S - {b}). if x=a then v b / u b else v x - (v b / u b) * u x) =
                v b / u b + (\<Sum>x \<in> S - {b}. v x - (v b / u b) * u x)"
            using \<open>a \<notin> S\<close> \<open>b \<in> S\<close> True  apply simp
            apply (rule sum.cong, auto)
            done
          also have "... = v b / u b + (\<Sum>x \<in> S - {b}. v x) - (v b / u b) * (\<Sum>x \<in> S - {b}. u x)"
            by (simp add: Groups_Big.sum_subtractf sum_distrib_left)
          also have "... = (\<Sum>x\<in>S. v x)"
            using \<open>0 < u b\<close> True  by (simp add: Groups_Big.sum_diff1 u1 field_simps)
          finally show "sum (\<lambda>x. if x=a then v b / u b else v x - (v b / u b) * u x) (insert a (S - {b})) = 1"
            by (simp add: v1)
          show "0 \<le> (if i = a then v b / u b else v i - v b / u b * u i)"
            if "i \<in> insert a (S - {b})" for i
            using \<open>0 < u b\<close> \<open>0 < v b\<close> v0 [of i] le_Max [of i] beq that False
            by (auto simp: field_simps split: if_split_asm)
          have "(\<Sum>x\<in>insert a (S - {b}). (if x=a then v b / u b else v x - v b / u b * u x) *\<^sub>R x) =
                (v b / u b) *\<^sub>R a + (\<Sum>x\<in>S - {b}. (v x - v b / u b * u x) *\<^sub>R x)"
            using \<open>a \<notin> S\<close> \<open>b \<in> S\<close> True  apply simp
            apply (rule sum.cong, auto)
            done
          also have "... = (v b / u b) *\<^sub>R a + (\<Sum>x \<in> S - {b}. v x *\<^sub>R x) - (v b / u b) *\<^sub>R (\<Sum>x \<in> S - {b}. u x *\<^sub>R x)"
            by (simp add: Groups_Big.sum_subtractf scaleR_left_diff_distrib sum_distrib_left real_vector.scale_sum_right)
          also have "... = (\<Sum>x\<in>S. v x *\<^sub>R x)"
            using \<open>0 < u b\<close> True  by (simp add: ua vx Groups_Big.sum_diff1 algebra_simps)
          finally
          show "(\<Sum>x\<in>insert a (S - {b}). (if x=a then v b / u b else v x - v b / u b * u x) *\<^sub>R x) = x"
            by (simp add: vx)
        qed
      qed (rule \<open>b \<in> S\<close>)
    qed
  next
    case False
    obtain T where "finite T" "T \<subseteq> S" and caT: "card T \<le> Suc (DIM('a))" and xT: "x \<in> convex hull T"
      using xS by (auto simp: caratheodory [of S])
    with False obtain b where b: "b \<in> S" "b \<notin> T"
      by (metis antisym subsetI)
    show ?thesis
    proof
      show "x \<in> convex hull insert a (S - {b})"
        using  \<open>T \<subseteq> S\<close> b by (blast intro: subsetD [OF hull_mono xT])
    qed (rule \<open>b \<in> S\<close>)
  qed
qed

lemma convex_hull_exchange_Union:
  fixes a :: "'a::euclidean_space"
  assumes "a \<in> convex hull S"
  shows "convex hull S = (\<Union>b \<in> S. convex hull (insert a (S - {b})))" (is "?lhs = ?rhs")
proof
  show "?lhs \<subseteq> ?rhs"
    by (blast intro: in_convex_hull_exchange [OF assms])
  show "?rhs \<subseteq> ?lhs"
  proof clarify
    fix x b
    assume"b \<in> S" "x \<in> convex hull insert a (S - {b})"
    then show "x \<in> convex hull S" if "b \<in> S"
      by (metis (no_types) that assms order_refl hull_mono hull_redundant insert_Diff_single insert_subset subsetCE)
  qed
qed

lemma Un_closed_segment:
  fixes a :: "'a::euclidean_space"
  assumes "b \<in> closed_segment a c"
    shows "closed_segment a b \<union> closed_segment b c = closed_segment a c"
proof (cases "c = a")
  case True
  with assms show ?thesis by simp
next
  case False
  with assms have "convex hull {a, b} \<union> convex hull {b, c} = (\<Union>ba\<in>{a, c}. convex hull insert b ({a, c} - {ba}))"
    by (auto simp: insert_Diff_if insert_commute)
  then show ?thesis
    using convex_hull_exchange_Union
    by (metis assms segment_convex_hull)
qed

lemma Un_open_segment:
  fixes a :: "'a::euclidean_space"
  assumes "b \<in> open_segment a c"
  shows "open_segment a b \<union> {b} \<union> open_segment b c = open_segment a c"
proof -
  have b: "b \<in> closed_segment a c"
    by (simp add: assms open_closed_segment)
  have *: "open_segment a c \<subseteq> insert b (open_segment a b \<union> open_segment b c)"
          if "{b,c,a} \<union> open_segment a b \<union> open_segment b c = {c,a} \<union> open_segment a c"
  proof -
    have "insert a (insert c (insert b (open_segment a b \<union> open_segment b c))) = insert a (insert c (open_segment a c))"
      using that by (simp add: insert_commute)
    then show ?thesis
      by (metis (no_types) Diff_cancel Diff_eq_empty_iff Diff_insert2 open_segment_def)
  qed
  show ?thesis
    using Un_closed_segment [OF b]
    apply (simp add: closed_segment_eq_open)
      apply (rule equalityI)
    using assms
     apply (simp add: b subset_open_segment)
      using * by (simp add: insert_commute)
qed

subsection\<open>Covering an open set by a countable chain of compact sets\<close>
  
proposition open_Union_compact_subsets:
  fixes S :: "'a::euclidean_space set"
  assumes "open S"
  obtains C where "\<And>n. compact(C n)" "\<And>n. C n \<subseteq> S"
                  "\<And>n. C n \<subseteq> interior(C(Suc n))"
                  "\<Union>(range C) = S"
                  "\<And>K. \<lbrakk>compact K; K \<subseteq> S\<rbrakk> \<Longrightarrow> \<exists>N. \<forall>n\<ge>N. K \<subseteq> (C n)"
proof (cases "S = {}")
  case True
  then show ?thesis
    by (rule_tac C = "\<lambda>n. {}" in that) auto
next
  case False
  then obtain a where "a \<in> S"
    by auto
  let ?C = "\<lambda>n. cball a (real n) - (\<Union>x \<in> -S. \<Union>e \<in> ball 0 (1 / real(Suc n)). {x + e})"
  have "\<exists>N. \<forall>n\<ge>N. K \<subseteq> (f n)"
        if "\<And>n. compact(f n)" and sub_int: "\<And>n. f n \<subseteq> interior (f(Suc n))"
            and eq: "\<Union>(range f) = S" and "compact K" "K \<subseteq> S" for f K
  proof -
    have *: "\<forall>n. f n \<subseteq> (\<Union>n. interior (f n))"
      by (meson Sup_upper2 UNIV_I \<open>\<And>n. f n \<subseteq> interior (f (Suc n))\<close> image_iff)
    have mono: "\<And>m n. m \<le> n \<Longrightarrow>f m \<subseteq> f n"
      by (meson dual_order.trans interior_subset lift_Suc_mono_le sub_int)
    obtain I where "finite I" and I: "K \<subseteq> (\<Union>i\<in>I. interior (f i))"
    proof (rule compactE_image [OF \<open>compact K\<close>])
      show "K \<subseteq> (\<Union>n. interior (f n))"
        using \<open>K \<subseteq> S\<close> \<open>UNION UNIV f = S\<close> * by blast
    qed auto
    { fix n
      assume n: "Max I \<le> n"
      have "(\<Union>i\<in>I. interior (f i)) \<subseteq> f n"
        by (rule UN_least) (meson dual_order.trans interior_subset mono I Max_ge [OF \<open>finite I\<close>] n)
      then have "K \<subseteq> f n"
        using I by auto
    }
    then show ?thesis
      by blast
  qed
  moreover have "\<exists>f. (\<forall>n. compact(f n)) \<and> (\<forall>n. (f n) \<subseteq> S) \<and> (\<forall>n. (f n) \<subseteq> interior(f(Suc n))) \<and>
                     ((\<Union>(range f) = S))"
  proof (intro exI conjI allI)
    show "\<And>n. compact (?C n)"
      by (auto simp: compact_diff open_sums)
    show "\<And>n. ?C n \<subseteq> S"
      by auto
    show "?C n \<subseteq> interior (?C (Suc n))" for n
    proof (simp add: interior_diff, rule Diff_mono)
      show "cball a (real n) \<subseteq> ball a (1 + real n)"
        by (simp add: cball_subset_ball_iff)
      have cl: "closed (\<Union>x\<in>- S. \<Union>e\<in>cball 0 (1 / (2 + real n)). {x + e})"
        using assms by (auto intro: closed_compact_sums)
      have "closure (\<Union>x\<in>- S. \<Union>y\<in>ball 0 (1 / (2 + real n)). {x + y})
            \<subseteq> (\<Union>x \<in> -S. \<Union>e \<in> cball 0 (1 / (2 + real n)). {x + e})"
        by (intro closure_minimal UN_mono ball_subset_cball order_refl cl)
      also have "... \<subseteq> (\<Union>x \<in> -S. \<Union>y\<in>ball 0 (1 / (1 + real n)). {x + y})"
        apply (intro UN_mono order_refl)
        apply (simp add: cball_subset_ball_iff divide_simps)
        done
      finally show "closure (\<Union>x\<in>- S. \<Union>y\<in>ball 0 (1 / (2 + real n)). {x + y})
                    \<subseteq> (\<Union>x \<in> -S. \<Union>y\<in>ball 0 (1 / (1 + real n)). {x + y})" .
    qed
    have "S \<subseteq> UNION UNIV ?C"
    proof
      fix x
      assume x: "x \<in> S"
      then obtain e where "e > 0" and e: "ball x e \<subseteq> S"
        using assms open_contains_ball by blast
      then obtain N1 where "N1 > 0" and N1: "real N1 > 1/e"
        using reals_Archimedean2
        by (metis divide_less_0_iff less_eq_real_def neq0_conv not_le of_nat_0 of_nat_1 of_nat_less_0_iff)
      obtain N2 where N2: "norm(x - a) \<le> real N2"
        by (meson real_arch_simple)
      have N12: "inverse((N1 + N2) + 1) \<le> inverse(N1)"
        using \<open>N1 > 0\<close> by (auto simp: divide_simps)
      have "x \<noteq> y + z" if "y \<notin> S" "norm z < 1 / (1 + (real N1 + real N2))" for y z
      proof -
        have "e * real N1 < e * (1 + (real N1 + real N2))"
          by (simp add: \<open>0 < e\<close>)
        then have "1 / (1 + (real N1 + real N2)) < e"
          using N1 \<open>e > 0\<close>
          by (metis divide_less_eq less_trans mult.commute of_nat_add of_nat_less_0_iff of_nat_Suc)
        then have "x - z \<in> ball x e"
          using that by simp
        then have "x - z \<in> S"
          using e by blast
        with that show ?thesis
          by auto
      qed
      with N2 show "x \<in> UNION UNIV ?C"
        by (rule_tac a = "N1+N2" in UN_I) (auto simp: dist_norm norm_minus_commute)
    qed
    then show "UNION UNIV ?C = S" by auto
  qed
  ultimately show ?thesis
    using that by metis
qed
  
end
