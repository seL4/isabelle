(*  Title:      HOL/Library/Convex.thy
    Author:     Armin Heller, TU Muenchen
    Author:     Johannes Hoelzl, TU Muenchen
*)

header {* Convexity in real vector spaces *}

theory Convex
imports Product_Vector
begin

subsection {* Convexity. *}

definition convex :: "'a::real_vector set \<Rightarrow> bool"
  where "convex s \<longleftrightarrow> (\<forall>x\<in>s. \<forall>y\<in>s. \<forall>u\<ge>0. \<forall>v\<ge>0. u + v = 1 \<longrightarrow> u *\<^sub>R x + v *\<^sub>R y \<in> s)"

lemma convex_alt:
  "convex s \<longleftrightarrow> (\<forall>x\<in>s. \<forall>y\<in>s. \<forall>u. 0 \<le> u \<and> u \<le> 1 \<longrightarrow> ((1 - u) *\<^sub>R x + u *\<^sub>R y) \<in> s)"
  (is "_ \<longleftrightarrow> ?alt")
proof
  assume alt[rule_format]: ?alt
  { fix x y and u v :: real assume mem: "x \<in> s" "y \<in> s"
    assume "0 \<le> u" "0 \<le> v"
    moreover assume "u + v = 1" then have "u = 1 - v" by auto
    ultimately have "u *\<^sub>R x + v *\<^sub>R y \<in> s" using alt[OF mem] by auto }
  then show "convex s" unfolding convex_def by auto
qed (auto simp: convex_def)

lemma mem_convex:
  assumes "convex s" "a \<in> s" "b \<in> s" "0 \<le> u" "u \<le> 1"
  shows "((1 - u) *\<^sub>R a + u *\<^sub>R b) \<in> s"
  using assms unfolding convex_alt by auto

lemma convex_empty[intro]: "convex {}"
  unfolding convex_def by simp

lemma convex_singleton[intro]: "convex {a}"
  unfolding convex_def by (auto simp: scaleR_left_distrib[symmetric])

lemma convex_UNIV[intro]: "convex UNIV"
  unfolding convex_def by auto

lemma convex_Inter: "(\<forall>s\<in>f. convex s) ==> convex(\<Inter> f)"
  unfolding convex_def by auto

lemma convex_Int: "convex s \<Longrightarrow> convex t \<Longrightarrow> convex (s \<inter> t)"
  unfolding convex_def by auto

lemma convex_halfspace_le: "convex {x. inner a x \<le> b}"
  unfolding convex_def
  by (auto simp: inner_add intro!: convex_bound_le)

lemma convex_halfspace_ge: "convex {x. inner a x \<ge> b}"
proof -
  have *: "{x. inner a x \<ge> b} = {x. inner (-a) x \<le> -b}" by auto
  show ?thesis unfolding * using convex_halfspace_le[of "-a" "-b"] by auto
qed

lemma convex_hyperplane: "convex {x. inner a x = b}"
proof -
  have *: "{x. inner a x = b} = {x. inner a x \<le> b} \<inter> {x. inner a x \<ge> b}" by auto
  show ?thesis using convex_halfspace_le convex_halfspace_ge
    by (auto intro!: convex_Int simp: *)
qed

lemma convex_halfspace_lt: "convex {x. inner a x < b}"
  unfolding convex_def
  by (auto simp: convex_bound_lt inner_add)

lemma convex_halfspace_gt: "convex {x. inner a x > b}"
   using convex_halfspace_lt[of "-a" "-b"] by auto

lemma convex_real_interval:
  fixes a b :: "real"
  shows "convex {a..}" and "convex {..b}"
    and "convex {a<..}" and "convex {..<b}"
    and "convex {a..b}" and "convex {a<..b}"
    and "convex {a..<b}" and "convex {a<..<b}"
proof -
  have "{a..} = {x. a \<le> inner 1 x}" by auto
  then show 1: "convex {a..}" by (simp only: convex_halfspace_ge)
  have "{..b} = {x. inner 1 x \<le> b}" by auto
  then show 2: "convex {..b}" by (simp only: convex_halfspace_le)
  have "{a<..} = {x. a < inner 1 x}" by auto
  then show 3: "convex {a<..}" by (simp only: convex_halfspace_gt)
  have "{..<b} = {x. inner 1 x < b}" by auto
  then show 4: "convex {..<b}" by (simp only: convex_halfspace_lt)
  have "{a..b} = {a..} \<inter> {..b}" by auto
  then show "convex {a..b}" by (simp only: convex_Int 1 2)
  have "{a<..b} = {a<..} \<inter> {..b}" by auto
  then show "convex {a<..b}" by (simp only: convex_Int 3 2)
  have "{a..<b} = {a..} \<inter> {..<b}" by auto
  then show "convex {a..<b}" by (simp only: convex_Int 1 4)
  have "{a<..<b} = {a<..} \<inter> {..<b}" by auto
  then show "convex {a<..<b}" by (simp only: convex_Int 3 4)
qed


subsection {* Explicit expressions for convexity in terms of arbitrary sums. *}

lemma convex_setsum:
  fixes C :: "'a::real_vector set"
  assumes "finite s" and "convex C" and "(\<Sum> i \<in> s. a i) = 1"
  assumes "\<And>i. i \<in> s \<Longrightarrow> a i \<ge> 0" and "\<And>i. i \<in> s \<Longrightarrow> y i \<in> C"
  shows "(\<Sum> j \<in> s. a j *\<^sub>R y j) \<in> C"
  using assms
proof (induct s arbitrary:a rule: finite_induct)
  case empty
  then show ?case by auto
next
  case (insert i s) note asms = this
  { assume "a i = 1"
    then have "(\<Sum> j \<in> s. a j) = 0"
      using asms by auto
    then have "\<And>j. j \<in> s \<Longrightarrow> a j = 0"
      using setsum_nonneg_0[where 'b=real] asms by fastforce
    then have ?case using asms by auto }
  moreover
  { assume asm: "a i \<noteq> 1"
    from asms have yai: "y i \<in> C" "a i \<ge> 0" by auto
    have fis: "finite (insert i s)" using asms by auto
    then have ai1: "a i \<le> 1" using setsum_nonneg_leq_bound[of "insert i s" a 1] asms by simp
    then have "a i < 1" using asm by auto
    then have i0: "1 - a i > 0" by auto
    let ?a = "\<lambda>j. a j / (1 - a i)"
    { fix j assume "j \<in> s"
      then have "?a j \<ge> 0"
        using i0 asms divide_nonneg_pos
        by fastforce
    } note a_nonneg = this
    have "(\<Sum> j \<in> insert i s. a j) = 1" using asms by auto
    then have "(\<Sum> j \<in> s. a j) = 1 - a i" using setsum.insert asms by fastforce
    then have "(\<Sum> j \<in> s. a j) / (1 - a i) = 1" using i0 by auto
    then have a1: "(\<Sum> j \<in> s. ?a j) = 1" unfolding setsum_divide_distrib by simp
    with asms have "(\<Sum>j\<in>s. ?a j *\<^sub>R y j) \<in> C" using a_nonneg by fastforce
    then have "a i *\<^sub>R y i + (1 - a i) *\<^sub>R (\<Sum> j \<in> s. ?a j *\<^sub>R y j) \<in> C"
      using asms[unfolded convex_def, rule_format] yai ai1 by auto
    then have "a i *\<^sub>R y i + (\<Sum> j \<in> s. (1 - a i) *\<^sub>R (?a j *\<^sub>R y j)) \<in> C"
      using scaleR_right.setsum[of "(1 - a i)" "\<lambda> j. ?a j *\<^sub>R y j" s] by auto
    then have "a i *\<^sub>R y i + (\<Sum> j \<in> s. a j *\<^sub>R y j) \<in> C" using i0 by auto
    then have ?case using setsum.insert asms by auto
  }
  ultimately show ?case by auto
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
  from this convex_setsum[of "{1 .. k}" s]
  show "(\<Sum>j\<in>{1 .. k}. u j *\<^sub>R x j) \<in> s" by auto
next
  assume asm: "\<forall>k u x. (\<forall> i :: nat. 1 \<le> i \<and> i \<le> k \<longrightarrow> 0 \<le> u i \<and> x i \<in> s) \<and> setsum u {1..k} = 1
    \<longrightarrow> (\<Sum>i = 1..k. u i *\<^sub>R (x i :: 'a)) \<in> s"
  { fix \<mu> :: real
    fix x y :: 'a
    assume xy: "x \<in> s" "y \<in> s"
    assume mu: "\<mu> \<ge> 0" "\<mu> \<le> 1"
    let ?u = "\<lambda>i. if (i :: nat) = 1 then \<mu> else 1 - \<mu>"
    let ?x = "\<lambda>i. if (i :: nat) = 1 then x else y"
    have "{1 :: nat .. 2} \<inter> - {x. x = 1} = {2}" by auto
    then have card: "card ({1 :: nat .. 2} \<inter> - {x. x = 1}) = 1" by simp
    then have "setsum ?u {1 .. 2} = 1"
      using setsum_cases[of "{(1 :: nat) .. 2}" "\<lambda> x. x = 1" "\<lambda> x. \<mu>" "\<lambda> x. 1 - \<mu>"]
      by auto
    with asm[rule_format, of "2" ?u ?x] have s: "(\<Sum>j \<in> {1..2}. ?u j *\<^sub>R ?x j) \<in> s"
      using mu xy by auto
    have grarr: "(\<Sum>j \<in> {Suc (Suc 0)..2}. ?u j *\<^sub>R ?x j) = (1 - \<mu>) *\<^sub>R y"
      using setsum_head_Suc[of "Suc (Suc 0)" 2 "\<lambda> j. (1 - \<mu>) *\<^sub>R y"] by auto
    from setsum_head_Suc[of "Suc 0" 2 "\<lambda> j. ?u j *\<^sub>R ?x j", simplified this]
    have "(\<Sum>j \<in> {1..2}. ?u j *\<^sub>R ?x j) = \<mu> *\<^sub>R x + (1 - \<mu>) *\<^sub>R y" by auto
    then have "(1 - \<mu>) *\<^sub>R y + \<mu> *\<^sub>R x \<in> s" using s by (auto simp:add_commute)
  }
  then show "convex s" unfolding convex_alt by auto
qed


lemma convex_explicit:
  fixes s :: "'a::real_vector set"
  shows "convex s \<longleftrightarrow>
    (\<forall>t u. finite t \<and> t \<subseteq> s \<and> (\<forall>x\<in>t. 0 \<le> u x) \<and> setsum u t = 1 \<longrightarrow> setsum (\<lambda>x. u x *\<^sub>R x) t \<in> s)"
proof safe
  fix t
  fix u :: "'a \<Rightarrow> real"
  assume "convex s" "finite t"
    "t \<subseteq> s" "\<forall>x\<in>t. 0 \<le> u x" "setsum u t = 1"
  then show "(\<Sum>x\<in>t. u x *\<^sub>R x) \<in> s"
    using convex_setsum[of t s u "\<lambda> x. x"] by auto
next
  assume asm0: "\<forall>t. \<forall> u. finite t \<and> t \<subseteq> s \<and> (\<forall>x\<in>t. 0 \<le> u x)
    \<and> setsum u t = 1 \<longrightarrow> (\<Sum>x\<in>t. u x *\<^sub>R x) \<in> s"
  show "convex s"
    unfolding convex_alt
  proof safe
    fix x y
    fix \<mu> :: real
    assume asm: "x \<in> s" "y \<in> s" "0 \<le> \<mu>" "\<mu> \<le> 1"
    { assume "x \<noteq> y"
      then have "(1 - \<mu>) *\<^sub>R x + \<mu> *\<^sub>R y \<in> s"
        using asm0[rule_format, of "{x, y}" "\<lambda> z. if z = x then 1 - \<mu> else \<mu>"]
          asm by auto }
    moreover
    { assume "x = y"
      then have "(1 - \<mu>) *\<^sub>R x + \<mu> *\<^sub>R y \<in> s"
        using asm0[rule_format, of "{x, y}" "\<lambda> z. 1"]
          asm by (auto simp:field_simps real_vector.scale_left_diff_distrib) }
    ultimately show "(1 - \<mu>) *\<^sub>R x + \<mu> *\<^sub>R y \<in> s" by blast
  qed
qed

lemma convex_finite:
  assumes "finite s"
  shows "convex s \<longleftrightarrow> (\<forall>u. (\<forall>x\<in>s. 0 \<le> u x) \<and> setsum u s = 1
                      \<longrightarrow> setsum (\<lambda>x. u x *\<^sub>R x) s \<in> s)"
  unfolding convex_explicit
proof safe
  fix t u
  assume sum: "\<forall>u. (\<forall>x\<in>s. 0 \<le> u x) \<and> setsum u s = 1 \<longrightarrow> (\<Sum>x\<in>s. u x *\<^sub>R x) \<in> s"
    and as: "finite t" "t \<subseteq> s" "\<forall>x\<in>t. 0 \<le> u x" "setsum u t = (1::real)"
  have *: "s \<inter> t = t" using as(2) by auto
  have if_distrib_arg: "\<And>P f g x. (if P then f else g) x = (if P then f x else g x)"
    by simp
  show "(\<Sum>x\<in>t. u x *\<^sub>R x) \<in> s"
   using sum[THEN spec[where x="\<lambda>x. if x\<in>t then u x else 0"]] as *
   by (auto simp: assms setsum_cases if_distrib if_distrib_arg)
qed (erule_tac x=s in allE, erule_tac x=u in allE, auto)

definition convex_on :: "'a::real_vector set \<Rightarrow> ('a \<Rightarrow> real) \<Rightarrow> bool"
  where "convex_on s f \<longleftrightarrow>
    (\<forall>x\<in>s. \<forall>y\<in>s. \<forall>u\<ge>0. \<forall>v\<ge>0. u + v = 1 \<longrightarrow> f (u *\<^sub>R x + v *\<^sub>R y) \<le> u * f x + v * f y)"

lemma convex_on_subset: "convex_on t f \<Longrightarrow> s \<subseteq> t \<Longrightarrow> convex_on s f"
  unfolding convex_on_def by auto

lemma convex_add[intro]:
  assumes "convex_on s f" "convex_on s g"
  shows "convex_on s (\<lambda>x. f x + g x)"
proof -
  { fix x y
    assume "x\<in>s" "y\<in>s"
    moreover
    fix u v :: real
    assume "0 \<le> u" "0 \<le> v" "u + v = 1"
    ultimately
    have "f (u *\<^sub>R x + v *\<^sub>R y) + g (u *\<^sub>R x + v *\<^sub>R y) \<le> (u * f x + v * f y) + (u * g x + v * g y)"
      using assms unfolding convex_on_def by (auto simp add: add_mono)
    then have "f (u *\<^sub>R x + v *\<^sub>R y) + g (u *\<^sub>R x + v *\<^sub>R y) \<le> u * (f x + g x) + v * (f y + g y)"
      by (simp add: field_simps)
  }
  then show ?thesis unfolding convex_on_def by auto
qed

lemma convex_cmul[intro]:
  assumes "0 \<le> (c::real)" "convex_on s f"
  shows "convex_on s (\<lambda>x. c * f x)"
proof-
  have *: "\<And>u c fx v fy ::real. u * (c * fx) + v * (c * fy) = c * (u * fx + v * fy)"
    by (simp add: field_simps)
  show ?thesis using assms(2) and mult_left_mono [OF _ assms(1)]
    unfolding convex_on_def and * by auto
qed

lemma convex_lower:
  assumes "convex_on s f"  "x\<in>s"  "y \<in> s"  "0 \<le> u"  "0 \<le> v"  "u + v = 1"
  shows "f (u *\<^sub>R x + v *\<^sub>R y) \<le> max (f x) (f y)"
proof-
  let ?m = "max (f x) (f y)"
  have "u * f x + v * f y \<le> u * max (f x) (f y) + v * max (f x) (f y)"
    using assms(4,5) by (auto simp add: mult_left_mono add_mono)
  also have "\<dots> = max (f x) (f y)" using assms(6) unfolding distrib[symmetric] by auto
  finally show ?thesis
    using assms unfolding convex_on_def by fastforce
qed

lemma convex_distance[intro]:
  fixes s :: "'a::real_normed_vector set"
  shows "convex_on s (\<lambda>x. dist a x)"
proof (auto simp add: convex_on_def dist_norm)
  fix x y
  assume "x\<in>s" "y\<in>s"
  fix u v :: real
  assume "0 \<le> u" "0 \<le> v" "u + v = 1"
  have "a = u *\<^sub>R a + v *\<^sub>R a"
    unfolding scaleR_left_distrib[symmetric] and `u+v=1` by simp
  then have *: "a - (u *\<^sub>R x + v *\<^sub>R y) = (u *\<^sub>R (a - x)) + (v *\<^sub>R (a - y))"
    by (auto simp add: algebra_simps)
  show "norm (a - (u *\<^sub>R x + v *\<^sub>R y)) \<le> u * norm (a - x) + v * norm (a - y)"
    unfolding * using norm_triangle_ineq[of "u *\<^sub>R (a - x)" "v *\<^sub>R (a - y)"]
    using `0 \<le> u` `0 \<le> v` by auto
qed


subsection {* Arithmetic operations on sets preserve convexity. *}

lemma convex_scaling:
  assumes "convex s"
  shows"convex ((\<lambda>x. c *\<^sub>R x) ` s)"
  using assms unfolding convex_def image_iff
proof safe
  fix x xa y xb :: "'a::real_vector"
  fix u v :: real
  assume asm: "\<forall>x\<in>s. \<forall>y\<in>s. \<forall>u\<ge>0. \<forall>v\<ge>0. u + v = 1 \<longrightarrow> u *\<^sub>R x + v *\<^sub>R y \<in> s"
    "xa \<in> s" "xb \<in> s" "0 \<le> u" "0 \<le> v" "u + v = 1"
  show "\<exists>x\<in>s. u *\<^sub>R c *\<^sub>R xa + v *\<^sub>R c *\<^sub>R xb = c *\<^sub>R x"
    using bexI[of _ "u *\<^sub>R xa +v *\<^sub>R xb"] asm by (auto simp add: algebra_simps)
qed

lemma convex_negations: "convex s \<Longrightarrow> convex ((\<lambda>x. -x)` s)"
  using assms unfolding convex_def image_iff
proof safe
  fix x xa y xb :: "'a::real_vector"
  fix u v :: real
  assume asm: "\<forall>x\<in>s. \<forall>y\<in>s. \<forall>u\<ge>0. \<forall>v\<ge>0. u + v = 1 \<longrightarrow> u *\<^sub>R x + v *\<^sub>R y \<in> s"
    "xa \<in> s" "xb \<in> s" "0 \<le> u" "0 \<le> v" "u + v = 1"
  show "\<exists>x\<in>s. u *\<^sub>R - xa + v *\<^sub>R - xb = - x"
    using bexI[of _ "u *\<^sub>R xa +v *\<^sub>R xb"] asm by auto
qed

lemma convex_sums:
  assumes "convex s" "convex t"
  shows "convex {x + y| x y. x \<in> s \<and> y \<in> t}"
  using assms unfolding convex_def image_iff
proof safe
  fix xa xb ya yb
  assume xy:"xa\<in>s" "xb\<in>s" "ya\<in>t" "yb\<in>t"
  fix u v :: real
  assume uv: "0 \<le> u" "0 \<le> v" "u + v = 1"
  show "\<exists>x y. u *\<^sub>R (xa + ya) + v *\<^sub>R (xb + yb) = x + y \<and> x \<in> s \<and> y \<in> t"
    using exI[of _ "u *\<^sub>R xa + v *\<^sub>R xb"] exI[of _ "u *\<^sub>R ya + v *\<^sub>R yb"]
      assms[unfolded convex_def] uv xy by (auto simp add:scaleR_right_distrib)
qed

lemma convex_differences:
  assumes "convex s" "convex t"
  shows "convex {x - y| x y. x \<in> s \<and> y \<in> t}"
proof -
  have "{x - y| x y. x \<in> s \<and> y \<in> t} = {x + y |x y. x \<in> s \<and> y \<in> uminus ` t}"
  proof safe
    fix x x' y
    assume "x' \<in> s" "y \<in> t"
    then show "\<exists>x y'. x' - y = x + y' \<and> x \<in> s \<and> y' \<in> uminus ` t"
      using exI[of _ x'] exI[of _ "-y"] by auto
  next
    fix x x' y y'
    assume "x' \<in> s" "y' \<in> t"
    then show "\<exists>x y. x' + - y' = x - y \<and> x \<in> s \<and> y \<in> t"
      using exI[of _ x'] exI[of _ y'] by auto
  qed
  then show ?thesis
    using convex_sums[OF assms(1) convex_negations[OF assms(2)]] by auto
qed

lemma convex_translation:
  assumes "convex s"
  shows "convex ((\<lambda>x. a + x) ` s)"
proof -
  have "{a + y |y. y \<in> s} = (\<lambda>x. a + x) ` s" by auto
  then show ?thesis
    using convex_sums[OF convex_singleton[of a] assms] by auto
qed

lemma convex_affinity:
  assumes "convex s"
  shows "convex ((\<lambda>x. a + c *\<^sub>R x) ` s)"
proof -
  have "(\<lambda>x. a + c *\<^sub>R x) ` s = op + a ` op *\<^sub>R c ` s" by auto
  then show ?thesis
    using convex_translation[OF convex_scaling[OF assms], of a c] by auto
qed

lemma convex_linear_image:
  assumes c:"convex s" and l:"bounded_linear f"
  shows "convex(f ` s)"
proof (auto simp add: convex_def)
  interpret f: bounded_linear f by fact
  fix x y
  assume xy: "x \<in> s" "y \<in> s"
  fix u v :: real
  assume uv: "0 \<le> u" "0 \<le> v" "u + v = 1"
  show "u *\<^sub>R f x + v *\<^sub>R f y \<in> f ` s" unfolding image_iff
    using bexI[of _ "u *\<^sub>R x + v *\<^sub>R y"] f.add f.scaleR
      c[unfolded convex_def] xy uv by auto
qed


lemma pos_is_convex: "convex {0 :: real <..}"
  unfolding convex_alt
proof safe
  fix y x \<mu> :: real
  assume asms: "y > 0" "x > 0" "\<mu> \<ge> 0" "\<mu> \<le> 1"
  { assume "\<mu> = 0"
    then have "\<mu> *\<^sub>R x + (1 - \<mu>) *\<^sub>R y = y" by simp
    then have "\<mu> *\<^sub>R x + (1 - \<mu>) *\<^sub>R y > 0" using asms by simp }
  moreover
  { assume "\<mu> = 1"
    then have "\<mu> *\<^sub>R x + (1 - \<mu>) *\<^sub>R y > 0" using asms by simp }
  moreover
  { assume "\<mu> \<noteq> 1" "\<mu> \<noteq> 0"
    then have "\<mu> > 0" "(1 - \<mu>) > 0" using asms by auto
    then have "\<mu> *\<^sub>R x + (1 - \<mu>) *\<^sub>R y > 0" using asms
      by (auto simp add: add_pos_pos mult_pos_pos) }
  ultimately show "(1 - \<mu>) *\<^sub>R y + \<mu> *\<^sub>R x > 0" using assms by fastforce
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
  case (insert i s) note asms = this
  then have "convex_on C f" by simp
  from this[unfolded convex_on_def, rule_format]
  have conv: "\<And>x y \<mu>. x \<in> C \<Longrightarrow> y \<in> C \<Longrightarrow> 0 \<le> \<mu> \<Longrightarrow> \<mu> \<le> 1
      \<Longrightarrow> f (\<mu> *\<^sub>R x + (1 - \<mu>) *\<^sub>R y) \<le> \<mu> * f x + (1 - \<mu>) * f y"
    by simp
  { assume "a i = 1"
    then have "(\<Sum> j \<in> s. a j) = 0"
      using asms by auto
    then have "\<And>j. j \<in> s \<Longrightarrow> a j = 0"
      using setsum_nonneg_0[where 'b=real] asms by fastforce
    then have ?case using asms by auto }
  moreover
  { assume asm: "a i \<noteq> 1"
    from asms have yai: "y i \<in> C" "a i \<ge> 0" by auto
    have fis: "finite (insert i s)" using asms by auto
    then have ai1: "a i \<le> 1" using setsum_nonneg_leq_bound[of "insert i s" a] asms by simp
    then have "a i < 1" using asm by auto
    then have i0: "1 - a i > 0" by auto
    let ?a = "\<lambda>j. a j / (1 - a i)"
    { fix j assume "j \<in> s"
      then have "?a j \<ge> 0"
        using i0 asms divide_nonneg_pos
        by fastforce }
    note a_nonneg = this
    have "(\<Sum> j \<in> insert i s. a j) = 1" using asms by auto
    then have "(\<Sum> j \<in> s. a j) = 1 - a i" using setsum.insert asms by fastforce
    then have "(\<Sum> j \<in> s. a j) / (1 - a i) = 1" using i0 by auto
    then have a1: "(\<Sum> j \<in> s. ?a j) = 1" unfolding setsum_divide_distrib by simp
    have "convex C" using asms by auto
    then have asum: "(\<Sum> j \<in> s. ?a j *\<^sub>R y j) \<in> C"
      using asms convex_setsum[OF `finite s`
        `convex C` a1 a_nonneg] by auto
    have asum_le: "f (\<Sum> j \<in> s. ?a j *\<^sub>R y j) \<le> (\<Sum> j \<in> s. ?a j * f (y j))"
      using a_nonneg a1 asms by blast
    have "f (\<Sum> j \<in> insert i s. a j *\<^sub>R y j) = f ((\<Sum> j \<in> s. a j *\<^sub>R y j) + a i *\<^sub>R y i)"
      using setsum.insert[of s i "\<lambda> j. a j *\<^sub>R y j", OF `finite s` `i \<notin> s`] asms
      by (auto simp only:add_commute)
    also have "\<dots> = f (((1 - a i) * inverse (1 - a i)) *\<^sub>R (\<Sum> j \<in> s. a j *\<^sub>R y j) + a i *\<^sub>R y i)"
      using i0 by auto
    also have "\<dots> = f ((1 - a i) *\<^sub>R (\<Sum> j \<in> s. (a j * inverse (1 - a i)) *\<^sub>R y j) + a i *\<^sub>R y i)"
      using scaleR_right.setsum[of "inverse (1 - a i)" "\<lambda> j. a j *\<^sub>R y j" s, symmetric]
      by (auto simp:algebra_simps)
    also have "\<dots> = f ((1 - a i) *\<^sub>R (\<Sum> j \<in> s. ?a j *\<^sub>R y j) + a i *\<^sub>R y i)"
      by (auto simp: divide_inverse)
    also have "\<dots> \<le> (1 - a i) *\<^sub>R f ((\<Sum> j \<in> s. ?a j *\<^sub>R y j)) + a i * f (y i)"
      using conv[of "y i" "(\<Sum> j \<in> s. ?a j *\<^sub>R y j)" "a i", OF yai(1) asum yai(2) ai1]
      by (auto simp add:add_commute)
    also have "\<dots> \<le> (1 - a i) * (\<Sum> j \<in> s. ?a j * f (y j)) + a i * f (y i)"
      using add_right_mono[OF mult_left_mono[of _ _ "1 - a i",
        OF asum_le less_imp_le[OF i0]], of "a i * f (y i)"] by simp
    also have "\<dots> = (\<Sum> j \<in> s. (1 - a i) * ?a j * f (y j)) + a i * f (y i)"
      unfolding setsum_right_distrib[of "1 - a i" "\<lambda> j. ?a j * f (y j)"] using i0 by auto
    also have "\<dots> = (\<Sum> j \<in> s. a j * f (y j)) + a i * f (y i)" using i0 by auto
    also have "\<dots> = (\<Sum> j \<in> insert i s. a j * f (y j))" using asms by auto
    finally have "f (\<Sum> j \<in> insert i s. a j *\<^sub>R y j) \<le> (\<Sum> j \<in> insert i s. a j * f (y j))"
      by simp }
  ultimately show ?case by auto
qed

lemma convex_on_alt:
  fixes C :: "'a::real_vector set"
  assumes "convex C"
  shows "convex_on C f =
  (\<forall> x \<in> C. \<forall> y \<in> C. \<forall> \<mu> :: real. \<mu> \<ge> 0 \<and> \<mu> \<le> 1
      \<longrightarrow> f (\<mu> *\<^sub>R x + (1 - \<mu>) *\<^sub>R y) \<le> \<mu> * f x + (1 - \<mu>) * f y)"
proof safe
  fix x y
  fix \<mu> :: real
  assume asms: "convex_on C f" "x \<in> C" "y \<in> C" "0 \<le> \<mu>" "\<mu> \<le> 1"
  from this[unfolded convex_on_def, rule_format]
  have "\<And>u v. \<lbrakk>0 \<le> u; 0 \<le> v; u + v = 1\<rbrakk> \<Longrightarrow> f (u *\<^sub>R x + v *\<^sub>R y) \<le> u * f x + v * f y" by auto
  from this[of "\<mu>" "1 - \<mu>", simplified] asms
  show "f (\<mu> *\<^sub>R x + (1 - \<mu>) *\<^sub>R y) \<le> \<mu> * f x + (1 - \<mu>) * f y" by auto
next
  assume asm: "\<forall>x\<in>C. \<forall>y\<in>C. \<forall>\<mu>. 0 \<le> \<mu> \<and> \<mu> \<le> 1 \<longrightarrow> f (\<mu> *\<^sub>R x + (1 - \<mu>) *\<^sub>R y) \<le> \<mu> * f x + (1 - \<mu>) * f y"
  { fix x y
    fix u v :: real
    assume lasm: "x \<in> C" "y \<in> C" "u \<ge> 0" "v \<ge> 0" "u + v = 1"
    then have[simp]: "1 - u = v" by auto
    from asm[rule_format, of x y u]
    have "f (u *\<^sub>R x + v *\<^sub>R y) \<le> u * f x + v * f y" using lasm by auto
  }
  then show "convex_on C f" unfolding convex_on_def by auto
qed

lemma convex_on_diff:
  fixes f :: "real \<Rightarrow> real"
  assumes f: "convex_on I f" and I: "x\<in>I" "y\<in>I" and t: "x < t" "t < y"
  shows "(f x - f t) / (x - t) \<le> (f x - f y) / (x - y)"
    "(f x - f y) / (x - y) \<le> (f t - f y) / (t - y)"
proof -
  def a \<equiv> "(t - y) / (x - y)"
  with t have "0 \<le> a" "0 \<le> 1 - a" by (auto simp: field_simps)
  with f `x \<in> I` `y \<in> I` have cvx: "f (a * x + (1 - a) * y) \<le> a * f x + (1 - a) * f y"
    by (auto simp: convex_on_def)
  have "a * x + (1 - a) * y = a * (x - y) + y" by (simp add: field_simps)
  also have "\<dots> = t" unfolding a_def using `x < t` `t < y` by simp
  finally have "f t \<le> a * f x + (1 - a) * f y" using cvx by simp
  also have "\<dots> = a * (f x - f y) + f y" by (simp add: field_simps)
  finally have "f t - f y \<le> a * (f x - f y)" by simp
  with t show "(f x - f t) / (x - t) \<le> (f x - f y) / (x - y)"
    by (simp add: le_divide_eq divide_le_eq field_simps a_def)
  with t show "(f x - f y) / (x - y) \<le> (f t - f y) / (t - y)"
    by (simp add: le_divide_eq divide_le_eq field_simps)
qed

lemma pos_convex_function:
  fixes f :: "real \<Rightarrow> real"
  assumes "convex C"
    and leq: "\<And>x y. \<lbrakk>x \<in> C ; y \<in> C\<rbrakk> \<Longrightarrow> f' x * (y - x) \<le> f y - f x"
  shows "convex_on C f"
  unfolding convex_on_alt[OF assms(1)]
  using assms
proof safe
  fix x y \<mu> :: real
  let ?x = "\<mu> *\<^sub>R x + (1 - \<mu>) *\<^sub>R y"
  assume asm: "convex C" "x \<in> C" "y \<in> C" "\<mu> \<ge> 0" "\<mu> \<le> 1"
  then have "1 - \<mu> \<ge> 0" by auto
  then have xpos: "?x \<in> C" using asm unfolding convex_alt by fastforce
  have geq: "\<mu> * (f x - f ?x) + (1 - \<mu>) * (f y - f ?x)
            \<ge> \<mu> * f' ?x * (x - ?x) + (1 - \<mu>) * f' ?x * (y - ?x)"
    using add_mono[OF mult_left_mono[OF leq[OF xpos asm(2)] `\<mu> \<ge> 0`]
      mult_left_mono[OF leq[OF xpos asm(3)] `1 - \<mu> \<ge> 0`]] by auto
  then have "\<mu> * f x + (1 - \<mu>) * f y - f ?x \<ge> 0"
    by (auto simp add: field_simps)
  then show "f (\<mu> *\<^sub>R x + (1 - \<mu>) *\<^sub>R y) \<le> \<mu> * f x + (1 - \<mu>) * f y"
    using convex_on_alt by auto
qed

lemma atMostAtLeast_subset_convex:
  fixes C :: "real set"
  assumes "convex C"
    and "x \<in> C" "y \<in> C" "x < y"
  shows "{x .. y} \<subseteq> C"
proof safe
  fix z assume zasm: "z \<in> {x .. y}"
  { assume asm: "x < z" "z < y"
    let ?\<mu> = "(y - z) / (y - x)"
    have "0 \<le> ?\<mu>" "?\<mu> \<le> 1" using assms asm by (auto simp add: field_simps)
    then have comb: "?\<mu> * x + (1 - ?\<mu>) * y \<in> C"
      using assms iffD1[OF convex_alt, rule_format, of C y x ?\<mu>]
      by (simp add: algebra_simps)
    have "?\<mu> * x + (1 - ?\<mu>) * y = (y - z) * x / (y - x) + (1 - (y - z) / (y - x)) * y"
      by (auto simp add: field_simps)
    also have "\<dots> = ((y - z) * x + (y - x - (y - z)) * y) / (y - x)"
      using assms unfolding add_divide_distrib by (auto simp: field_simps)
    also have "\<dots> = z"
      using assms by (auto simp: field_simps)
    finally have "z \<in> C"
      using comb by auto }
  note less = this
  show "z \<in> C" using zasm less assms
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
  { fix x y :: real
    assume asm: "x \<in> C" "y \<in> C" "y > x"
    then have ge: "y - x > 0" "y - x \<ge> 0" by auto
    from asm have le: "x - y < 0" "x - y \<le> 0" by auto
    then obtain z1 where z1: "z1 > x" "z1 < y" "f y - f x = (y - x) * f' z1"
      using subsetD[OF atMostAtLeast_subset_convex[OF `convex C` `x \<in> C` `y \<in> C` `x < y`],
        THEN f', THEN MVT2[OF `x < y`, rule_format, unfolded atLeastAtMost_iff[symmetric]]]
      by auto
    then have "z1 \<in> C" using atMostAtLeast_subset_convex
      `convex C` `x \<in> C` `y \<in> C` `x < y` by fastforce
    from z1 have z1': "f x - f y = (x - y) * f' z1"
      by (simp add:field_simps)
    obtain z2 where z2: "z2 > x" "z2 < z1" "f' z1 - f' x = (z1 - x) * f'' z2"
      using subsetD[OF atMostAtLeast_subset_convex[OF `convex C` `x \<in> C` `z1 \<in> C` `x < z1`],
        THEN f'', THEN MVT2[OF `x < z1`, rule_format, unfolded atLeastAtMost_iff[symmetric]]] z1
      by auto
    obtain z3 where z3: "z3 > z1" "z3 < y" "f' y - f' z1 = (y - z1) * f'' z3"
      using subsetD[OF atMostAtLeast_subset_convex[OF `convex C` `z1 \<in> C` `y \<in> C` `z1 < y`],
        THEN f'', THEN MVT2[OF `z1 < y`, rule_format, unfolded atLeastAtMost_iff[symmetric]]] z1
      by auto
    have "f' y - (f x - f y) / (x - y) = f' y - f' z1"
      using asm z1' by auto
    also have "\<dots> = (y - z1) * f'' z3" using z3 by auto
    finally have cool': "f' y - (f x - f y) / (x - y) = (y - z1) * f'' z3" by simp
    have A': "y - z1 \<ge> 0" using z1 by auto
    have "z3 \<in> C" using z3 asm atMostAtLeast_subset_convex
      `convex C` `x \<in> C` `z1 \<in> C` `x < z1` by fastforce
    then have B': "f'' z3 \<ge> 0" using assms by auto
    from A' B' have "(y - z1) * f'' z3 \<ge> 0" using mult_nonneg_nonneg by auto
    from cool' this have "f' y - (f x - f y) / (x - y) \<ge> 0" by auto
    from mult_right_mono_neg[OF this le(2)]
    have "f' y * (x - y) - (f x - f y) / (x - y) * (x - y) \<le> 0 * (x - y)"
      by (simp add: algebra_simps)
    then have "f' y * (x - y) - (f x - f y) \<le> 0" using le by auto
    then have res: "f' y * (x - y) \<le> f x - f y" by auto
    have "(f y - f x) / (y - x) - f' x = f' z1 - f' x"
      using asm z1 by auto
    also have "\<dots> = (z1 - x) * f'' z2" using z2 by auto
    finally have cool: "(f y - f x) / (y - x) - f' x = (z1 - x) * f'' z2" by simp
    have A: "z1 - x \<ge> 0" using z1 by auto
    have "z2 \<in> C" using z2 z1 asm atMostAtLeast_subset_convex
      `convex C` `z1 \<in> C` `y \<in> C` `z1 < y` by fastforce
    then have B: "f'' z2 \<ge> 0" using assms by auto
    from A B have "(z1 - x) * f'' z2 \<ge> 0" using mult_nonneg_nonneg by auto
    from cool this have "(f y - f x) / (y - x) - f' x \<ge> 0" by auto
    from mult_right_mono[OF this ge(2)]
    have "(f y - f x) / (y - x) * (y - x) - f' x * (y - x) \<ge> 0 * (y - x)"
      by (simp add: algebra_simps)
    then have "f y - f x - f' x * (y - x) \<ge> 0" using ge by auto
    then have "f y - f x \<ge> f' x * (y - x)" "f' y * (x - y) \<le> f x - f y"
      using res by auto } note less_imp = this
  { fix x y :: real
    assume "x \<in> C" "y \<in> C" "x \<noteq> y"
    then have"f y - f x \<ge> f' x * (y - x)"
    unfolding neq_iff using less_imp by auto } note neq_imp = this
  moreover
  { fix x y :: real
    assume asm: "x \<in> C" "y \<in> C" "x = y"
    then have "f y - f x \<ge> f' x * (y - x)" by auto }
  ultimately show ?thesis using assms by blast
qed

lemma f''_ge0_imp_convex:
  fixes f :: "real \<Rightarrow> real"
  assumes conv: "convex C"
    and f': "\<And>x. x \<in> C \<Longrightarrow> DERIV f x :> (f' x)"
    and f'': "\<And>x. x \<in> C \<Longrightarrow> DERIV f' x :> (f'' x)"
    and pos: "\<And>x. x \<in> C \<Longrightarrow> f'' x \<ge> 0"
  shows "convex_on C f"
using f''_imp_f'[OF conv f' f'' pos] assms pos_convex_function by fastforce

lemma minus_log_convex:
  fixes b :: real
  assumes "b > 1"
  shows "convex_on {0 <..} (\<lambda> x. - log b x)"
proof -
  have "\<And>z. z > 0 \<Longrightarrow> DERIV (log b) z :> 1 / (ln b * z)" using DERIV_log by auto
  then have f': "\<And>z. z > 0 \<Longrightarrow> DERIV (\<lambda> z. - log b z) z :> - 1 / (ln b * z)"
    using DERIV_minus by auto
  have "\<And>z :: real. z > 0 \<Longrightarrow> DERIV inverse z :> - (inverse z ^ Suc (Suc 0))"
    using less_imp_neq[THEN not_sym, THEN DERIV_inverse] by auto
  from this[THEN DERIV_cmult, of _ "- 1 / ln b"]
  have "\<And>z :: real. z > 0 \<Longrightarrow>
    DERIV (\<lambda> z. (- 1 / ln b) * inverse z) z :> (- 1 / ln b) * (- (inverse z ^ Suc (Suc 0)))"
    by auto
  then have f''0: "\<And>z :: real. z > 0 \<Longrightarrow> DERIV (\<lambda> z. - 1 / (ln b * z)) z :> 1 / (ln b * z * z)"
    unfolding inverse_eq_divide by (auto simp add: mult_assoc)
  have f''_ge0: "\<And>z :: real. z > 0 \<Longrightarrow> 1 / (ln b * z * z) \<ge> 0"
    using `b > 1` by (auto intro!:less_imp_le simp add: divide_pos_pos[of 1] mult_pos_pos)
  from f''_ge0_imp_convex[OF pos_is_convex,
    unfolded greaterThan_iff, OF f' f''0 f''_ge0]
  show ?thesis by auto
qed

end
