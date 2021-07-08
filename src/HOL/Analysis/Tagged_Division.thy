(*  Title:      HOL/Analysis/Tagged_Division.thy
    Author:     John Harrison
    Author:     Robert Himmelmann, TU Muenchen (Translation from HOL light); proofs reworked by LCP
*)

section \<open>Tagged Divisions for Henstock-Kurzweil Integration\<close>

theory Tagged_Division
  imports Topology_Euclidean_Space
begin

lemma sum_Sigma_product:
  assumes "finite S"
    and "\<And>i. i \<in> S \<Longrightarrow> finite (T i)"
  shows "(\<Sum>i\<in>S. sum (x i) (T i)) = (\<Sum>(i, j)\<in>Sigma S T. x i j)"
  using assms
proof induct
  case empty
  then show ?case
    by simp
next
  case (insert a S)
  show ?case
    by (simp add: insert.hyps(1) insert.prems sum.Sigma)
qed

lemmas scaleR_simps = scaleR_zero_left scaleR_minus_left scaleR_left_diff_distrib
  scaleR_zero_right scaleR_minus_right scaleR_right_diff_distrib scaleR_eq_0_iff
  scaleR_cancel_left scaleR_cancel_right scaleR_add_right scaleR_add_left real_vector_class.scaleR_one


subsection\<^marker>\<open>tag unimportant\<close> \<open>Sundries\<close>


text\<open>A transitive relation is well-founded if all initial segments are finite.\<close>
lemma wf_finite_segments:
  assumes "irrefl r" and "trans r" and "\<And>x. finite {y. (y, x) \<in> r}"
  shows "wf (r)"
  apply (simp add: trans_wf_iff wf_iff_acyclic_if_finite converse_def assms)
  using acyclic_def assms irrefl_def trans_Restr by fastforce

text\<open>For creating values between \<^term>\<open>u\<close> and \<^term>\<open>v\<close>.\<close>
lemma scaling_mono:
  fixes u::"'a::linordered_field"
  assumes "u \<le> v" "0 \<le> r" "r \<le> s"
    shows "u + r * (v - u) / s \<le> v"
proof -
  have "r/s \<le> 1" using assms
    using divide_le_eq_1 by fastforce
  then have "(r/s) * (v - u) \<le> 1 * (v - u)"
    by (meson diff_ge_0_iff_ge mult_right_mono \<open>u \<le> v\<close>)
  then show ?thesis
    by (simp add: field_simps)
qed

subsection \<open>Some useful lemmas about intervals\<close>

lemma interior_subset_union_intervals:
  assumes "i = cbox a b"
    and "j = cbox c d"
    and "interior j \<noteq> {}"
    and "i \<subseteq> j \<union> S"
    and "interior i \<inter> interior j = {}"
  shows "interior i \<subseteq> interior S"
proof -
  have "box a b \<inter> cbox c d = {}"
     using Int_interval_mixed_eq_empty[of c d a b] assms
     unfolding interior_cbox by auto
  moreover
  have "box a b \<subseteq> cbox c d \<union> S"
    apply (rule order_trans,rule box_subset_cbox)
    using assms by auto
  ultimately
  show ?thesis
    unfolding assms interior_cbox
      by auto (metis IntI UnE empty_iff interior_maximal open_box subsetCE subsetI)
qed

lemma interior_Union_subset_cbox:
  assumes "finite f"
  assumes f: "\<And>s. s \<in> f \<Longrightarrow> \<exists>a b. s = cbox a b" "\<And>s. s \<in> f \<Longrightarrow> interior s \<subseteq> t"
    and t: "closed t"
  shows "interior (\<Union>f) \<subseteq> t"
proof -
  have [simp]: "s \<in> f \<Longrightarrow> closed s" for s
    using f by auto
  define E where "E = {s\<in>f. interior s = {}}"
  then have "finite E" "E \<subseteq> {s\<in>f. interior s = {}}"
    using \<open>finite f\<close> by auto
  then have "interior (\<Union>f) = interior (\<Union>(f - E))"
  proof (induction E rule: finite_subset_induct')
    case (insert s f')
    have "interior (\<Union>(f - insert s f') \<union> s) = interior (\<Union>(f - insert s f'))"
      using insert.hyps \<open>finite f\<close> by (intro interior_closed_Un_empty_interior) auto
    also have "\<Union>(f - insert s f') \<union> s = \<Union>(f - f')"
      using insert.hyps by auto
    finally show ?case
      by (simp add: insert.IH)
  qed simp
  also have "\<dots> \<subseteq> \<Union>(f - E)"
    by (rule interior_subset)
  also have "\<dots> \<subseteq> t"
  proof (rule Union_least)
    fix s assume "s \<in> f - E"
    with f[of s] obtain a b where s: "s \<in> f" "s = cbox a b" "box a b \<noteq> {}"
      by (fastforce simp: E_def)
    have "closure (interior s) \<subseteq> closure t"
      by (intro closure_mono f \<open>s \<in> f\<close>)
    with s \<open>closed t\<close> show "s \<subseteq> t"
      by simp
  qed
  finally show ?thesis .
qed

lemma Int_interior_Union_intervals:
    "\<lbrakk>finite \<F>; open S; \<And>T. T\<in>\<F> \<Longrightarrow> \<exists>a b. T = cbox a b; \<And>T. T\<in>\<F> \<Longrightarrow> S \<inter> (interior T) = {}\<rbrakk> 
    \<Longrightarrow> S \<inter> interior (\<Union>\<F>) = {}"
  using interior_Union_subset_cbox[of \<F> "UNIV - S"] by auto

lemma interval_split:
  fixes a :: "'a::euclidean_space"
  assumes "k \<in> Basis"
  shows
    "cbox a b \<inter> {x. x\<bullet>k \<le> c} = cbox a (\<Sum>i\<in>Basis. (if i = k then min (b\<bullet>k) c else b\<bullet>i) *\<^sub>R i)"
    "cbox a b \<inter> {x. x\<bullet>k \<ge> c} = cbox (\<Sum>i\<in>Basis. (if i = k then max (a\<bullet>k) c else a\<bullet>i) *\<^sub>R i) b"
  using assms by (rule_tac set_eqI; auto simp: mem_box)+

lemma interval_not_empty: "\<forall>i\<in>Basis. a\<bullet>i \<le> b\<bullet>i \<Longrightarrow> cbox a b \<noteq> {}"
  by (simp add: box_ne_empty)

subsection \<open>Bounds on intervals where they exist\<close>

definition\<^marker>\<open>tag important\<close> interval_upperbound :: "('a::euclidean_space) set \<Rightarrow> 'a"
  where "interval_upperbound s = (\<Sum>i\<in>Basis. (SUP x\<in>s. x\<bullet>i) *\<^sub>R i)"

definition\<^marker>\<open>tag important\<close> interval_lowerbound :: "('a::euclidean_space) set \<Rightarrow> 'a"
  where "interval_lowerbound s = (\<Sum>i\<in>Basis. (INF x\<in>s. x\<bullet>i) *\<^sub>R i)"

lemma interval_upperbound[simp]:
  "\<forall>i\<in>Basis. a\<bullet>i \<le> b\<bullet>i \<Longrightarrow>
    interval_upperbound (cbox a b) = (b::'a::euclidean_space)"
  unfolding interval_upperbound_def euclidean_representation_sum cbox_def
  by (safe intro!: cSup_eq) auto

lemma interval_lowerbound[simp]:
  "\<forall>i\<in>Basis. a\<bullet>i \<le> b\<bullet>i \<Longrightarrow>
    interval_lowerbound (cbox a b) = (a::'a::euclidean_space)"
  unfolding interval_lowerbound_def euclidean_representation_sum cbox_def
  by (safe intro!: cInf_eq) auto

lemmas interval_bounds = interval_upperbound interval_lowerbound

lemma
  fixes X::"real set"
  shows interval_upperbound_real[simp]: "interval_upperbound X = Sup X"
    and interval_lowerbound_real[simp]: "interval_lowerbound X = Inf X"
  by (auto simp: interval_upperbound_def interval_lowerbound_def)

lemma interval_bounds'[simp]:
  assumes "cbox a b \<noteq> {}"
  shows "interval_upperbound (cbox a b) = b"
    and "interval_lowerbound (cbox a b) = a"
  using assms unfolding box_ne_empty by auto

lemma interval_upperbound_Times:
  assumes "A \<noteq> {}" and "B \<noteq> {}"
  shows "interval_upperbound (A \<times> B) = (interval_upperbound A, interval_upperbound B)"
proof-
  from assms have fst_image_times': "A = fst ` (A \<times> B)" by simp
  have "(\<Sum>i\<in>Basis. (SUP x\<in>A \<times> B. x \<bullet> (i, 0)) *\<^sub>R i) = (\<Sum>i\<in>Basis. (SUP x\<in>A. x \<bullet> i) *\<^sub>R i)"
      by (subst (2) fst_image_times') (simp del: fst_image_times add: image_comp inner_Pair_0)
  moreover from assms have snd_image_times': "B = snd ` (A \<times> B)" by simp
  have "(\<Sum>i\<in>Basis. (SUP x\<in>A \<times> B. x \<bullet> (0, i)) *\<^sub>R i) = (\<Sum>i\<in>Basis. (SUP x\<in>B. x \<bullet> i) *\<^sub>R i)"
      by (subst (2) snd_image_times') (simp del: snd_image_times add: image_comp inner_Pair_0)
  ultimately show ?thesis unfolding interval_upperbound_def
      by (subst sum_Basis_prod_eq) (auto simp add: sum_prod)
qed

lemma interval_lowerbound_Times:
  assumes "A \<noteq> {}" and "B \<noteq> {}"
  shows "interval_lowerbound (A \<times> B) = (interval_lowerbound A, interval_lowerbound B)"
proof-
  from assms have fst_image_times': "A = fst ` (A \<times> B)" by simp
  have "(\<Sum>i\<in>Basis. (INF x\<in>A \<times> B. x \<bullet> (i, 0)) *\<^sub>R i) = (\<Sum>i\<in>Basis. (INF x\<in>A. x \<bullet> i) *\<^sub>R i)"
      by (subst (2) fst_image_times') (simp del: fst_image_times add: image_comp inner_Pair_0)
  moreover from assms have snd_image_times': "B = snd ` (A \<times> B)" by simp
  have "(\<Sum>i\<in>Basis. (INF x\<in>A \<times> B. x \<bullet> (0, i)) *\<^sub>R i) = (\<Sum>i\<in>Basis. (INF x\<in>B. x \<bullet> i) *\<^sub>R i)"
      by (subst (2) snd_image_times') (simp del: snd_image_times add: image_comp inner_Pair_0)
  ultimately show ?thesis unfolding interval_lowerbound_def
      by (subst sum_Basis_prod_eq) (auto simp add: sum_prod)
qed

subsection \<open>The notion of a gauge --- simply an open set containing the point\<close>

definition\<^marker>\<open>tag important\<close> "gauge \<gamma> \<longleftrightarrow> (\<forall>x. x \<in> \<gamma> x \<and> open (\<gamma> x))"

lemma gaugeI:
  assumes "\<And>x. x \<in> \<gamma> x"
    and "\<And>x. open (\<gamma> x)"
  shows "gauge \<gamma>"
  using assms unfolding gauge_def by auto

lemma gaugeD[dest]:
  assumes "gauge \<gamma>"
  shows "x \<in> \<gamma> x"
    and "open (\<gamma> x)"
  using assms unfolding gauge_def by auto

lemma gauge_ball_dependent: "\<forall>x. 0 < e x \<Longrightarrow> gauge (\<lambda>x. ball x (e x))"
  unfolding gauge_def by auto

lemma gauge_ball[intro]: "0 < e \<Longrightarrow> gauge (\<lambda>x. ball x e)"
  unfolding gauge_def by auto

lemma gauge_trivial[intro!]: "gauge (\<lambda>x. ball x 1)"
  by (rule gauge_ball) auto

lemma gauge_Int[intro]: "gauge \<gamma>1 \<Longrightarrow> gauge \<gamma>2 \<Longrightarrow> gauge (\<lambda>x. \<gamma>1 x \<inter> \<gamma>2 x)"
  unfolding gauge_def by auto

lemma gauge_reflect:
  fixes \<gamma> :: "'a::euclidean_space \<Rightarrow> 'a set"
  shows "gauge \<gamma> \<Longrightarrow> gauge (\<lambda>x. uminus ` \<gamma> (- x))"
  using equation_minus_iff
  by (auto simp: gauge_def surj_def intro!: open_surjective_linear_image linear_uminus)

lemma gauge_Inter:
  assumes "finite S"
    and "\<And>u. u\<in>S \<Longrightarrow> gauge (f u)"
  shows "gauge (\<lambda>x. \<Inter>{f u x | u. u \<in> S})"
proof -
  have *: "\<And>x. {f u x |u. u \<in> S} = (\<lambda>u. f u x) ` S"
    by auto
  show ?thesis
    unfolding gauge_def unfolding *
    using assms unfolding Ball_def Inter_iff mem_Collect_eq gauge_def by auto
qed

lemma gauge_existence_lemma:
  "(\<forall>x. \<exists>d :: real. p x \<longrightarrow> 0 < d \<and> q d x) \<longleftrightarrow> (\<forall>x. \<exists>d>0. p x \<longrightarrow> q d x)"
  by (metis zero_less_one)

subsection \<open>Attempt a systematic general set of "offset" results for components\<close>
(*FIXME Restructure, the subsection consists only of 1 lemma *)
lemma gauge_modify:
  assumes "(\<forall>S. open S \<longrightarrow> open {x. f(x) \<in> S})" "gauge d"
  shows "gauge (\<lambda>x. {y. f y \<in> d (f x)})"
  using assms unfolding gauge_def by force

subsection \<open>Divisions\<close>

definition\<^marker>\<open>tag important\<close> division_of (infixl "division'_of" 40)
where
  "s division_of i \<longleftrightarrow>
    finite s \<and>
    (\<forall>K\<in>s. K \<subseteq> i \<and> K \<noteq> {} \<and> (\<exists>a b. K = cbox a b)) \<and>
    (\<forall>K1\<in>s. \<forall>K2\<in>s. K1 \<noteq> K2 \<longrightarrow> interior(K1) \<inter> interior(K2) = {}) \<and>
    (\<Union>s = i)"

lemma division_ofD[dest]:
  assumes "s division_of i"
  shows "finite s"
    and "\<And>K. K \<in> s \<Longrightarrow> K \<subseteq> i"
    and "\<And>K. K \<in> s \<Longrightarrow> K \<noteq> {}"
    and "\<And>K. K \<in> s \<Longrightarrow> \<exists>a b. K = cbox a b"
    and "\<And>K1 K2. K1 \<in> s \<Longrightarrow> K2 \<in> s \<Longrightarrow> K1 \<noteq> K2 \<Longrightarrow> interior(K1) \<inter> interior(K2) = {}"
    and "\<Union>s = i"
  using assms unfolding division_of_def by auto

lemma division_ofI:
  assumes "finite s"
    and "\<And>K. K \<in> s \<Longrightarrow> K \<subseteq> i"
    and "\<And>K. K \<in> s \<Longrightarrow> K \<noteq> {}"
    and "\<And>K. K \<in> s \<Longrightarrow> \<exists>a b. K = cbox a b"
    and "\<And>K1 K2. K1 \<in> s \<Longrightarrow> K2 \<in> s \<Longrightarrow> K1 \<noteq> K2 \<Longrightarrow> interior K1 \<inter> interior K2 = {}"
    and "\<Union>s = i"
  shows "s division_of i"
  using assms unfolding division_of_def by auto

lemma division_of_finite: "s division_of i \<Longrightarrow> finite s"
  by auto

lemma division_of_self[intro]: "cbox a b \<noteq> {} \<Longrightarrow> {cbox a b} division_of (cbox a b)"
  unfolding division_of_def by auto

lemma division_of_trivial[simp]: "s division_of {} \<longleftrightarrow> s = {}"
  unfolding division_of_def by auto

lemma division_of_sing[simp]:
  "s division_of cbox a (a::'a::euclidean_space) \<longleftrightarrow> s = {cbox a a}"
  (is "?l = ?r")
proof
  assume ?r
  moreover
  { fix K
    assume "s = {{a}}" "K\<in>s"
    then have "\<exists>x y. K = cbox x y"
      apply (rule_tac x=a in exI)+
      apply force
      done
  }
  ultimately show ?l
    unfolding division_of_def cbox_sing by auto
next
  assume ?l
  have "x = {a}" if  "x \<in> s" for x
    by (metis \<open>s division_of cbox a a\<close> cbox_sing division_ofD(2) division_ofD(3) subset_singletonD that)
  moreover have "s \<noteq> {}"
    using \<open>s division_of cbox a a\<close> by auto
  ultimately show ?r
    unfolding cbox_sing by auto
qed

lemma elementary_empty: obtains p where "p division_of {}"
  unfolding division_of_trivial by auto

lemma elementary_interval: obtains p where "p division_of (cbox a b)"
  by (metis division_of_trivial division_of_self)

lemma division_contains: "s division_of i \<Longrightarrow> \<forall>x\<in>i. \<exists>k\<in>s. x \<in> k"
  unfolding division_of_def by auto

lemma forall_in_division:
  "d division_of i \<Longrightarrow> (\<forall>x\<in>d. P x) \<longleftrightarrow> (\<forall>a b. cbox a b \<in> d \<longrightarrow> P (cbox a b))"
  unfolding division_of_def by fastforce

lemma cbox_division_memE:
  assumes \<D>: "K \<in> \<D>" "\<D> division_of S"
  obtains a b where "K = cbox a b" "K \<noteq> {}" "K \<subseteq> S"
  using assms unfolding division_of_def by metis

lemma division_of_subset:
  assumes "p division_of (\<Union>p)"
    and "q \<subseteq> p"
  shows "q division_of (\<Union>q)"
proof (rule division_ofI)
  note * = division_ofD[OF assms(1)]
  show "finite q"
    using "*"(1) assms(2) infinite_super by auto
  {
    fix k
    assume "k \<in> q"
    then have kp: "k \<in> p"
      using assms(2) by auto
    show "k \<subseteq> \<Union>q"
      using \<open>k \<in> q\<close> by auto
    show "\<exists>a b. k = cbox a b"
      using *(4)[OF kp] by auto
    show "k \<noteq> {}"
      using *(3)[OF kp] by auto
  }
  fix k1 k2
  assume "k1 \<in> q" "k2 \<in> q" "k1 \<noteq> k2"
  then have **: "k1 \<in> p" "k2 \<in> p" "k1 \<noteq> k2"
    using assms(2) by auto
  show "interior k1 \<inter> interior k2 = {}"
    using *(5)[OF **] by auto
qed auto

lemma division_of_union_self[intro]: "p division_of s \<Longrightarrow> p division_of (\<Union>p)"
  unfolding division_of_def by auto

lemma division_inter:
  fixes s1 s2 :: "'a::euclidean_space set"
  assumes "p1 division_of s1"
    and "p2 division_of s2"
  shows "{k1 \<inter> k2 | k1 k2. k1 \<in> p1 \<and> k2 \<in> p2 \<and> k1 \<inter> k2 \<noteq> {}} division_of (s1 \<inter> s2)"
  (is "?A' division_of _")
proof -
  let ?A = "{s. s \<in>  (\<lambda>(k1,k2). k1 \<inter> k2) ` (p1 \<times> p2) \<and> s \<noteq> {}}"
  have *: "?A' = ?A" by auto
  show ?thesis
    unfolding *
  proof (rule division_ofI)
    have "?A \<subseteq> (\<lambda>(x, y). x \<inter> y) ` (p1 \<times> p2)"
      by auto
    moreover have "finite (p1 \<times> p2)"
      using assms unfolding division_of_def by auto
    ultimately show "finite ?A" by auto
    have *: "\<And>s. \<Union>{x\<in>s. x \<noteq> {}} = \<Union>s"
      by auto
    show "\<Union>?A = s1 \<inter> s2"
      unfolding * 
      using division_ofD(6)[OF assms(1)] and division_ofD(6)[OF assms(2)] by auto
    {
      fix k
      assume "k \<in> ?A"
      then obtain k1 k2 where k: "k = k1 \<inter> k2" "k1 \<in> p1" "k2 \<in> p2" "k \<noteq> {}"
        by auto
      then show "k \<noteq> {}"
        by auto
      show "k \<subseteq> s1 \<inter> s2"
        using division_ofD(2)[OF assms(1) k(2)] and division_ofD(2)[OF assms(2) k(3)]
        unfolding k by auto
      obtain a1 b1 where k1: "k1 = cbox a1 b1"
        using division_ofD(4)[OF assms(1) k(2)] by blast
      obtain a2 b2 where k2: "k2 = cbox a2 b2"
        using division_ofD(4)[OF assms(2) k(3)] by blast
      show "\<exists>a b. k = cbox a b"
        unfolding k k1 k2 unfolding Int_interval by auto
    }
    fix k1 k2
    assume "k1 \<in> ?A"
    then obtain x1 y1 where k1: "k1 = x1 \<inter> y1" "x1 \<in> p1" "y1 \<in> p2" "k1 \<noteq> {}"
      by auto
    assume "k2 \<in> ?A"
    then obtain x2 y2 where k2: "k2 = x2 \<inter> y2" "x2 \<in> p1" "y2 \<in> p2" "k2 \<noteq> {}"
      by auto
    assume "k1 \<noteq> k2"
    then have th: "x1 \<noteq> x2 \<or> y1 \<noteq> y2"
      unfolding k1 k2 by auto
    have *: "interior x1 \<inter> interior x2 = {} \<or> interior y1 \<inter> interior y2 = {} \<Longrightarrow>
      interior (x1 \<inter> y1) \<subseteq> interior x1 \<Longrightarrow> interior (x1 \<inter> y1) \<subseteq> interior y1 \<Longrightarrow>
      interior (x2 \<inter> y2) \<subseteq> interior x2 \<Longrightarrow> interior (x2 \<inter> y2) \<subseteq> interior y2 \<Longrightarrow>
      interior (x1 \<inter> y1) \<inter> interior (x2 \<inter> y2) = {}" by auto
    show "interior k1 \<inter> interior k2 = {}"
      unfolding k1 k2
      apply (rule *)
      using assms division_ofD(5) k1 k2(2) k2(3) th apply auto
      done
  qed
qed

lemma division_inter_1:
  assumes "d division_of i"
    and "cbox a (b::'a::euclidean_space) \<subseteq> i"
  shows "{cbox a b \<inter> k | k. k \<in> d \<and> cbox a b \<inter> k \<noteq> {}} division_of (cbox a b)"
proof (cases "cbox a b = {}")
  case True
  show ?thesis
    unfolding True and division_of_trivial by auto
next
  case False
  have *: "cbox a b \<inter> i = cbox a b" using assms(2) by auto
  show ?thesis
    using division_inter[OF division_of_self[OF False] assms(1)]
    unfolding * by auto
qed

lemma elementary_Int:
  fixes s t :: "'a::euclidean_space set"
  assumes "p1 division_of s"
    and "p2 division_of t"
  shows "\<exists>p. p division_of (s \<inter> t)"
using assms division_inter by blast

lemma elementary_Inter:
  assumes "finite f"
    and "f \<noteq> {}"
    and "\<forall>s\<in>f. \<exists>p. p division_of (s::('a::euclidean_space) set)"
  shows "\<exists>p. p division_of (\<Inter>f)"
  using assms
proof (induct f rule: finite_induct)
  case (insert x f)
  show ?case
  proof (cases "f = {}")
    case True
    then show ?thesis
      unfolding True using insert by auto
  next
    case False
    obtain p where "p division_of \<Inter>f"
      using insert(3)[OF False insert(5)[unfolded ball_simps,THEN conjunct2]] ..
    moreover obtain px where "px division_of x"
      using insert(5)[rule_format,OF insertI1] ..
    ultimately show ?thesis
      by (simp add: elementary_Int Inter_insert)
  qed
qed auto

lemma division_disjoint_union:
  assumes "p1 division_of s1"
    and "p2 division_of s2"
    and "interior s1 \<inter> interior s2 = {}"
  shows "(p1 \<union> p2) division_of (s1 \<union> s2)"
proof (rule division_ofI)
  note d1 = division_ofD[OF assms(1)]
  note d2 = division_ofD[OF assms(2)]
  show "finite (p1 \<union> p2)"
    using d1(1) d2(1) by auto
  show "\<Union>(p1 \<union> p2) = s1 \<union> s2"
    using d1(6) d2(6) by auto
  {
    fix k1 k2
    assume as: "k1 \<in> p1 \<union> p2" "k2 \<in> p1 \<union> p2" "k1 \<noteq> k2"
    moreover
    let ?g="interior k1 \<inter> interior k2 = {}"
    {
      assume as: "k1\<in>p1" "k2\<in>p2"
      have ?g
        using interior_mono[OF d1(2)[OF as(1)]] interior_mono[OF d2(2)[OF as(2)]]
        using assms(3) by blast
    }
    moreover
    {
      assume as: "k1\<in>p2" "k2\<in>p1"
      have ?g
        using interior_mono[OF d1(2)[OF as(2)]] interior_mono[OF d2(2)[OF as(1)]]
        using assms(3) by blast
    }
    ultimately show ?g
      using d1(5)[OF _ _ as(3)] and d2(5)[OF _ _ as(3)] by auto
  }
  fix k
  assume k: "k \<in> p1 \<union> p2"
  show "k \<subseteq> s1 \<union> s2"
    using k d1(2) d2(2) by auto
  show "k \<noteq> {}"
    using k d1(3) d2(3) by auto
  show "\<exists>a b. k = cbox a b"
    using k d1(4) d2(4) by auto
qed

lemma partial_division_extend_1:
  fixes a b c d :: "'a::euclidean_space"
  assumes incl: "cbox c d \<subseteq> cbox a b"
    and nonempty: "cbox c d \<noteq> {}"
  obtains p where "p division_of (cbox a b)" "cbox c d \<in> p"
proof
  let ?B = "\<lambda>f::'a\<Rightarrow>'a \<times> 'a.
    cbox (\<Sum>i\<in>Basis. (fst (f i) \<bullet> i) *\<^sub>R i) (\<Sum>i\<in>Basis. (snd (f i) \<bullet> i) *\<^sub>R i)"
  define p where "p = ?B ` (Basis \<rightarrow>\<^sub>E {(a, c), (c, d), (d, b)})"

  show "cbox c d \<in> p"
    unfolding p_def
    by (auto simp add: box_eq_empty cbox_def intro!: image_eqI[where x="\<lambda>(i::'a)\<in>Basis. (c, d)"])
  have ord: "a \<bullet> i \<le> c \<bullet> i" "c \<bullet> i \<le> d \<bullet> i" "d \<bullet> i \<le> b \<bullet> i" if "i \<in> Basis" for i
    using incl nonempty that
    unfolding box_eq_empty subset_box by (auto simp: not_le)

  show "p division_of (cbox a b)"
  proof (rule division_ofI)
    show "finite p"
      unfolding p_def by (auto intro!: finite_PiE)
    {
      fix k
      assume "k \<in> p"
      then obtain f where f: "f \<in> Basis \<rightarrow>\<^sub>E {(a, c), (c, d), (d, b)}" and k: "k = ?B f"
        by (auto simp: p_def)
      then show "\<exists>a b. k = cbox a b"
        by auto
      have "k \<subseteq> cbox a b \<and> k \<noteq> {}"
      proof (simp add: k box_eq_empty subset_box not_less, safe)
        fix i :: 'a
        assume i: "i \<in> Basis"
        with f have "f i = (a, c) \<or> f i = (c, d) \<or> f i = (d, b)"
          by (auto simp: PiE_iff)
        with i ord[of i]
        show "a \<bullet> i \<le> fst (f i) \<bullet> i" "snd (f i) \<bullet> i \<le> b \<bullet> i" "fst (f i) \<bullet> i \<le> snd (f i) \<bullet> i"
          by auto
      qed
      then show "k \<noteq> {}" "k \<subseteq> cbox a b"
        by auto
      {
        fix l
        assume "l \<in> p"
        then obtain g where g: "g \<in> Basis \<rightarrow>\<^sub>E {(a, c), (c, d), (d, b)}" and l: "l = ?B g"
          by (auto simp: p_def)
        assume "l \<noteq> k"
        have "\<exists>i\<in>Basis. f i \<noteq> g i"
        proof (rule ccontr)
          assume "\<not> ?thesis"
          with f g have "f = g"
            by (auto simp: PiE_iff extensional_def fun_eq_iff)
          with \<open>l \<noteq> k\<close> show False
            by (simp add: l k)
        qed
        then obtain i where *: "i \<in> Basis" "f i \<noteq> g i" ..
        then have "f i = (a, c) \<or> f i = (c, d) \<or> f i = (d, b)"
                  "g i = (a, c) \<or> g i = (c, d) \<or> g i = (d, b)"
          using f g by (auto simp: PiE_iff)
        with * ord[of i] show "interior l \<inter> interior k = {}"
          by (auto simp add: l k disjoint_interval intro!: bexI[of _ i])
      }
      note \<open>k \<subseteq> cbox a b\<close>
    }
    moreover
    {
      fix x assume x: "x \<in> cbox a b"
      have "\<forall>i\<in>Basis. \<exists>l. x \<bullet> i \<in> {fst l \<bullet> i .. snd l \<bullet> i} \<and> l \<in> {(a, c), (c, d), (d, b)}"
      proof
        fix i :: 'a
        assume "i \<in> Basis"
        with x ord[of i]
        have "(a \<bullet> i \<le> x \<bullet> i \<and> x \<bullet> i \<le> c \<bullet> i) \<or> (c \<bullet> i \<le> x \<bullet> i \<and> x \<bullet> i \<le> d \<bullet> i) \<or>
            (d \<bullet> i \<le> x \<bullet> i \<and> x \<bullet> i \<le> b \<bullet> i)"
          by (auto simp: cbox_def)
        then show "\<exists>l. x \<bullet> i \<in> {fst l \<bullet> i .. snd l \<bullet> i} \<and> l \<in> {(a, c), (c, d), (d, b)}"
          by auto
      qed
      then obtain f where
        f: "\<forall>i\<in>Basis. x \<bullet> i \<in> {fst (f i) \<bullet> i..snd (f i) \<bullet> i} \<and> f i \<in> {(a, c), (c, d), (d, b)}"
        unfolding bchoice_iff ..
      moreover from f have "restrict f Basis \<in> Basis \<rightarrow>\<^sub>E {(a, c), (c, d), (d, b)}"
        by auto
      moreover from f have "x \<in> ?B (restrict f Basis)"
        by (auto simp: mem_box)
      ultimately have "\<exists>k\<in>p. x \<in> k"
        unfolding p_def by blast
    }
    ultimately show "\<Union>p = cbox a b"
      by auto
  qed
qed

proposition partial_division_extend_interval:
  assumes "p division_of (\<Union>p)" "(\<Union>p) \<subseteq> cbox a b"
  obtains q where "p \<subseteq> q" "q division_of cbox a (b::'a::euclidean_space)"
proof (cases "p = {}")
  case True
  obtain q where "q division_of (cbox a b)"
    by (rule elementary_interval)
  then show ?thesis
    using True that by blast
next
  case False
  note p = division_ofD[OF assms(1)]
  have div_cbox: "\<forall>k\<in>p. \<exists>q. q division_of cbox a b \<and> k \<in> q"
  proof
    fix k
    assume kp: "k \<in> p"
    obtain c d where k: "k = cbox c d"
      using p(4)[OF kp] by blast
    have *: "cbox c d \<subseteq> cbox a b" "cbox c d \<noteq> {}"
      using p(2,3)[OF kp, unfolded k] using assms(2)
      by (blast intro: order.trans)+
    obtain q where "q division_of cbox a b" "cbox c d \<in> q"
      by (rule partial_division_extend_1[OF *])
    then show "\<exists>q. q division_of cbox a b \<and> k \<in> q"
      unfolding k by auto
  qed
  obtain q where q: "\<And>x. x \<in> p \<Longrightarrow> q x division_of cbox a b" "\<And>x. x \<in> p \<Longrightarrow> x \<in> q x"
    using bchoice[OF div_cbox] by blast
  have "q x division_of \<Union>(q x)" if x: "x \<in> p" for x
    apply (rule division_ofI)
    using division_ofD[OF q(1)[OF x]] by auto
  then have di: "\<And>x. x \<in> p \<Longrightarrow> \<exists>d. d division_of \<Union>(q x - {x})"
    by (meson Diff_subset division_of_subset)
  have "\<exists>d. d division_of \<Inter>((\<lambda>i. \<Union>(q i - {i})) ` p)"
    apply (rule elementary_Inter [OF finite_imageI[OF p(1)]])
    apply (auto dest: di simp: False elementary_Inter [OF finite_imageI[OF p(1)]])
    done
  then obtain d where d: "d division_of \<Inter>((\<lambda>i. \<Union>(q i - {i})) ` p)" ..
  have "d \<union> p division_of cbox a b"
  proof -
    have te: "\<And>S f T. S \<noteq> {} \<Longrightarrow> \<forall>i\<in>S. f i \<union> i = T \<Longrightarrow> T = \<Inter>(f ` S) \<union> \<Union>S" by auto
    have cbox_eq: "cbox a b = \<Inter>((\<lambda>i. \<Union>(q i - {i})) ` p) \<union> \<Union>p"
    proof (rule te[OF False], clarify)
      fix i
      assume i: "i \<in> p"
      show "\<Union>(q i - {i}) \<union> i = cbox a b"
        using division_ofD(6)[OF q(1)[OF i]] using q(2)[OF i] by auto
    qed
    { fix K
      assume K: "K \<in> p"
      note qk=division_ofD[OF q(1)[OF K]]
      have *: "\<And>u T S. T \<inter> S = {} \<Longrightarrow> u \<subseteq> S \<Longrightarrow> u \<inter> T = {}"
        by auto
      have "interior (\<Inter>i\<in>p. \<Union>(q i - {i})) \<inter> interior K = {}"
      proof (rule *[OF Int_interior_Union_intervals])
        show "\<And>T. T\<in>q K - {K} \<Longrightarrow> interior K \<inter> interior T = {}"
          using qk(5) using q(2)[OF K] by auto
        show "interior (\<Inter>i\<in>p. \<Union>(q i - {i})) \<subseteq> interior (\<Union>(q K - {K}))"
          apply (rule interior_mono)+
          using K by auto
      qed (use qk in auto)} note [simp] = this
    show "d \<union> p division_of (cbox a b)"
      unfolding cbox_eq
      apply (rule division_disjoint_union[OF d assms(1)])
      apply (rule Int_interior_Union_intervals)
      apply (rule p open_interior ballI)+
      apply simp_all
      done
  qed
  then show ?thesis
    by (meson Un_upper2 that)
qed

lemma elementary_bounded[dest]:
  fixes S :: "'a::euclidean_space set"
  shows "p division_of S \<Longrightarrow> bounded S"
  unfolding division_of_def by (metis bounded_Union bounded_cbox)

lemma elementary_subset_cbox:
  "p division_of S \<Longrightarrow> \<exists>a b. S \<subseteq> cbox a (b::'a::euclidean_space)"
  by (meson bounded_subset_cbox_symmetric elementary_bounded)

proposition division_union_intervals_exists:
  fixes a b :: "'a::euclidean_space"
  assumes "cbox a b \<noteq> {}"
  obtains p where "(insert (cbox a b) p) division_of (cbox a b \<union> cbox c d)"
proof (cases "cbox c d = {}")
  case True
  with assms that show ?thesis by force
next
  case False
  show ?thesis
  proof (cases "cbox a b \<inter> cbox c d = {}")
    case True
    then show ?thesis
      by (metis that False assms division_disjoint_union division_of_self insert_is_Un interior_Int interior_empty)
  next
    case False
    obtain u v where uv: "cbox a b \<inter> cbox c d = cbox u v"
      unfolding Int_interval by auto
    have uv_sub: "cbox u v \<subseteq> cbox c d" using uv by auto
    obtain p where pd: "p division_of cbox c d" and "cbox u v \<in> p"
      by (rule partial_division_extend_1[OF uv_sub False[unfolded uv]])
    note p = this division_ofD[OF pd]
    have "interior (cbox a b \<inter> \<Union>(p - {cbox u v})) = interior(cbox u v \<inter> \<Union>(p - {cbox u v}))"
      apply (rule arg_cong[of _ _ interior])
      using p(8) uv by auto
    also have "\<dots> = {}"
      unfolding interior_Int
      apply (rule Int_interior_Union_intervals)
      using p(6) p(7)[OF p(2)] \<open>finite p\<close>
      apply auto
      done
    finally have [simp]: "interior (cbox a b) \<inter> interior (\<Union>(p - {cbox u v})) = {}" by simp
    have cbe: "cbox a b \<union> cbox c d = cbox a b \<union> \<Union>(p - {cbox u v})"
      using p(8) unfolding uv[symmetric] by auto
    have "insert (cbox a b) (p - {cbox u v}) division_of cbox a b \<union> \<Union>(p - {cbox u v})"
    proof -
      have "{cbox a b} division_of cbox a b"
        by (simp add: assms division_of_self)
      then show "insert (cbox a b) (p - {cbox u v}) division_of cbox a b \<union> \<Union>(p - {cbox u v})"
        by (metis (no_types) Diff_subset \<open>interior (cbox a b) \<inter> interior (\<Union>(p - {cbox u v})) = {}\<close> division_disjoint_union division_of_subset insert_is_Un p(1) p(8))
    qed
    with that[of "p - {cbox u v}"] show ?thesis by (simp add: cbe)
  qed
qed

lemma division_of_Union:
  assumes "finite f"
    and "\<And>p. p \<in> f \<Longrightarrow> p division_of (\<Union>p)"
    and "\<And>k1 k2. k1 \<in> \<Union>f \<Longrightarrow> k2 \<in> \<Union>f \<Longrightarrow> k1 \<noteq> k2 \<Longrightarrow> interior k1 \<inter> interior k2 = {}"
  shows "\<Union>f division_of \<Union>(\<Union>f)"
  using assms  by (auto intro!: division_ofI)

lemma elementary_union_interval:
  fixes a b :: "'a::euclidean_space"
  assumes "p division_of \<Union>p"
  obtains q where "q division_of (cbox a b \<union> \<Union>p)"
proof (cases "p = {} \<or> cbox a b = {}")
  case True
  obtain p where "p division_of (cbox a b)"
    by (rule elementary_interval)
  then show thesis
    using True assms that by auto
next
  case False
  then have "p \<noteq> {}" "cbox a b \<noteq> {}"
    by auto
  note pdiv = division_ofD[OF assms]
  show ?thesis
  proof (cases "interior (cbox a b) = {}")
    case True
    show ?thesis
      apply (rule that [of "insert (cbox a b) p", OF division_ofI])
      using pdiv(1-4) True False apply auto
       apply (metis IntI equals0D pdiv(5))
      by (metis disjoint_iff_not_equal pdiv(5))
  next
    case False  
    have "\<forall>K\<in>p. \<exists>q. (insert (cbox a b) q) division_of (cbox a b \<union> K)"
    proof
      fix K
      assume kp: "K \<in> p"
      from pdiv(4)[OF kp] obtain c d where "K = cbox c d" by blast
      then show "\<exists>q. (insert (cbox a b) q) division_of (cbox a b \<union> K)"
        by (meson \<open>cbox a b \<noteq> {}\<close> division_union_intervals_exists)
    qed
    from bchoice[OF this] obtain q where "\<forall>x\<in>p. insert (cbox a b) (q x) division_of (cbox a b) \<union> x" ..
    note q = division_ofD[OF this[rule_format]]
    let ?D = "\<Union>{insert (cbox a b) (q K) | K. K \<in> p}"
    show thesis
    proof (rule that[OF division_ofI])
      have *: "{insert (cbox a b) (q K) |K. K \<in> p} = (\<lambda>K. insert (cbox a b) (q K)) ` p"
        by auto
      show "finite ?D"
        using "*" pdiv(1) q(1) by auto
      have "\<Union>?D = (\<Union>x\<in>p. \<Union>(insert (cbox a b) (q x)))"
        by auto
      also have "... = \<Union>{cbox a b \<union> t |t. t \<in> p}"
        using q(6) by auto
      also have "... = cbox a b \<union> \<Union>p"
        using \<open>p \<noteq> {}\<close> by auto
      finally show "\<Union>?D = cbox a b \<union> \<Union>p" .
      show "K \<subseteq> cbox a b \<union> \<Union>p" "K \<noteq> {}" if "K \<in> ?D" for K
        using q that by blast+
      show "\<exists>a b. K = cbox a b" if "K \<in> ?D" for K
        using q(4) that by auto
    next
      fix K' K
      assume K: "K \<in> ?D" and K': "K' \<in> ?D" "K \<noteq> K'"
      obtain x where x: "K \<in> insert (cbox a b) (q x)" "x\<in>p"
        using K by auto
      obtain x' where x': "K'\<in>insert (cbox a b) (q x')" "x'\<in>p"
        using K' by auto
      show "interior K \<inter> interior K' = {}"
      proof (cases "x = x' \<or> K  = cbox a b \<or> K' = cbox a b")
        case True
        then show ?thesis
          using True K' q(5) x' x by auto
      next
        case False
        then have as': "K \<noteq> cbox a b" "K' \<noteq> cbox a b"
          by auto
        obtain c d where K: "K = cbox c d"
          using q(4) x by blast
        have "interior K \<inter> interior (cbox a b) = {}"
          using as' K'(2) q(5) x by blast
        then have "interior K \<subseteq> interior x"
          by (metis \<open>interior (cbox a b) \<noteq> {}\<close> K q(2) x interior_subset_union_intervals)
        moreover
        obtain c d where c_d: "K' = cbox c d"
          using q(4)[OF x'(2,1)] by blast
        have "interior K' \<inter> interior (cbox a b) = {}"
          using as'(2) q(5) x' by blast
        then have "interior K' \<subseteq> interior x'"
          by (metis \<open>interior (cbox a b) \<noteq> {}\<close> c_d interior_subset_union_intervals q(2) x'(1) x'(2))
        moreover have "interior x \<inter> interior x' = {}"
          by (meson False assms division_ofD(5) x'(2) x(2))
        ultimately show ?thesis
          using \<open>interior K \<subseteq> interior x\<close> \<open>interior K' \<subseteq> interior x'\<close> by auto
      qed
    qed
  qed
qed



lemma elementary_unions_intervals:
  assumes fin: "finite f"
    and "\<And>s. s \<in> f \<Longrightarrow> \<exists>a b. s = cbox a (b::'a::euclidean_space)"
  obtains p where "p division_of (\<Union>f)"
proof -
  have "\<exists>p. p division_of (\<Union>f)"
  proof (induct_tac f rule:finite_subset_induct)
    show "\<exists>p. p division_of \<Union>{}" using elementary_empty by auto
  next
    fix x F
    assume as: "finite F" "x \<notin> F" "\<exists>p. p division_of \<Union>F" "x\<in>f"
    from this(3) obtain p where p: "p division_of \<Union>F" ..
    from assms(2)[OF as(4)] obtain a b where x: "x = cbox a b" by blast
    have *: "\<Union>F = \<Union>p"
      using division_ofD[OF p] by auto
    show "\<exists>p. p division_of \<Union>(insert x F)"
      using elementary_union_interval[OF p[unfolded *], of a b]
      unfolding Union_insert x * by metis
  qed (insert assms, auto)
  then show ?thesis
    using that by auto
qed

lemma elementary_union:
  fixes S T :: "'a::euclidean_space set"
  assumes "ps division_of S" "pt division_of T"
  obtains p where "p division_of (S \<union> T)"
proof -
  have *: "S \<union> T = \<Union>ps \<union> \<Union>pt"
    using assms unfolding division_of_def by auto
  show ?thesis
    apply (rule elementary_unions_intervals[of "ps \<union> pt"])
    using assms apply auto
    by (simp add: * that)
qed

lemma partial_division_extend:
  fixes T :: "'a::euclidean_space set"
  assumes "p division_of S"
    and "q division_of T"
    and "S \<subseteq> T"
  obtains r where "p \<subseteq> r" and "r division_of T"
proof -
  note divp = division_ofD[OF assms(1)] and divq = division_ofD[OF assms(2)]
  obtain a b where ab: "T \<subseteq> cbox a b"
    using elementary_subset_cbox[OF assms(2)] by auto
  obtain r1 where "p \<subseteq> r1" "r1 division_of (cbox a b)"
    using assms
    by (metis ab dual_order.trans partial_division_extend_interval divp(6))
  note r1 = this division_ofD[OF this(2)]
  obtain p' where "p' division_of \<Union>(r1 - p)"
    apply (rule elementary_unions_intervals[of "r1 - p"])
    using r1(3,6)
      apply auto
    done
  then obtain r2 where r2: "r2 division_of (\<Union>(r1 - p)) \<inter> (\<Union>q)"
    by (metis assms(2) divq(6) elementary_Int)
  {
    fix x
    assume x: "x \<in> T" "x \<notin> S"
    then obtain R where r: "R \<in> r1" "x \<in> R"
      unfolding r1 using ab
      by (meson division_contains r1(2) subsetCE)
    moreover have "R \<notin> p"
    proof
      assume "R \<in> p"
      then have "x \<in> S" using divp(2) r by auto
      then show False using x by auto
    qed
    ultimately have "x\<in>\<Union>(r1 - p)" by auto
  }
  then have Teq: "T = \<Union>p \<union> (\<Union>(r1 - p) \<inter> \<Union>q)"
    unfolding divp divq using assms(3) by auto
  have "interior S \<inter> interior (\<Union>(r1-p)) = {}"
  proof (rule Int_interior_Union_intervals)
    have *: "\<And>S. (\<And>x. x \<in> S \<Longrightarrow> False) \<Longrightarrow> S = {}"
      by auto
    show "interior S \<inter> interior m = {}" if "m \<in> r1 - p" for m 
    proof -
      have "interior m \<inter> interior (\<Union>p) = {}"
      proof (rule Int_interior_Union_intervals)
        show "\<And>T. T\<in>p \<Longrightarrow> interior m \<inter> interior T = {}"
          by (metis DiffD1 DiffD2 that r1(1) r1(7) rev_subsetD)
      qed (use divp in auto)
      then show "interior S \<inter> interior m = {}"
        unfolding divp by auto
    qed 
  qed (use r1 in auto)
  then have "interior S \<inter> interior (\<Union>(r1-p) \<inter> (\<Union>q)) = {}"
    using interior_subset by auto
  then have div: "p \<union> r2 division_of \<Union>p \<union> \<Union>(r1 - p) \<inter> \<Union>q"
    by (simp add: assms(1) division_disjoint_union divp(6) r2)
  show ?thesis
    apply (rule that[of "p \<union> r2"])
     apply (auto simp: div Teq)
    done
qed


lemma division_split:
  fixes a :: "'a::euclidean_space"
  assumes "p division_of (cbox a b)"
    and k: "k\<in>Basis"
  shows "{l \<inter> {x. x\<bullet>k \<le> c} | l. l \<in> p \<and> l \<inter> {x. x\<bullet>k \<le> c} \<noteq> {}} division_of(cbox a b \<inter> {x. x\<bullet>k \<le> c})"
      (is "?p1 division_of ?I1")
    and "{l \<inter> {x. x\<bullet>k \<ge> c} | l. l \<in> p \<and> l \<inter> {x. x\<bullet>k \<ge> c} \<noteq> {}} division_of (cbox a b \<inter> {x. x\<bullet>k \<ge> c})"
      (is "?p2 division_of ?I2")
proof (rule_tac[!] division_ofI)
  note p = division_ofD[OF assms(1)]
  show "finite ?p1" "finite ?p2"
    using p(1) by auto
  show "\<Union>?p1 = ?I1" "\<Union>?p2 = ?I2"
    unfolding p(6)[symmetric] by auto
  {
    fix K
    assume "K \<in> ?p1"
    then obtain l where l: "K = l \<inter> {x. x \<bullet> k \<le> c}" "l \<in> p" "l \<inter> {x. x \<bullet> k \<le> c} \<noteq> {}"
      by blast
    obtain u v where uv: "l = cbox u v"
      using assms(1) l(2) by blast
    show "K \<subseteq> ?I1"
      using l p(2) uv by force
    show  "K \<noteq> {}"
      by (simp add: l)
    show  "\<exists>a b. K = cbox a b"
      apply (simp add: l uv p(2-3)[OF l(2)])
      apply (subst interval_split[OF k])
      apply (auto intro: order.trans)
      done
    fix K'
    assume "K' \<in> ?p1"
    then obtain l' where l': "K' = l' \<inter> {x. x \<bullet> k \<le> c}" "l' \<in> p" "l' \<inter> {x. x \<bullet> k \<le> c} \<noteq> {}"
      by blast
    assume "K \<noteq> K'"
    then show "interior K \<inter> interior K' = {}"
      unfolding l l' using p(5)[OF l(2) l'(2)] by auto
  }
  {
    fix K
    assume "K \<in> ?p2"
    then obtain l where l: "K = l \<inter> {x. c \<le> x \<bullet> k}" "l \<in> p" "l \<inter> {x. c \<le> x \<bullet> k} \<noteq> {}"
      by blast
    obtain u v where uv: "l = cbox u v"
      using l(2) p(4) by blast
    show "K \<subseteq> ?I2"
      using l p(2) uv by force
    show  "K \<noteq> {}"
      by (simp add: l)
    show  "\<exists>a b. K = cbox a b"
      apply (simp add: l uv p(2-3)[OF l(2)])
      apply (subst interval_split[OF k])
      apply (auto intro: order.trans)
      done
    fix K'
    assume "K' \<in> ?p2"
    then obtain l' where l': "K' = l' \<inter> {x. c \<le> x \<bullet> k}" "l' \<in> p" "l' \<inter> {x. c \<le> x \<bullet> k} \<noteq> {}"
      by blast
    assume "K \<noteq> K'"
    then show "interior K \<inter> interior K' = {}"
      unfolding l l' using p(5)[OF l(2) l'(2)] by auto
  }
qed

subsection \<open>Tagged (partial) divisions\<close>

definition\<^marker>\<open>tag important\<close> tagged_partial_division_of (infixr "tagged'_partial'_division'_of" 40)
  where "s tagged_partial_division_of i \<longleftrightarrow>
    finite s \<and>
    (\<forall>x K. (x, K) \<in> s \<longrightarrow> x \<in> K \<and> K \<subseteq> i \<and> (\<exists>a b. K = cbox a b)) \<and>
    (\<forall>x1 K1 x2 K2. (x1, K1) \<in> s \<and> (x2, K2) \<in> s \<and> (x1, K1) \<noteq> (x2, K2) \<longrightarrow>
      interior K1 \<inter> interior K2 = {})"

lemma tagged_partial_division_ofD:
  assumes "s tagged_partial_division_of i"
  shows "finite s"
    and "\<And>x K. (x,K) \<in> s \<Longrightarrow> x \<in> K"
    and "\<And>x K. (x,K) \<in> s \<Longrightarrow> K \<subseteq> i"
    and "\<And>x K. (x,K) \<in> s \<Longrightarrow> \<exists>a b. K = cbox a b"
    and "\<And>x1 K1 x2 K2. (x1,K1) \<in> s \<Longrightarrow>
      (x2, K2) \<in> s \<Longrightarrow> (x1, K1) \<noteq> (x2, K2) \<Longrightarrow> interior K1 \<inter> interior K2 = {}"
  using assms unfolding tagged_partial_division_of_def by blast+

definition\<^marker>\<open>tag important\<close> tagged_division_of (infixr "tagged'_division'_of" 40)
  where "s tagged_division_of i \<longleftrightarrow> s tagged_partial_division_of i \<and> (\<Union>{K. \<exists>x. (x,K) \<in> s} = i)"

lemma tagged_division_of_finite: "s tagged_division_of i \<Longrightarrow> finite s"
  unfolding tagged_division_of_def tagged_partial_division_of_def by auto

lemma tagged_division_of:
  "s tagged_division_of i \<longleftrightarrow>
    finite s \<and>
    (\<forall>x K. (x, K) \<in> s \<longrightarrow> x \<in> K \<and> K \<subseteq> i \<and> (\<exists>a b. K = cbox a b)) \<and>
    (\<forall>x1 K1 x2 K2. (x1, K1) \<in> s \<and> (x2, K2) \<in> s \<and> (x1, K1) \<noteq> (x2, K2) \<longrightarrow>
      interior K1 \<inter> interior K2 = {}) \<and>
    (\<Union>{K. \<exists>x. (x,K) \<in> s} = i)"
  unfolding tagged_division_of_def tagged_partial_division_of_def by auto

lemma tagged_division_ofI:
  assumes "finite s"
    and "\<And>x K. (x,K) \<in> s \<Longrightarrow> x \<in> K"
    and "\<And>x K. (x,K) \<in> s \<Longrightarrow> K \<subseteq> i"
    and "\<And>x K. (x,K) \<in> s \<Longrightarrow> \<exists>a b. K = cbox a b"
    and "\<And>x1 K1 x2 K2. (x1,K1) \<in> s \<Longrightarrow> (x2, K2) \<in> s \<Longrightarrow> (x1, K1) \<noteq> (x2, K2) \<Longrightarrow>
      interior K1 \<inter> interior K2 = {}"
    and "(\<Union>{K. \<exists>x. (x,K) \<in> s} = i)"
  shows "s tagged_division_of i"
  unfolding tagged_division_of
  using assms  by fastforce

lemma tagged_division_ofD[dest]:  (*FIXME USE A LOCALE*)
  assumes "s tagged_division_of i"
  shows "finite s"
    and "\<And>x K. (x,K) \<in> s \<Longrightarrow> x \<in> K"
    and "\<And>x K. (x,K) \<in> s \<Longrightarrow> K \<subseteq> i"
    and "\<And>x K. (x,K) \<in> s \<Longrightarrow> \<exists>a b. K = cbox a b"
    and "\<And>x1 K1 x2 K2. (x1, K1) \<in> s \<Longrightarrow> (x2, K2) \<in> s \<Longrightarrow> (x1, K1) \<noteq> (x2, K2) \<Longrightarrow>
      interior K1 \<inter> interior K2 = {}"
    and "(\<Union>{K. \<exists>x. (x,K) \<in> s} = i)"
  using assms unfolding tagged_division_of by blast+

lemma division_of_tagged_division:
  assumes "s tagged_division_of i"
  shows "(snd ` s) division_of i"
proof (rule division_ofI)
  note assm = tagged_division_ofD[OF assms]
  show "\<Union>(snd ` s) = i" "finite (snd ` s)"
    using assm by auto
  fix k
  assume k: "k \<in> snd ` s"
  then obtain xk where xk: "(xk, k) \<in> s"
    by auto
  then show "k \<subseteq> i" "k \<noteq> {}" "\<exists>a b. k = cbox a b"
    using assm by fastforce+
  fix k'
  assume k': "k' \<in> snd ` s" "k \<noteq> k'"
  from this(1) obtain xk' where xk': "(xk', k') \<in> s"
    by auto
  then show "interior k \<inter> interior k' = {}"
    using assm(5) k'(2) xk by blast
qed

lemma partial_division_of_tagged_division:
  assumes "s tagged_partial_division_of i"
  shows "(snd ` s) division_of \<Union>(snd ` s)"
proof (rule division_ofI)
  note assm = tagged_partial_division_ofD[OF assms]
  show "finite (snd ` s)" "\<Union>(snd ` s) = \<Union>(snd ` s)"
    using assm by auto
  fix k
  assume k: "k \<in> snd ` s"
  then obtain xk where xk: "(xk, k) \<in> s"
    by auto
  then show "k \<noteq> {}" "\<exists>a b. k = cbox a b" "k \<subseteq> \<Union>(snd ` s)"
    using assm by auto
  fix k'
  assume k': "k' \<in> snd ` s" "k \<noteq> k'"
  from this(1) obtain xk' where xk': "(xk', k') \<in> s"
    by auto
  then show "interior k \<inter> interior k' = {}"
    using assm(5) k'(2) xk by auto
qed

lemma tagged_partial_division_subset:
  assumes "s tagged_partial_division_of i"
    and "t \<subseteq> s"
  shows "t tagged_partial_division_of i"
  using assms finite_subset[OF assms(2)]
  unfolding tagged_partial_division_of_def
  by blast

lemma tag_in_interval: "p tagged_division_of i \<Longrightarrow> (x, k) \<in> p \<Longrightarrow> x \<in> i"
  by auto

lemma tagged_division_of_empty: "{} tagged_division_of {}"
  unfolding tagged_division_of by auto

lemma tagged_partial_division_of_trivial[simp]: "p tagged_partial_division_of {} \<longleftrightarrow> p = {}"
  unfolding tagged_partial_division_of_def by auto

lemma tagged_division_of_trivial[simp]: "p tagged_division_of {} \<longleftrightarrow> p = {}"
  unfolding tagged_division_of by auto

lemma tagged_division_of_self: "x \<in> cbox a b \<Longrightarrow> {(x,cbox a b)} tagged_division_of (cbox a b)"
  by (rule tagged_division_ofI) auto

lemma tagged_division_of_self_real: "x \<in> {a .. b::real} \<Longrightarrow> {(x,{a .. b})} tagged_division_of {a .. b}"
  unfolding box_real[symmetric]
  by (rule tagged_division_of_self)

lemma tagged_division_Un:
  assumes "p1 tagged_division_of s1"
    and "p2 tagged_division_of s2"
    and "interior s1 \<inter> interior s2 = {}"
  shows "(p1 \<union> p2) tagged_division_of (s1 \<union> s2)"
proof (rule tagged_division_ofI)
  note p1 = tagged_division_ofD[OF assms(1)]
  note p2 = tagged_division_ofD[OF assms(2)]
  show "finite (p1 \<union> p2)"
    using p1(1) p2(1) by auto
  show "\<Union>{k. \<exists>x. (x, k) \<in> p1 \<union> p2} = s1 \<union> s2"
    using p1(6) p2(6) by blast
  fix x k
  assume xk: "(x, k) \<in> p1 \<union> p2"
  show "x \<in> k" "\<exists>a b. k = cbox a b"
    using xk p1(2,4) p2(2,4) by auto
  show "k \<subseteq> s1 \<union> s2"
    using xk p1(3) p2(3) by blast
  fix x' k'
  assume xk': "(x', k') \<in> p1 \<union> p2" "(x, k) \<noteq> (x', k')"
  have *: "\<And>a b. a \<subseteq> s1 \<Longrightarrow> b \<subseteq> s2 \<Longrightarrow> interior a \<inter> interior b = {}"
    using assms(3) interior_mono by blast
  show "interior k \<inter> interior k' = {}"
    apply (cases "(x, k) \<in> p1")
    apply (meson "*" UnE assms(1) assms(2) p1(5) tagged_division_ofD(3) xk'(1) xk'(2))
    by (metis "*" UnE assms(1) assms(2) inf_sup_aci(1) p2(5) tagged_division_ofD(3) xk xk'(1) xk'(2))
qed

lemma tagged_division_Union:
  assumes "finite I"
    and tag: "\<And>i. i\<in>I \<Longrightarrow> pfn i tagged_division_of i"
    and disj: "\<And>i1 i2. \<lbrakk>i1 \<in> I; i2 \<in> I; i1 \<noteq> i2\<rbrakk> \<Longrightarrow> interior(i1) \<inter> interior(i2) = {}"
  shows "\<Union>(pfn ` I) tagged_division_of (\<Union>I)"
proof (rule tagged_division_ofI)
  note assm = tagged_division_ofD[OF tag]
  show "finite (\<Union>(pfn ` I))"
    using assms by auto
  have "\<Union>{k. \<exists>x. (x, k) \<in> \<Union>(pfn ` I)} = \<Union>((\<lambda>i. \<Union>{k. \<exists>x. (x, k) \<in> pfn i}) ` I)"
    by blast
  also have "\<dots> = \<Union>I"
    using assm(6) by auto
  finally show "\<Union>{k. \<exists>x. (x, k) \<in> \<Union>(pfn ` I)} = \<Union>I" .
  fix x k
  assume xk: "(x, k) \<in> \<Union>(pfn ` I)"
  then obtain i where i: "i \<in> I" "(x, k) \<in> pfn i"
    by auto
  show "x \<in> k" "\<exists>a b. k = cbox a b" "k \<subseteq> \<Union>I"
    using assm(2-4)[OF i] using i(1) by auto
  fix x' k'
  assume xk': "(x', k') \<in> \<Union>(pfn ` I)" "(x, k) \<noteq> (x', k')"
  then obtain i' where i': "i' \<in> I" "(x', k') \<in> pfn i'"
    by auto
  have *: "\<And>a b. i \<noteq> i' \<Longrightarrow> a \<subseteq> i \<Longrightarrow> b \<subseteq> i' \<Longrightarrow> interior a \<inter> interior b = {}"
    using i(1) i'(1) disj interior_mono by blast
  show "interior k \<inter> interior k' = {}"
  proof (cases "i = i'")
    case True then show ?thesis 
      using assm(5) i' i xk'(2) by blast
  next
    case False then show ?thesis 
    using "*" assm(3) i' i by auto
  qed
qed

lemma tagged_partial_division_of_Union_self:
  assumes "p tagged_partial_division_of s"
  shows "p tagged_division_of (\<Union>(snd ` p))"
  apply (rule tagged_division_ofI)
  using tagged_partial_division_ofD[OF assms]
  apply auto
  done

lemma tagged_division_of_union_self:
  assumes "p tagged_division_of s"
  shows "p tagged_division_of (\<Union>(snd ` p))"
  apply (rule tagged_division_ofI)
  using tagged_division_ofD[OF assms]
  apply auto
  done

lemma tagged_division_Un_interval:
  fixes a :: "'a::euclidean_space"
  assumes "p1 tagged_division_of (cbox a b \<inter> {x. x\<bullet>k \<le> (c::real)})"
    and "p2 tagged_division_of (cbox a b \<inter> {x. x\<bullet>k \<ge> c})"
    and k: "k \<in> Basis"
  shows "(p1 \<union> p2) tagged_division_of (cbox a b)"
proof -
  have *: "cbox a b = (cbox a b \<inter> {x. x\<bullet>k \<le> c}) \<union> (cbox a b \<inter> {x. x\<bullet>k \<ge> c})"
    by auto
  show ?thesis
    apply (subst *)
    apply (rule tagged_division_Un[OF assms(1-2)])
    unfolding interval_split[OF k] interior_cbox
    using k
    apply (auto simp add: box_def elim!: ballE[where x=k])
    done
qed

lemma tagged_division_Un_interval_real:
  fixes a :: real
  assumes "p1 tagged_division_of ({a .. b} \<inter> {x. x\<bullet>k \<le> (c::real)})"
    and "p2 tagged_division_of ({a .. b} \<inter> {x. x\<bullet>k \<ge> c})"
    and k: "k \<in> Basis"
  shows "(p1 \<union> p2) tagged_division_of {a .. b}"
  using assms
  unfolding box_real[symmetric]
  by (rule tagged_division_Un_interval)

lemma tagged_division_split_left_inj:
  assumes d: "d tagged_division_of i"
  and tags: "(x1, K1) \<in> d" "(x2, K2) \<in> d"
  and "K1 \<noteq> K2"
  and eq: "K1 \<inter> {x. x \<bullet> k \<le> c} = K2 \<inter> {x. x \<bullet> k \<le> c}"
    shows "interior (K1 \<inter> {x. x\<bullet>k \<le> c}) = {}"
proof -
  have "interior (K1 \<inter> K2) = {} \<or> (x2, K2) = (x1, K1)"
    using tags d by (metis (no_types) interior_Int tagged_division_ofD(5))
  then show ?thesis
    using eq \<open>K1 \<noteq> K2\<close> by (metis (no_types) inf_assoc inf_bot_left inf_left_idem interior_Int old.prod.inject)
qed

lemma tagged_division_split_right_inj:
  assumes d: "d tagged_division_of i"
  and tags: "(x1, K1) \<in> d" "(x2, K2) \<in> d"
  and "K1 \<noteq> K2"
  and eq: "K1 \<inter> {x. x\<bullet>k \<ge> c} = K2 \<inter> {x. x\<bullet>k \<ge> c}"
    shows "interior (K1 \<inter> {x. x\<bullet>k \<ge> c}) = {}"
proof -
  have "interior (K1 \<inter> K2) = {} \<or> (x2, K2) = (x1, K1)"
    using tags d by (metis (no_types) interior_Int tagged_division_ofD(5))
  then show ?thesis
    using eq \<open>K1 \<noteq> K2\<close> by (metis (no_types) inf_assoc inf_bot_left inf_left_idem interior_Int old.prod.inject)
qed

lemma (in comm_monoid_set) over_tagged_division_lemma:
  assumes "p tagged_division_of i"
    and "\<And>u v. box u v = {} \<Longrightarrow> d (cbox u v) = \<^bold>1"
  shows "F (\<lambda>(_, k). d k) p = F d (snd ` p)"
proof -
  have *: "(\<lambda>(_ ,k). d k) = d \<circ> snd"
    by (simp add: fun_eq_iff)
  note assm = tagged_division_ofD[OF assms(1)]
  show ?thesis
    unfolding *
  proof (rule reindex_nontrivial[symmetric])
    show "finite p"
      using assm by auto
    fix x y
    assume "x\<in>p" "y\<in>p" "x\<noteq>y" "snd x = snd y"
    obtain a b where ab: "snd x = cbox a b"
      using assm(4)[of "fst x" "snd x"] \<open>x\<in>p\<close> by auto
    have "(fst x, snd y) \<in> p" "(fst x, snd y) \<noteq> y"
      using \<open>x \<in> p\<close> \<open>x \<noteq> y\<close> \<open>snd x = snd y\<close> [symmetric] by auto
    with \<open>x\<in>p\<close> \<open>y\<in>p\<close> have "interior (snd x) \<inter> interior (snd y) = {}"
      by (intro assm(5)[of "fst x" _ "fst y"]) auto
    then have "box a b = {}"
      unfolding \<open>snd x = snd y\<close>[symmetric] ab by auto
    then have "d (cbox a b) = \<^bold>1"
      using assm(2)[of "fst x" "snd x"] \<open>x\<in>p\<close> ab[symmetric] by (intro assms(2)) auto
    then show "d (snd x) = \<^bold>1"
      unfolding ab by auto
  qed
qed


subsection \<open>Functions closed on boxes: morphisms from boxes to monoids\<close>

text \<open>This auxiliary structure is used to sum up over the elements of a division. Main theorem is
  \<open>operative_division\<close>. Instances for the monoid are \<^typ>\<open>'a option\<close>, \<^typ>\<open>real\<close>, and
  \<^typ>\<open>bool\<close>.\<close>

paragraph\<^marker>\<open>tag important\<close> \<open>Using additivity of lifted function to encode definedness.\<close>
text \<open>%whitespace\<close>
definition\<^marker>\<open>tag important\<close> lift_option :: "('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> 'a option \<Rightarrow> 'b option \<Rightarrow> 'c option"
where
  "lift_option f a' b' = Option.bind a' (\<lambda>a. Option.bind b' (\<lambda>b. Some (f a b)))"

lemma lift_option_simps[simp]:
  "lift_option f (Some a) (Some b) = Some (f a b)"
  "lift_option f None b' = None"
  "lift_option f a' None = None"
  by (auto simp: lift_option_def)

lemma\<^marker>\<open>tag important\<close> comm_monoid_lift_option:
  assumes "comm_monoid f z"
  shows "comm_monoid (lift_option f) (Some z)"
proof -
  from assms interpret comm_monoid f z .
  show ?thesis
    by standard (auto simp: lift_option_def ac_simps split: bind_split)
qed

lemma comm_monoid_and: "comm_monoid HOL.conj True"
  by standard auto

lemma comm_monoid_set_and: "comm_monoid_set HOL.conj True"
  by (rule comm_monoid_set.intro) (fact comm_monoid_and)


paragraph \<open>Misc\<close>

lemma interval_real_split:
  "{a .. b::real} \<inter> {x. x \<le> c} = {a .. min b c}"
  "{a .. b} \<inter> {x. c \<le> x} = {max a c .. b}"
  apply (metis Int_atLeastAtMostL1 atMost_def)
  apply (metis Int_atLeastAtMostL2 atLeast_def)
  done

lemma bgauge_existence_lemma: "(\<forall>x\<in>s. \<exists>d::real. 0 < d \<and> q d x) \<longleftrightarrow> (\<forall>x. \<exists>d>0. x\<in>s \<longrightarrow> q d x)"
  by (meson zero_less_one)


paragraph \<open>Division points\<close>
text \<open>%whitespace\<close>
definition\<^marker>\<open>tag important\<close> "division_points (k::('a::euclidean_space) set) d =
   {(j,x). j \<in> Basis \<and> (interval_lowerbound k)\<bullet>j < x \<and> x < (interval_upperbound k)\<bullet>j \<and>
     (\<exists>i\<in>d. (interval_lowerbound i)\<bullet>j = x \<or> (interval_upperbound i)\<bullet>j = x)}"

lemma division_points_finite:
  fixes i :: "'a::euclidean_space set"
  assumes "d division_of i"
  shows "finite (division_points i d)"
proof -
  note assm = division_ofD[OF assms]
  let ?M = "\<lambda>j. {(j,x)|x. (interval_lowerbound i)\<bullet>j < x \<and> x < (interval_upperbound i)\<bullet>j \<and>
    (\<exists>i\<in>d. (interval_lowerbound i)\<bullet>j = x \<or> (interval_upperbound i)\<bullet>j = x)}"
  have *: "division_points i d = \<Union>(?M ` Basis)"
    unfolding division_points_def by auto
  show ?thesis
    unfolding * using assm by auto
qed

lemma division_points_subset:
  fixes a :: "'a::euclidean_space"
  assumes "d division_of (cbox a b)"
    and "\<forall>i\<in>Basis. a\<bullet>i < b\<bullet>i"  "a\<bullet>k < c" "c < b\<bullet>k"
    and k: "k \<in> Basis"
  shows "division_points (cbox a b \<inter> {x. x\<bullet>k \<le> c}) {l \<inter> {x. x\<bullet>k \<le> c} | l . l \<in> d \<and> l \<inter> {x. x\<bullet>k \<le> c} \<noteq> {}} \<subseteq>
      division_points (cbox a b) d" (is ?t1)
    and "division_points (cbox a b \<inter> {x. x\<bullet>k \<ge> c}) {l \<inter> {x. x\<bullet>k \<ge> c} | l . l \<in> d \<and> \<not>(l \<inter> {x. x\<bullet>k \<ge> c} = {})} \<subseteq>
      division_points (cbox a b) d" (is ?t2)
proof -
  note assm = division_ofD[OF assms(1)]
  have *: "\<forall>i\<in>Basis. a\<bullet>i \<le> b\<bullet>i"
    "\<forall>i\<in>Basis. a\<bullet>i \<le> (\<Sum>i\<in>Basis. (if i = k then min (b \<bullet> k) c else  b \<bullet> i) *\<^sub>R i) \<bullet> i"
    "\<forall>i\<in>Basis. (\<Sum>i\<in>Basis. (if i = k then max (a \<bullet> k) c else a \<bullet> i) *\<^sub>R i) \<bullet> i \<le> b\<bullet>i"
    "min (b \<bullet> k) c = c" "max (a \<bullet> k) c = c"
    using assms using less_imp_le by auto
   have "\<exists>i\<in>d. interval_lowerbound i \<bullet> x = y \<or> interval_upperbound i \<bullet> x = y"
     if "a \<bullet> x < y" "y < (if x = k then c else b \<bullet> x)"
        "interval_lowerbound i \<bullet> x = y \<or> interval_upperbound i \<bullet> x = y"
        "i = l \<inter> {x. x \<bullet> k \<le> c}" "l \<in> d" "l \<inter> {x. x \<bullet> k \<le> c} \<noteq> {}"
        "x \<in> Basis" for i l x y
  proof -
    obtain u v where l: "l = cbox u v"
      using \<open>l \<in> d\<close> assms(1) by blast
    have *: "\<forall>i\<in>Basis. u \<bullet> i \<le> (\<Sum>i\<in>Basis. (if i = k then min (v \<bullet> k) c else v \<bullet> i) *\<^sub>R i) \<bullet> i"
      using that(6) unfolding l interval_split[OF k] box_ne_empty that .
    have **: "\<forall>i\<in>Basis. u\<bullet>i \<le> v\<bullet>i"
      using l using that(6) unfolding box_ne_empty[symmetric] by auto
    show ?thesis
      apply (rule bexI[OF _ \<open>l \<in> d\<close>])
      using that(1-3,5) \<open>x \<in> Basis\<close>
      unfolding l interval_bounds[OF **] interval_bounds[OF *] interval_split[OF k] that
      apply (auto split: if_split_asm)
      done
  qed
  moreover have "\<And>x y. \<lbrakk>y < (if x = k then c else b \<bullet> x)\<rbrakk> \<Longrightarrow> y < b \<bullet> x"
    using \<open>c < b\<bullet>k\<close> by (auto split: if_split_asm)
  ultimately show ?t1 
    unfolding division_points_def interval_split[OF k, of a b]
    unfolding interval_bounds[OF *(1)] interval_bounds[OF *(2)] interval_bounds[OF *(3)]
    unfolding * by force
  have "\<And>x y i l. (if x = k then c else a \<bullet> x) < y \<Longrightarrow> a \<bullet> x < y"
    using \<open>a\<bullet>k < c\<close> by (auto split: if_split_asm)
  moreover have "\<exists>i\<in>d. interval_lowerbound i \<bullet> x = y \<or>
                       interval_upperbound i \<bullet> x = y"
    if "(if x = k then c else a \<bullet> x) < y" "y < b \<bullet> x"
      "interval_lowerbound i \<bullet> x = y \<or> interval_upperbound i \<bullet> x = y"
      "i = l \<inter> {x. c \<le> x \<bullet> k}" "l \<in> d" "l \<inter> {x. c \<le> x \<bullet> k} \<noteq> {}"
      "x \<in> Basis" for x y i l
  proof -
    obtain u v where l: "l = cbox u v"
      using \<open>l \<in> d\<close> assm(4) by blast
    have *: "\<forall>i\<in>Basis. (\<Sum>i\<in>Basis. (if i = k then max (u \<bullet> k) c else u \<bullet> i) *\<^sub>R i) \<bullet> i \<le> v \<bullet> i"
      using that(6) unfolding l interval_split[OF k] box_ne_empty that .
    have **: "\<forall>i\<in>Basis. u\<bullet>i \<le> v\<bullet>i"
      using l using that(6) unfolding box_ne_empty[symmetric] by auto
    show "\<exists>i\<in>d. interval_lowerbound i \<bullet> x = y \<or> interval_upperbound i \<bullet> x = y"
      apply (rule bexI[OF _ \<open>l \<in> d\<close>])
      using that(1-3,5) \<open>x \<in> Basis\<close>
      unfolding l interval_bounds[OF **] interval_bounds[OF *] interval_split[OF k] that
      apply (auto split: if_split_asm)
      done
  qed
  ultimately show ?t2
    unfolding division_points_def interval_split[OF k, of a b]
    unfolding interval_bounds[OF *(1)] interval_bounds[OF *(2)] interval_bounds[OF *(3)]
    unfolding *
    by force
qed

lemma division_points_psubset:
  fixes a :: "'a::euclidean_space"
  assumes d: "d division_of (cbox a b)"
      and altb: "\<forall>i\<in>Basis. a\<bullet>i < b\<bullet>i"  "a\<bullet>k < c" "c < b\<bullet>k"
      and "l \<in> d"
      and disj: "interval_lowerbound l\<bullet>k = c \<or> interval_upperbound l\<bullet>k = c"
      and k: "k \<in> Basis"
  shows "division_points (cbox a b \<inter> {x. x\<bullet>k \<le> c}) {l \<inter> {x. x\<bullet>k \<le> c} | l. l\<in>d \<and> l \<inter> {x. x\<bullet>k \<le> c} \<noteq> {}} \<subset>
         division_points (cbox a b) d" (is "?D1 \<subset> ?D")
    and "division_points (cbox a b \<inter> {x. x\<bullet>k \<ge> c}) {l \<inter> {x. x\<bullet>k \<ge> c} | l. l\<in>d \<and> l \<inter> {x. x\<bullet>k \<ge> c} \<noteq> {}} \<subset>
         division_points (cbox a b) d" (is "?D2 \<subset> ?D")
proof -
  have ab: "\<forall>i\<in>Basis. a\<bullet>i \<le> b\<bullet>i"
    using altb by (auto intro!:less_imp_le)
  obtain u v where l: "l = cbox u v"
    using d \<open>l \<in> d\<close> by blast
  have uv: "\<forall>i\<in>Basis. u\<bullet>i \<le> v\<bullet>i" "\<forall>i\<in>Basis. a\<bullet>i \<le> u\<bullet>i \<and> v\<bullet>i \<le> b\<bullet>i"
    apply (metis assms(5) box_ne_empty(1) cbox_division_memE d l)
    by (metis assms(5) box_ne_empty(1) cbox_division_memE d l subset_box(1))
  have *: "interval_upperbound (cbox a b \<inter> {x. x \<bullet> k \<le> interval_upperbound l \<bullet> k}) \<bullet> k = interval_upperbound l \<bullet> k"
          "interval_upperbound (cbox a b \<inter> {x. x \<bullet> k \<le> interval_lowerbound l \<bullet> k}) \<bullet> k = interval_lowerbound l \<bullet> k"
    unfolding l interval_split[OF k] interval_bounds[OF uv(1)]
    using uv[rule_format, of k] ab k
    by auto
  have "\<exists>x. x \<in> ?D - ?D1"
    using assms(3-)
    unfolding division_points_def interval_bounds[OF ab]
    by (force simp add: *)
  moreover have "?D1 \<subseteq> ?D"
    by (auto simp add: assms division_points_subset)
  ultimately show "?D1 \<subset> ?D"
    by blast
  have *: "interval_lowerbound (cbox a b \<inter> {x. x \<bullet> k \<ge> interval_lowerbound l \<bullet> k}) \<bullet> k = interval_lowerbound l \<bullet> k"
    "interval_lowerbound (cbox a b \<inter> {x. x \<bullet> k \<ge> interval_upperbound l \<bullet> k}) \<bullet> k = interval_upperbound l \<bullet> k"
    unfolding l interval_split[OF k] interval_bounds[OF uv(1)]
    using uv[rule_format, of k] ab k
    by auto
  have "\<exists>x. x \<in> ?D - ?D2"
    using assms(3-)
    unfolding division_points_def interval_bounds[OF ab]
    by (force simp add: *)
  moreover have "?D2 \<subseteq> ?D"
    by (auto simp add: assms division_points_subset)
  ultimately show "?D2 \<subset> ?D"
    by blast
qed

lemma division_split_left_inj:
  fixes S :: "'a::euclidean_space set"
  assumes div: "\<D> division_of S"
    and eq: "K1 \<inter> {x::'a. x\<bullet>k \<le> c} = K2 \<inter> {x. x\<bullet>k \<le> c}"
    and "K1 \<in> \<D>" "K2 \<in> \<D>" "K1 \<noteq> K2"
  shows "interior (K1 \<inter> {x. x\<bullet>k \<le> c}) = {}"
proof -
  have "interior K2 \<inter> interior {a. a \<bullet> k \<le> c} = interior K1 \<inter> interior {a. a \<bullet> k \<le> c}"
    by (metis (no_types) eq interior_Int)
  moreover have "\<And>A. interior A \<inter> interior K2 = {} \<or> A = K2 \<or> A \<notin> \<D>"
    by (meson div \<open>K2 \<in> \<D>\<close> division_of_def)
  ultimately show ?thesis
    using \<open>K1 \<in> \<D>\<close> \<open>K1 \<noteq> K2\<close> by auto
qed

lemma division_split_right_inj:
  fixes S :: "'a::euclidean_space set"
  assumes div: "\<D> division_of S"
    and eq: "K1 \<inter> {x::'a. x\<bullet>k \<ge> c} = K2 \<inter> {x. x\<bullet>k \<ge> c}"
    and "K1 \<in> \<D>" "K2 \<in> \<D>" "K1 \<noteq> K2"
  shows "interior (K1 \<inter> {x. x\<bullet>k \<ge> c}) = {}"
proof -
  have "interior K2 \<inter> interior {a. a \<bullet> k \<ge> c} = interior K1 \<inter> interior {a. a \<bullet> k \<ge> c}"
    by (metis (no_types) eq interior_Int)
  moreover have "\<And>A. interior A \<inter> interior K2 = {} \<or> A = K2 \<or> A \<notin> \<D>"
    by (meson div \<open>K2 \<in> \<D>\<close> division_of_def)
  ultimately show ?thesis
    using \<open>K1 \<in> \<D>\<close> \<open>K1 \<noteq> K2\<close> by auto
qed

lemma interval_doublesplit:
  fixes a :: "'a::euclidean_space"
  assumes "k \<in> Basis"
  shows "cbox a b \<inter> {x . \<bar>x\<bullet>k - c\<bar> \<le> (e::real)} =
    cbox (\<Sum>i\<in>Basis. (if i = k then max (a\<bullet>k) (c - e) else a\<bullet>i) *\<^sub>R i)
     (\<Sum>i\<in>Basis. (if i = k then min (b\<bullet>k) (c + e) else b\<bullet>i) *\<^sub>R i)"
proof -
  have *: "\<And>x c e::real. \<bar>x - c\<bar> \<le> e \<longleftrightarrow> x \<ge> c - e \<and> x \<le> c + e"
    by auto
  have **: "\<And>s P Q. s \<inter> {x. P x \<and> Q x} = (s \<inter> {x. Q x}) \<inter> {x. P x}"
    by blast
  show ?thesis
    unfolding * ** interval_split[OF assms] by (rule refl)
qed

lemma division_doublesplit:
  fixes a :: "'a::euclidean_space"
  assumes "p division_of (cbox a b)"
    and k: "k \<in> Basis"
  shows "(\<lambda>l. l \<inter> {x. \<bar>x\<bullet>k - c\<bar> \<le> e}) ` {l\<in>p. l \<inter> {x. \<bar>x\<bullet>k - c\<bar> \<le> e} \<noteq> {}}
         division_of  (cbox a b \<inter> {x. \<bar>x\<bullet>k - c\<bar> \<le> e})"
proof -
  have *: "\<And>x c. \<bar>x - c\<bar> \<le> e \<longleftrightarrow> x \<ge> c - e \<and> x \<le> c + e"
    by auto
  have **: "\<And>p q p' q'. p division_of q \<Longrightarrow> p = p' \<Longrightarrow> q = q' \<Longrightarrow> p' division_of q'"
    by auto
  note division_split(1)[OF assms, where c="c+e",unfolded interval_split[OF k]]
  note division_split(2)[OF this, where c="c-e" and k=k,OF k]
  then show ?thesis
    apply (rule **)
    subgoal
      apply (simp add: abs_diff_le_iff field_simps Collect_conj_eq setcompr_eq_image [symmetric] cong: image_cong_simp)
      apply (rule equalityI)
      apply blast
      apply clarsimp
      apply (rule_tac x="xa \<inter> {x. c + e \<ge> x \<bullet> k}" in exI)
      apply auto
      done
    by (simp add: interval_split k interval_doublesplit)
qed
              
paragraph \<open>Operative\<close>

locale operative = comm_monoid_set +
  fixes g :: "'b::euclidean_space set \<Rightarrow> 'a"
  assumes box_empty_imp: "\<And>a b. box a b = {} \<Longrightarrow> g (cbox a b) = \<^bold>1"
    and Basis_imp: "\<And>a b c k. k \<in> Basis \<Longrightarrow> g (cbox a b) = g (cbox a b \<inter> {x. x\<bullet>k \<le> c}) \<^bold>* g (cbox a b \<inter> {x. x\<bullet>k \<ge> c})"
begin

lemma empty [simp]:
  "g {} = \<^bold>1"
proof -
  have *: "cbox One (-One) = ({}::'b set)"
    by (auto simp: box_eq_empty inner_sum_left inner_Basis sum.If_cases ex_in_conv)
  moreover have "box One (-One) = ({}::'b set)"
    using box_subset_cbox[of One "-One"] by (auto simp: *)
  ultimately show ?thesis
    using box_empty_imp [of One "-One"] by simp
qed
       
lemma division:
  "F g d = g (cbox a b)" if "d division_of (cbox a b)"
proof -
  define C where [abs_def]: "C = card (division_points (cbox a b) d)"
  then show ?thesis
  using that proof (induction C arbitrary: a b d rule: less_induct)
    case (less a b d)
    show ?case
    proof cases
      assume "box a b = {}"
      { fix k assume "k\<in>d"
        then obtain a' b' where k: "k = cbox a' b'"
          using division_ofD(4)[OF less.prems] by blast
        with \<open>k\<in>d\<close> division_ofD(2)[OF less.prems] have "cbox a' b' \<subseteq> cbox a b"
          by auto
        then have "box a' b' \<subseteq> box a b"
          unfolding subset_box by auto
        then have "g k = \<^bold>1"
          using box_empty_imp [of a' b'] k by (simp add: \<open>box a b = {}\<close>) }
      then show "box a b = {} \<Longrightarrow> F g d = g (cbox a b)"
        by (auto intro!: neutral simp: box_empty_imp)
    next
      assume "box a b \<noteq> {}"
      then have ab: "\<forall>i\<in>Basis. a\<bullet>i < b\<bullet>i" and ab': "\<forall>i\<in>Basis. a\<bullet>i \<le> b\<bullet>i"
        by (auto simp: box_ne_empty)
      show "F g d = g (cbox a b)"
      proof (cases "division_points (cbox a b) d = {}")
        case True
        { fix u v and j :: 'b
          assume j: "j \<in> Basis" and as: "cbox u v \<in> d"
          then have "cbox u v \<noteq> {}"
            using less.prems by blast
          then have uv: "\<forall>i\<in>Basis. u\<bullet>i \<le> v\<bullet>i" "u\<bullet>j \<le> v\<bullet>j"
            using j unfolding box_ne_empty by auto
          have *: "\<And>p r Q. \<not> j\<in>Basis \<or> p \<or> r \<or> (\<forall>x\<in>d. Q x) \<Longrightarrow> p \<or> r \<or> Q (cbox u v)"
            using as j by auto
          have "(j, u\<bullet>j) \<notin> division_points (cbox a b) d"
               "(j, v\<bullet>j) \<notin> division_points (cbox a b) d" using True by auto
          note this[unfolded de_Morgan_conj division_points_def mem_Collect_eq split_conv interval_bounds[OF ab'] bex_simps]
          note *[OF this(1)] *[OF this(2)] note this[unfolded interval_bounds[OF uv(1)]]
          moreover
          have "a\<bullet>j \<le> u\<bullet>j" "v\<bullet>j \<le> b\<bullet>j"
            using division_ofD(2,2,3)[OF \<open>d division_of cbox a b\<close> as]
            apply (metis j subset_box(1) uv(1))
            by (metis \<open>cbox u v \<subseteq> cbox a b\<close> j subset_box(1) uv(1))
          ultimately have "u\<bullet>j = a\<bullet>j \<and> v\<bullet>j = a\<bullet>j \<or> u\<bullet>j = b\<bullet>j \<and> v\<bullet>j = b\<bullet>j \<or> u\<bullet>j = a\<bullet>j \<and> v\<bullet>j = b\<bullet>j"
            unfolding not_less de_Morgan_disj using ab[rule_format,of j] uv(2) j by force }
        then have d': "\<forall>i\<in>d. \<exists>u v. i = cbox u v \<and>
          (\<forall>j\<in>Basis. u\<bullet>j = a\<bullet>j \<and> v\<bullet>j = a\<bullet>j \<or> u\<bullet>j = b\<bullet>j \<and> v\<bullet>j = b\<bullet>j \<or> u\<bullet>j = a\<bullet>j \<and> v\<bullet>j = b\<bullet>j)"
          unfolding forall_in_division[OF less.prems] by blast
        have "(1/2) *\<^sub>R (a+b) \<in> cbox a b"
          unfolding mem_box using ab by (auto simp: inner_simps)
        note this[unfolded division_ofD(6)[OF \<open>d division_of cbox a b\<close>,symmetric] Union_iff]
        then obtain i where i: "i \<in> d" "(1 / 2) *\<^sub>R (a + b) \<in> i" ..
        obtain u v where uv: "i = cbox u v" 
                     "\<forall>j\<in>Basis. u \<bullet> j = a \<bullet> j \<and> v \<bullet> j = a \<bullet> j \<or>
                                u \<bullet> j = b \<bullet> j \<and> v \<bullet> j = b \<bullet> j \<or>
                                u \<bullet> j = a \<bullet> j \<and> v \<bullet> j = b \<bullet> j"
          using d' i(1) by auto
        have "cbox a b \<in> d"
        proof -
          have "u = a" "v = b"
            unfolding euclidean_eq_iff[where 'a='b]
          proof safe
            fix j :: 'b
            assume j: "j \<in> Basis"
            note i(2)[unfolded uv mem_box,rule_format,of j]
            then show "u \<bullet> j = a \<bullet> j" and "v \<bullet> j = b \<bullet> j"
              using uv(2)[rule_format,of j] j by (auto simp: inner_simps)
          qed
          then have "i = cbox a b" using uv by auto
          then show ?thesis using i by auto
        qed
        then have deq: "d = insert (cbox a b) (d - {cbox a b})"
          by auto
        have "F g (d - {cbox a b}) = \<^bold>1"
        proof (intro neutral ballI)
          fix x
          assume x: "x \<in> d - {cbox a b}"
          then have "x\<in>d"
            by auto note d'[rule_format,OF this]
          then obtain u v where uv: "x = cbox u v"
                      "\<forall>j\<in>Basis. u \<bullet> j = a \<bullet> j \<and> v \<bullet> j = a \<bullet> j \<or>
                                 u \<bullet> j = b \<bullet> j \<and> v \<bullet> j = b \<bullet> j \<or>
                                 u \<bullet> j = a \<bullet> j \<and> v \<bullet> j = b \<bullet> j" 
            by blast
          have "u \<noteq> a \<or> v \<noteq> b"
            using x[unfolded uv] by auto
          then obtain j where "u\<bullet>j \<noteq> a\<bullet>j \<or> v\<bullet>j \<noteq> b\<bullet>j" and j: "j \<in> Basis"
            unfolding euclidean_eq_iff[where 'a='b] by auto
          then have "u\<bullet>j = v\<bullet>j"
            using uv(2)[rule_format,OF j] by auto
          then have "box u v = {}"
            using j unfolding box_eq_empty by (auto intro!: bexI[of _ j])
          then show "g x = \<^bold>1"
            unfolding uv(1) by (rule box_empty_imp)
        qed
        then show "F g d = g (cbox a b)"
          using division_ofD[OF less.prems]
          apply (subst deq)
          apply (subst insert)
          apply auto
          done
      next
        case False
        then have "\<exists>x. x \<in> division_points (cbox a b) d"
          by auto
        then obtain k c 
          where "k \<in> Basis" "interval_lowerbound (cbox a b) \<bullet> k < c"
                "c < interval_upperbound (cbox a b) \<bullet> k"
                "\<exists>i\<in>d. interval_lowerbound i \<bullet> k = c \<or> interval_upperbound i \<bullet> k = c"
          unfolding division_points_def by auto
        then obtain j where "a \<bullet> k < c" "c < b \<bullet> k" 
              and "j \<in> d" and j: "interval_lowerbound j \<bullet> k = c \<or> interval_upperbound j \<bullet> k = c"
          by (metis division_of_trivial empty_iff interval_bounds' less.prems)
        let ?lec = "{x. x\<bullet>k \<le> c}" let ?gec = "{x. x\<bullet>k \<ge> c}"
        define d1 where "d1 = {l \<inter> ?lec | l. l \<in> d \<and> l \<inter> ?lec \<noteq> {}}"
        define d2 where "d2 = {l \<inter> ?gec | l. l \<in> d \<and> l \<inter> ?gec \<noteq> {}}"
        define cb where "cb = (\<Sum>i\<in>Basis. (if i = k then c else b\<bullet>i) *\<^sub>R i)"
        define ca where "ca = (\<Sum>i\<in>Basis. (if i = k then c else a\<bullet>i) *\<^sub>R i)"
        have "division_points (cbox a b \<inter> ?lec) {l \<inter> ?lec |l. l \<in> d \<and> l \<inter> ?lec \<noteq> {}} 
              \<subset> division_points (cbox a b) d"
          by (rule division_points_psubset[OF \<open>d division_of cbox a b\<close> ab \<open>a \<bullet> k < c\<close> \<open>c < b \<bullet> k\<close> \<open>j \<in> d\<close> j \<open>k \<in> Basis\<close>])
        with division_points_finite[OF \<open>d division_of cbox a b\<close>] 
        have "card
         (division_points (cbox a b \<inter> ?lec) {l \<inter> ?lec |l. l \<in> d \<and> l \<inter> ?lec \<noteq> {}})
           < card (division_points (cbox a b) d)"
          by (rule psubset_card_mono)
        moreover have "division_points (cbox a b \<inter> {x. c \<le> x \<bullet> k}) {l \<inter> {x. c \<le> x \<bullet> k} |l. l \<in> d \<and> l \<inter> {x. c \<le> x \<bullet> k} \<noteq> {}}
              \<subset> division_points (cbox a b) d"
          by (rule division_points_psubset[OF \<open>d division_of cbox a b\<close> ab \<open>a \<bullet> k < c\<close> \<open>c < b \<bullet> k\<close> \<open>j \<in> d\<close> j \<open>k \<in> Basis\<close>])
        with division_points_finite[OF \<open>d division_of cbox a b\<close>] 
        have "card (division_points (cbox a b \<inter> ?gec) {l \<inter> ?gec |l. l \<in> d \<and> l \<inter> ?gec \<noteq> {}})
              < card (division_points (cbox a b) d)"
          by (rule psubset_card_mono)
        ultimately have *: "F g d1 = g (cbox a b \<inter> ?lec)" "F g d2 = g (cbox a b \<inter> ?gec)"
          unfolding interval_split[OF \<open>k \<in> Basis\<close>]
          apply (rule_tac[!] less.hyps)
          using division_split[OF \<open>d division_of cbox a b\<close>, where k=k and c=c] \<open>k \<in> Basis\<close>
          by (simp_all add: interval_split  d1_def d2_def division_points_finite[OF \<open>d division_of cbox a b\<close>])
        have fxk_le: "g (l \<inter> ?lec) = \<^bold>1" 
          if "l \<in> d" "y \<in> d" "l \<inter> ?lec = y \<inter> ?lec" "l \<noteq> y" for l y
        proof -
          obtain u v where leq: "l = cbox u v"
            using \<open>l \<in> d\<close> less.prems by auto
          have "interior (cbox u v \<inter> ?lec) = {}"
            using that division_split_left_inj leq less.prems by blast
          then show ?thesis
            unfolding leq interval_split [OF \<open>k \<in> Basis\<close>]
            by (auto intro: box_empty_imp)
        qed
        have fxk_ge: "g (l \<inter> {x. x \<bullet> k \<ge> c}) = \<^bold>1"
          if "l \<in> d" "y \<in> d" "l \<inter> ?gec = y \<inter> ?gec" "l \<noteq> y" for l y
        proof -
          obtain u v where leq: "l = cbox u v"
            using \<open>l \<in> d\<close> less.prems by auto
          have "interior (cbox u v \<inter> ?gec) = {}"
            using that division_split_right_inj leq less.prems by blast
          then show ?thesis
            unfolding leq interval_split[OF \<open>k \<in> Basis\<close>]
            by (auto intro: box_empty_imp)
        qed
        have d1_alt: "d1 = (\<lambda>l. l \<inter> ?lec) ` {l \<in> d. l \<inter> ?lec \<noteq> {}}"
          using d1_def by auto
        have d2_alt: "d2 = (\<lambda>l. l \<inter> ?gec) ` {l \<in> d. l \<inter> ?gec \<noteq> {}}"
          using d2_def by auto
        have "g (cbox a b) = F g d1 \<^bold>* F g d2" (is "_ = ?prev")
          unfolding * using \<open>k \<in> Basis\<close>
          by (auto dest: Basis_imp)
        also have "F g d1 = F (\<lambda>l. g (l \<inter> ?lec)) d"
          unfolding d1_alt using division_of_finite[OF less.prems] fxk_le
          by (subst reindex_nontrivial) (auto intro!: mono_neutral_cong_left)
        also have "F g d2 = F (\<lambda>l. g (l \<inter> ?gec)) d"
          unfolding d2_alt using division_of_finite[OF less.prems] fxk_ge
          by (subst reindex_nontrivial) (auto intro!: mono_neutral_cong_left)
        also have *: "\<forall>x\<in>d. g x = g (x \<inter> ?lec) \<^bold>* g (x \<inter> ?gec)"
          unfolding forall_in_division[OF \<open>d division_of cbox a b\<close>]
          using \<open>k \<in> Basis\<close>
          by (auto dest: Basis_imp)
        have "F (\<lambda>l. g (l \<inter> ?lec)) d \<^bold>* F (\<lambda>l. g (l \<inter> ?gec)) d = F g d"
          using * by (simp add: distrib)
        finally show ?thesis by auto
      qed
    qed
  qed
qed

proposition tagged_division:
  assumes "d tagged_division_of (cbox a b)"
  shows "F (\<lambda>(_, l). g l) d = g (cbox a b)"
proof -
  have "F (\<lambda>(_, k). g k) d = F g (snd ` d)"
    using assms box_empty_imp by (rule over_tagged_division_lemma)
  then show ?thesis
    unfolding assms [THEN division_of_tagged_division, THEN division] .
  qed

end

locale operative_real = comm_monoid_set +
  fixes g :: "real set \<Rightarrow> 'a"
  assumes neutral: "b \<le> a \<Longrightarrow> g {a..b} = \<^bold>1"
  assumes coalesce_less: "a < c \<Longrightarrow> c < b \<Longrightarrow> g {a..c} \<^bold>* g {c..b} = g {a..b}"
begin

sublocale operative where g = g
  rewrites "box = (greaterThanLessThan :: real \<Rightarrow> _)"
    and "cbox = (atLeastAtMost :: real \<Rightarrow> _)"
    and "\<And>x::real. x \<in> Basis \<longleftrightarrow> x = 1"
proof -
  show "operative f z g"
  proof
    show "g (cbox a b) = \<^bold>1" if "box a b = {}" for a b
      using that by (simp add: neutral)
    show "g (cbox a b) = g (cbox a b \<inter> {x. x \<bullet> k \<le> c}) \<^bold>* g (cbox a b \<inter> {x. c \<le> x \<bullet> k})"
      if "k \<in> Basis" for a b c k
    proof -
      from that have [simp]: "k = 1"
        by simp
      from neutral [of 0 1] neutral [of a a for a] coalesce_less
  have [simp]: "g {} = \<^bold>1" "\<And>a. g {a} = \<^bold>1"
    "\<And>a b c. a < c \<Longrightarrow> c < b \<Longrightarrow> g {a..c} \<^bold>* g {c..b} = g {a..b}"
    by auto
      have "g {a..b} = g {a..min b c} \<^bold>* g {max a c..b}"
    by (auto simp: min_def max_def le_less)
      then show "g (cbox a b) = g (cbox a b \<inter> {x. x \<bullet> k \<le> c}) \<^bold>* g (cbox a b \<inter> {x. c \<le> x \<bullet> k})"
        by (simp add: atMost_def [symmetric] atLeast_def [symmetric])
qed
  qed
  show "box = (greaterThanLessThan :: real \<Rightarrow> _)"
    and "cbox = (atLeastAtMost :: real \<Rightarrow> _)"
    and "\<And>x::real. x \<in> Basis \<longleftrightarrow> x = 1"
    by (simp_all add: fun_eq_iff)
qed

lemma coalesce_less_eq:
  "g {a..c} \<^bold>* g {c..b} = g {a..b}" if "a \<le> c" "c \<le> b"
  proof (cases "c = a \<or> c = b")
    case False
  with that have "a < c" "c < b"
    by auto
    then show ?thesis
    by (rule coalesce_less)
  next
    case True
  with that box_empty_imp [of a a] box_empty_imp [of b b] show ?thesis
    by safe simp_all
    qed

end

lemma operative_realI:
  "operative_real f z g" if "operative f z g"
proof -
  interpret operative f z g
    using that .
  show ?thesis
  proof
    show "g {a..b} = z" if "b \<le> a" for a b
      using that box_empty_imp by simp
    show "f (g {a..c}) (g {c..b}) = g {a..b}" if "a < c" "c < b" for a b c
      using that
    using Basis_imp [of 1 a b c]
      by (simp_all add: atMost_def [symmetric] atLeast_def [symmetric] max_def min_def)
qed
qed


subsection \<open>Special case of additivity we need for the FTC\<close>
(*fix add explanation here *)
lemma additive_tagged_division_1:
  fixes f :: "real \<Rightarrow> 'a::real_normed_vector"
  assumes "a \<le> b"
    and "p tagged_division_of {a..b}"
  shows "sum (\<lambda>(x,k). f(Sup k) - f(Inf k)) p = f b - f a"
proof -
  let ?f = "(\<lambda>k::(real) set. if k = {} then 0 else f(interval_upperbound k) - f(interval_lowerbound k))"
  interpret operative_real plus 0 ?f
    rewrites "comm_monoid_set.F (+) 0 = sum"
    by standard[1] (auto simp add: sum_def)
  have p_td: "p tagged_division_of cbox a b"
    using assms(2) box_real(2) by presburger
  have **: "cbox a b \<noteq> {}"
    using assms(1) by auto
  then have "f b - f a = (\<Sum>(x, l)\<in>p. if l = {} then 0 else f (interval_upperbound l) - f (interval_lowerbound l))"
    proof -
      have "(if cbox a b = {} then 0 else f (interval_upperbound (cbox a b)) - f (interval_lowerbound (cbox a b))) = f b - f a"
        using assms by auto
      then show ?thesis
        using p_td assms by (simp add: tagged_division) 
    qed 
  then show ?thesis
    using assms by (auto intro!: sum.cong)
qed


subsection \<open>Fine-ness of a partition w.r.t. a gauge\<close>

definition\<^marker>\<open>tag important\<close> fine  (infixr "fine" 46)
  where "d fine s \<longleftrightarrow> (\<forall>(x,k) \<in> s. k \<subseteq> d x)"

lemma fineI:
  assumes "\<And>x k. (x, k) \<in> s \<Longrightarrow> k \<subseteq> d x"
  shows "d fine s"
  using assms unfolding fine_def by auto

lemma fineD[dest]:
  assumes "d fine s"
  shows "\<And>x k. (x,k) \<in> s \<Longrightarrow> k \<subseteq> d x"
  using assms unfolding fine_def by auto

lemma fine_Int: "(\<lambda>x. d1 x \<inter> d2 x) fine p \<longleftrightarrow> d1 fine p \<and> d2 fine p"
  unfolding fine_def by auto

lemma fine_Inter:
 "(\<lambda>x. \<Inter>{f d x | d.  d \<in> s}) fine p \<longleftrightarrow> (\<forall>d\<in>s. (f d) fine p)"
  unfolding fine_def by blast

lemma fine_Un: "d fine p1 \<Longrightarrow> d fine p2 \<Longrightarrow> d fine (p1 \<union> p2)"
  unfolding fine_def by blast

lemma fine_Union: "(\<And>p. p \<in> ps \<Longrightarrow> d fine p) \<Longrightarrow> d fine (\<Union>ps)"
  unfolding fine_def by auto

lemma fine_subset: "p \<subseteq> q \<Longrightarrow> d fine q \<Longrightarrow> d fine p"
  unfolding fine_def by blast

subsection \<open>Some basic combining lemmas\<close>

lemma tagged_division_Union_exists:
  assumes "finite I"
    and "\<forall>i\<in>I. \<exists>p. p tagged_division_of i \<and> d fine p"
    and "\<forall>i1\<in>I. \<forall>i2\<in>I. i1 \<noteq> i2 \<longrightarrow> interior i1 \<inter> interior i2 = {}"
    and "\<Union>I = i"
   obtains p where "p tagged_division_of i" and "d fine p"
proof -
  obtain pfn where pfn:
    "\<And>x. x \<in> I \<Longrightarrow> pfn x tagged_division_of x"
    "\<And>x. x \<in> I \<Longrightarrow> d fine pfn x"
    using bchoice[OF assms(2)] by auto
  show thesis
    apply (rule_tac p="\<Union>(pfn ` I)" in that)
    using assms(1) assms(3) assms(4) pfn(1) tagged_division_Union apply force
    by (metis (mono_tags, lifting) fine_Union imageE pfn(2))
qed
(* FIXME structure here, do not have one lemma in each subsection *)

subsection\<^marker>\<open>tag unimportant\<close> \<open>The set we're concerned with must be closed\<close>

lemma division_of_closed:
  fixes i :: "'n::euclidean_space set"
  shows "s division_of i \<Longrightarrow> closed i"
  unfolding division_of_def by fastforce
(* FIXME structure here, do not have one lemma in each subsection *)
subsection \<open>General bisection principle for intervals; might be useful elsewhere\<close>
(* FIXME  move? *)
lemma interval_bisection_step:
  fixes type :: "'a::euclidean_space"
  assumes emp: "P {}"
    and Un: "\<And>S T. \<lbrakk>P S; P T; interior(S) \<inter> interior(T) = {}\<rbrakk> \<Longrightarrow> P (S \<union> T)"
    and non: "\<not> P (cbox a (b::'a))"
  obtains c d where "\<not> P (cbox c d)"
    and "\<And>i. i \<in> Basis \<Longrightarrow> a\<bullet>i \<le> c\<bullet>i \<and> c\<bullet>i \<le> d\<bullet>i \<and> d\<bullet>i \<le> b\<bullet>i \<and> 2 * (d\<bullet>i - c\<bullet>i) \<le> b\<bullet>i - a\<bullet>i"
proof -
  have "cbox a b \<noteq> {}"
    using emp non by metis
  then have ab: "\<And>i. i\<in>Basis \<Longrightarrow> a \<bullet> i \<le> b \<bullet> i"
    by (force simp: mem_box)
  have UN_cases: "\<lbrakk>finite \<F>;
           \<And>S. S\<in>\<F> \<Longrightarrow> P S;
           \<And>S. S\<in>\<F> \<Longrightarrow> \<exists>a b. S = cbox a b;
           \<And>S T. S\<in>\<F> \<Longrightarrow> T\<in>\<F> \<Longrightarrow> S \<noteq> T \<Longrightarrow> interior S \<inter> interior T = {}\<rbrakk> \<Longrightarrow> P (\<Union>\<F>)" for \<F>
  proof (induct \<F> rule: finite_induct)
    case empty show ?case
      using emp by auto
  next
    case (insert x f)
    then show ?case
      unfolding Union_insert by (metis Int_interior_Union_intervals Un insert_iff open_interior)
  qed
  let ?ab = "\<lambda>i. (a\<bullet>i + b\<bullet>i) / 2"
  let ?A = "{cbox c d | c d::'a. \<forall>i\<in>Basis. (c\<bullet>i = a\<bullet>i) \<and> (d\<bullet>i = ?ab i) \<or>
    (c\<bullet>i = ?ab i) \<and> (d\<bullet>i = b\<bullet>i)}"
  have "P (\<Union>?A)" 
    if "\<And>c d.  \<forall>i\<in>Basis. a\<bullet>i \<le> c\<bullet>i \<and> c\<bullet>i \<le> d\<bullet>i \<and> d\<bullet>i \<le> b\<bullet>i \<and> 2 * (d\<bullet>i - c\<bullet>i) \<le> b\<bullet>i - a\<bullet>i \<Longrightarrow> P (cbox c d)"
  proof (rule UN_cases)
    let ?B = "(\<lambda>S. cbox (\<Sum>i\<in>Basis. (if i \<in> S then a\<bullet>i else ?ab i) *\<^sub>R i::'a)
                        (\<Sum>i\<in>Basis. (if i \<in> S then ?ab i else b\<bullet>i) *\<^sub>R i)) ` {s. s \<subseteq> Basis}"
    have "?A \<subseteq> ?B"
    proof
      fix x
      assume "x \<in> ?A"
      then obtain c d
        where x:  "x = cbox c d"
          "\<And>i. i \<in> Basis \<Longrightarrow>
                        c \<bullet> i = a \<bullet> i \<and> d \<bullet> i = ?ab i \<or> c \<bullet> i = ?ab i \<and> d \<bullet> i = b \<bullet> i" 
        by blast
      have "c = (\<Sum>i\<in>Basis. (if c \<bullet> i = a \<bullet> i then a \<bullet> i else ?ab i) *\<^sub>R i)"
           "d = (\<Sum>i\<in>Basis. (if c \<bullet> i = a \<bullet> i then ?ab i else b \<bullet> i) *\<^sub>R i)"
        using x(2) ab by (fastforce simp add: euclidean_eq_iff[where 'a='a])+
      then show "x \<in> ?B"
        unfolding x by (rule_tac x="{i. i\<in>Basis \<and> c\<bullet>i = a\<bullet>i}" in image_eqI) auto
    qed
    then show "finite ?A"
      by (rule finite_subset) auto
  next
    fix S
    assume "S \<in> ?A"
    then obtain c d
      where s: "S = cbox c d"
               "\<And>i. i \<in> Basis \<Longrightarrow> c \<bullet> i = a \<bullet> i \<and> d \<bullet> i = ?ab i \<or> c \<bullet> i = ?ab i \<and> d \<bullet> i = b \<bullet> i"
      by blast
    show "P S"
      unfolding s using ab s(2) by (fastforce intro!: that)
    show "\<exists>a b. S = cbox a b"
      unfolding s by auto
    fix T
    assume "T \<in> ?A"
    then obtain e f where t:
      "T = cbox e f"
      "\<And>i. i \<in> Basis \<Longrightarrow> e \<bullet> i = a \<bullet> i \<and> f \<bullet> i = ?ab i \<or> e \<bullet> i = ?ab i \<and> f \<bullet> i = b \<bullet> i"
      by blast
    assume "S \<noteq> T"
    then have "\<not> (c = e \<and> d = f)"
      unfolding s t by auto
    then obtain i where "c\<bullet>i \<noteq> e\<bullet>i \<or> d\<bullet>i \<noteq> f\<bullet>i" and i': "i \<in> Basis"
      unfolding euclidean_eq_iff[where 'a='a] by auto
    then have i: "c\<bullet>i \<noteq> e\<bullet>i" "d\<bullet>i \<noteq> f\<bullet>i"
      using s(2) t(2) apply fastforce
      using t(2)[OF i'] \<open>c \<bullet> i \<noteq> e \<bullet> i \<or> d \<bullet> i \<noteq> f \<bullet> i\<close> i' s(2) t(2) by fastforce
    have *: "\<And>s t. (\<And>a. a \<in> s \<Longrightarrow> a \<in> t \<Longrightarrow> False) \<Longrightarrow> s \<inter> t = {}"
      by auto
    show "interior S \<inter> interior T = {}"
      unfolding s t interior_cbox
    proof (rule *)
      fix x
      assume "x \<in> box c d" "x \<in> box e f"
      then have x: "c\<bullet>i < d\<bullet>i" "e\<bullet>i < f\<bullet>i" "c\<bullet>i < f\<bullet>i" "e\<bullet>i < d\<bullet>i"
        unfolding mem_box using i'  by force+
      show False  using s(2)[OF i'] t(2)[OF i'] and i x  
        by auto
    qed
  qed
  also have "\<Union>?A = cbox a b"
  proof (rule set_eqI,rule)
    fix x
    assume "x \<in> \<Union>?A"
    then obtain c d where x:
      "x \<in> cbox c d"
      "\<And>i. i \<in> Basis \<Longrightarrow> c \<bullet> i = a \<bullet> i \<and> d \<bullet> i = ?ab i \<or> c \<bullet> i = ?ab i \<and> d \<bullet> i = b \<bullet> i"
      by blast
    then show "x\<in>cbox a b"
      unfolding mem_box by force
  next
    fix x
    assume x: "x \<in> cbox a b"
    then have "\<forall>i\<in>Basis. \<exists>c d. (c = a\<bullet>i \<and> d = ?ab i \<or> c = ?ab i \<and> d = b\<bullet>i) \<and> c\<le>x\<bullet>i \<and> x\<bullet>i \<le> d"
      (is "\<forall>i\<in>Basis. \<exists>c d. ?P i c d")
      unfolding mem_box by (metis linear)
    then obtain \<alpha> \<beta> where "\<forall>i\<in>Basis. (\<alpha> \<bullet> i = a \<bullet> i \<and> \<beta> \<bullet> i = ?ab i \<or>
         \<alpha> \<bullet> i = ?ab i \<and> \<beta> \<bullet> i = b \<bullet> i) \<and> \<alpha> \<bullet> i \<le> x \<bullet> i \<and> x \<bullet> i \<le> \<beta> \<bullet> i"
      by (auto simp: choice_Basis_iff)
    then show "x\<in>\<Union>?A"
      by (force simp add: mem_box)
  qed
  finally show thesis
      by (metis (no_types, lifting) assms(3) that)
qed

lemma interval_bisection:
  fixes type :: "'a::euclidean_space"
  assumes "P {}"
    and Un: "\<And>S T. \<lbrakk>P S; P T; interior(S) \<inter> interior(T) = {}\<rbrakk> \<Longrightarrow> P (S \<union> T)"
    and "\<not> P (cbox a (b::'a))"
  obtains x where "x \<in> cbox a b"
    and "\<forall>e>0. \<exists>c d. x \<in> cbox c d \<and> cbox c d \<subseteq> ball x e \<and> cbox c d \<subseteq> cbox a b \<and> \<not> P (cbox c d)"
proof -
  have "\<forall>x. \<exists>y. \<not> P (cbox (fst x) (snd x)) \<longrightarrow> (\<not> P (cbox (fst y) (snd y)) \<and>
    (\<forall>i\<in>Basis. fst x\<bullet>i \<le> fst y\<bullet>i \<and> fst y\<bullet>i \<le> snd y\<bullet>i \<and> snd y\<bullet>i \<le> snd x\<bullet>i \<and>
       2 * (snd y\<bullet>i - fst y\<bullet>i) \<le> snd x\<bullet>i - fst x\<bullet>i))" (is "\<forall>x. ?P x")
  proof
    show "?P x" for x
    proof (cases "P (cbox (fst x) (snd x))")
      case True
      then show ?thesis by auto
    next
      case False
      obtain c d where "\<not> P (cbox c d)"
        "\<And>i. i \<in> Basis \<Longrightarrow>
           fst x \<bullet> i \<le> c \<bullet> i \<and>
           c \<bullet> i \<le> d \<bullet> i \<and>
           d \<bullet> i \<le> snd x \<bullet> i \<and>
           2 * (d \<bullet> i - c \<bullet> i) \<le> snd x \<bullet> i - fst x \<bullet> i"
        by (blast intro: interval_bisection_step[of P, OF assms(1-2) False])
      then show ?thesis
        by (rule_tac x="(c,d)" in exI) auto
    qed
  qed
  then obtain f where f:
    "\<forall>x.
      \<not> P (cbox (fst x) (snd x)) \<longrightarrow>
      \<not> P (cbox (fst (f x)) (snd (f x))) \<and>
        (\<forall>i\<in>Basis.
            fst x \<bullet> i \<le> fst (f x) \<bullet> i \<and>
            fst (f x) \<bullet> i \<le> snd (f x) \<bullet> i \<and>
            snd (f x) \<bullet> i \<le> snd x \<bullet> i \<and>
            2 * (snd (f x) \<bullet> i - fst (f x) \<bullet> i) \<le> snd x \<bullet> i - fst x \<bullet> i)" by metis
  define AB A B where ab_def: "AB n = (f ^^ n) (a,b)" "A n = fst(AB n)" "B n = snd(AB n)" for n
  have [simp]: "A 0 = a" "B 0 = b" and ABRAW: "\<And>n. \<not> P (cbox (A(Suc n)) (B(Suc n))) \<and>
    (\<forall>i\<in>Basis. A(n)\<bullet>i \<le> A(Suc n)\<bullet>i \<and> A(Suc n)\<bullet>i \<le> B(Suc n)\<bullet>i \<and> B(Suc n)\<bullet>i \<le> B(n)\<bullet>i \<and>
    2 * (B(Suc n)\<bullet>i - A(Suc n)\<bullet>i) \<le> B(n)\<bullet>i - A(n)\<bullet>i)" (is "\<And>n. ?P n")
  proof -
    show "A 0 = a" "B 0 = b"
      unfolding ab_def by auto
    note S = ab_def funpow.simps o_def id_apply
    show "?P n" for n
    proof (induct n)
      case 0
      then show ?case
        unfolding S using \<open>\<not> P (cbox a b)\<close> f by auto
    next
      case (Suc n)
      show ?case
        unfolding S
        apply (rule f[rule_format])
        using Suc
        unfolding S
        apply auto
        done
    qed
  qed
  then have AB: "A(n)\<bullet>i \<le> A(Suc n)\<bullet>i" "A(Suc n)\<bullet>i \<le> B(Suc n)\<bullet>i" 
                 "B(Suc n)\<bullet>i \<le> B(n)\<bullet>i" "2 * (B(Suc n)\<bullet>i - A(Suc n)\<bullet>i) \<le> B(n)\<bullet>i - A(n)\<bullet>i" 
                if "i\<in>Basis" for i n
    using that by blast+
  have notPAB: "\<not> P (cbox (A(Suc n)) (B(Suc n)))" for n
    using ABRAW by blast
  have interv: "\<exists>n. \<forall>x\<in>cbox (A n) (B n). \<forall>y\<in>cbox (A n) (B n). dist x y < e"
    if e: "0 < e" for e
  proof -
    obtain n where n: "(\<Sum>i\<in>Basis. b \<bullet> i - a \<bullet> i) / e < 2 ^ n"
      using real_arch_pow[of 2 "(sum (\<lambda>i. b\<bullet>i - a\<bullet>i) Basis) / e"] by auto
    show ?thesis
    proof (rule exI [where x=n], clarify)
      fix x y
      assume xy: "x\<in>cbox (A n) (B n)" "y\<in>cbox (A n) (B n)"
      have "dist x y \<le> sum (\<lambda>i. \<bar>(x - y)\<bullet>i\<bar>) Basis"
        unfolding dist_norm by(rule norm_le_l1)
      also have "\<dots> \<le> sum (\<lambda>i. B n\<bullet>i - A n\<bullet>i) Basis"
      proof (rule sum_mono)
        fix i :: 'a
        assume i: "i \<in> Basis"
        show "\<bar>(x - y) \<bullet> i\<bar> \<le> B n \<bullet> i - A n \<bullet> i"
          using xy[unfolded mem_box,THEN bspec, OF i]
          by (auto simp: inner_diff_left)
      qed
      also have "\<dots> \<le> sum (\<lambda>i. b\<bullet>i - a\<bullet>i) Basis / 2^n"
        unfolding sum_divide_distrib
      proof (rule sum_mono)
        show "B n \<bullet> i - A n \<bullet> i \<le> (b \<bullet> i - a \<bullet> i) / 2 ^ n" if i: "i \<in> Basis" for i
        proof (induct n)
          case 0
          then show ?case
            unfolding AB by auto
        next
          case (Suc n)
          have "B (Suc n) \<bullet> i - A (Suc n) \<bullet> i \<le> (B n \<bullet> i - A n \<bullet> i) / 2"
            using AB(3) that AB(4)[of i n] using i by auto
          also have "\<dots> \<le> (b \<bullet> i - a \<bullet> i) / 2 ^ Suc n"
            using Suc by (auto simp add: field_simps)
          finally show ?case .
        qed
      qed
      also have "\<dots> < e"
        using n using e by (auto simp add: field_simps)
      finally show "dist x y < e" .
    qed
  qed
  {
    fix n m :: nat
    assume "m \<le> n" then have "cbox (A n) (B n) \<subseteq> cbox (A m) (B m)"
    proof (induction rule: inc_induct)
      case (step i)
      show ?case
        using AB by (intro order_trans[OF step.IH] subset_box_imp) auto
    qed simp
  } note ABsubset = this
  have "\<And>n. cbox (A n) (B n) \<noteq> {}"
    by (meson AB dual_order.trans interval_not_empty)
  then obtain x0 where x0: "\<And>n. x0 \<in> cbox (A n) (B n)"
    using decreasing_closed_nest [OF closed_cbox] ABsubset interv by blast
  show thesis
  proof (rule that[rule_format, of x0])
    show "x0\<in>cbox a b"
      using \<open>A 0 = a\<close> \<open>B 0 = b\<close> x0 by blast
    fix e :: real
    assume "e > 0"
    from interv[OF this] obtain n
      where n: "\<forall>x\<in>cbox (A n) (B n). \<forall>y\<in>cbox (A n) (B n). dist x y < e" ..
    have "\<not> P (cbox (A n) (B n))"
    proof (cases "0 < n")
      case True then show ?thesis 
        by (metis Suc_pred' notPAB) 
    next
      case False then show ?thesis
        using \<open>A 0 = a\<close> \<open>B 0 = b\<close> \<open>\<not> P (cbox a b)\<close> by blast
    qed
    moreover have "cbox (A n) (B n) \<subseteq> ball x0 e"
      using n using x0[of n] by auto
    moreover have "cbox (A n) (B n) \<subseteq> cbox a b"
      using ABsubset \<open>A 0 = a\<close> \<open>B 0 = b\<close> by blast
    ultimately show "\<exists>c d. x0 \<in> cbox c d \<and> cbox c d \<subseteq> ball x0 e \<and> cbox c d \<subseteq> cbox a b \<and> \<not> P (cbox c d)"
      apply (rule_tac x="A n" in exI)
      apply (rule_tac x="B n" in exI)
      apply (auto simp: x0)
      done
  qed
qed


subsection \<open>Cousin's lemma\<close>

lemma fine_division_exists: (*FIXME rename(?) *)
  fixes a b :: "'a::euclidean_space"
  assumes "gauge g"
  obtains p where "p tagged_division_of (cbox a b)" "g fine p"
proof (cases "\<exists>p. p tagged_division_of (cbox a b) \<and> g fine p")
  case True
  then show ?thesis
    using that by auto
next
  case False
  assume "\<not> (\<exists>p. p tagged_division_of (cbox a b) \<and> g fine p)"
  obtain x where x:
      "x \<in> (cbox a b)"
      "\<And>e. 0 < e \<Longrightarrow>
        \<exists>c d.
          x \<in> cbox c d \<and>
          cbox c d \<subseteq> ball x e \<and>
          cbox c d \<subseteq> (cbox a b) \<and>
          \<not> (\<exists>p. p tagged_division_of cbox c d \<and> g fine p)"
    apply (rule interval_bisection[of "\<lambda>s. \<exists>p. p tagged_division_of s \<and> g fine p", OF _ _ False])
    apply (simp add: fine_def)
    apply (metis tagged_division_Un fine_Un)
    apply auto
    done
  obtain e where e: "e > 0" "ball x e \<subseteq> g x"
    using gaugeD[OF assms, of x] unfolding open_contains_ball by auto
  from x(2)[OF e(1)]
  obtain c d where c_d: "x \<in> cbox c d"
                        "cbox c d \<subseteq> ball x e"
                        "cbox c d \<subseteq> cbox a b"
                        "\<not> (\<exists>p. p tagged_division_of cbox c d \<and> g fine p)"
    by blast
  have "g fine {(x, cbox c d)}"
    unfolding fine_def using e using c_d(2) by auto
  then show ?thesis
    using tagged_division_of_self[OF c_d(1)] using c_d by auto
qed

lemma fine_division_exists_real:
  fixes a b :: real
  assumes "gauge g"
  obtains p where "p tagged_division_of {a .. b}" "g fine p"
  by (metis assms box_real(2) fine_division_exists)

subsection \<open>A technical lemma about "refinement" of division\<close>

lemma tagged_division_finer:
  fixes p :: "('a::euclidean_space \<times> ('a::euclidean_space set)) set"
  assumes ptag: "p tagged_division_of (cbox a b)"
    and "gauge d"
  obtains q where "q tagged_division_of (cbox a b)"
    and "d fine q"
    and "\<forall>(x,k) \<in> p. k \<subseteq> d(x) \<longrightarrow> (x,k) \<in> q"
proof -
  have p: "finite p" "p tagged_partial_division_of (cbox a b)"
    using ptag tagged_division_of_def by blast+
  have "(\<exists>q. q tagged_division_of (\<Union>{k. \<exists>x. (x,k) \<in> p}) \<and> d fine q \<and> (\<forall>(x,k) \<in> p. k \<subseteq> d(x) \<longrightarrow> (x,k) \<in> q))" 
    if "finite p" "p tagged_partial_division_of (cbox a b)" "gauge d" for p
    using that
  proof (induct p)
    case empty
    show ?case
      by (force simp add: fine_def)
  next
    case (insert xk p)
    obtain x k where xk: "xk = (x, k)"
      using surj_pair[of xk] by metis 
    obtain q1 where q1: "q1 tagged_division_of \<Union>{k. \<exists>x. (x, k) \<in> p}"
                and "d fine q1"
                and q1I: "\<And>x k. \<lbrakk>(x, k)\<in>p;  k \<subseteq> d x\<rbrakk> \<Longrightarrow> (x, k) \<in> q1"
      using case_prodD tagged_partial_division_subset[OF insert(4) subset_insertI]
      by (metis (mono_tags, lifting) insert.hyps(3) insert.prems(2))
    have *: "\<Union>{l. \<exists>y. (y,l) \<in> insert xk p} = k \<union> \<Union>{l. \<exists>y. (y,l) \<in> p}"
      unfolding xk by auto
    note p = tagged_partial_division_ofD[OF insert(4)]
    obtain u v where uv: "k = cbox u v"
      using p(4) xk by blast
    have "finite {k. \<exists>x. (x, k) \<in> p}"
      apply (rule finite_subset[of _ "snd ` p"])
      using image_iff apply fastforce
      using insert.hyps(1) by blast
    then have int: "interior (cbox u v) \<inter> interior (\<Union>{k. \<exists>x. (x, k) \<in> p}) = {}"
    proof (rule Int_interior_Union_intervals)
      show "open (interior (cbox u v))"
        by auto
      show "\<And>T. T \<in> {k. \<exists>x. (x, k) \<in> p} \<Longrightarrow> \<exists>a b. T = cbox a b"
        using p(4) by auto
      show "\<And>T. T \<in> {k. \<exists>x. (x, k) \<in> p} \<Longrightarrow> interior (cbox u v) \<inter> interior T = {}"
        by clarify (metis insert.hyps(2) insert_iff interior_cbox p(5) uv xk)
    qed
    show ?case
    proof (cases "cbox u v \<subseteq> d x")
      case True
      have "{(x, cbox u v)} tagged_division_of cbox u v"
        by (simp add: p(2) uv xk tagged_division_of_self)
      then have "{(x, cbox u v)} \<union> q1 tagged_division_of \<Union>{k. \<exists>x. (x, k) \<in> insert xk p}"
        unfolding * uv by (metis (no_types, lifting) int q1 tagged_division_Un)
      with True show ?thesis
        apply (rule_tac x="{(x,cbox u v)} \<union> q1" in exI)
        using \<open>d fine q1\<close> fine_def q1I uv xk apply fastforce
        done
    next
      case False
      obtain q2 where q2: "q2 tagged_division_of cbox u v" "d fine q2"
        using fine_division_exists[OF assms(2)] by blast
      show ?thesis
        apply (rule_tac x="q2 \<union> q1" in exI)
        apply (intro conjI)
        unfolding * uv
        apply (rule tagged_division_Un q2 q1 int fine_Un)+
          apply (auto intro: q1 q2 fine_Un \<open>d fine q1\<close> simp add: False q1I uv xk)
        done
    qed
  qed
  with p obtain q where q: "q tagged_division_of \<Union>{k. \<exists>x. (x, k) \<in> p}" "d fine q" "\<forall>(x, k)\<in>p. k \<subseteq> d x \<longrightarrow> (x, k) \<in> q"
    by (meson \<open>gauge d\<close>)
  with ptag that show ?thesis by auto
qed

subsubsection\<^marker>\<open>tag important\<close> \<open>Covering lemma\<close>

text\<open> Some technical lemmas used in the approximation results that follow. Proof of the covering
  lemma is an obvious multidimensional generalization of Lemma 3, p65 of Swartz's
  "Introduction to Gauge Integrals". \<close>

proposition covering_lemma:
  assumes "S \<subseteq> cbox a b" "box a b \<noteq> {}" "gauge g"
  obtains \<D> where
    "countable \<D>"  "\<Union>\<D> \<subseteq> cbox a b"
    "\<And>K. K \<in> \<D> \<Longrightarrow> interior K \<noteq> {} \<and> (\<exists>c d. K = cbox c d)"
    "pairwise (\<lambda>A B. interior A \<inter> interior B = {}) \<D>"
    "\<And>K. K \<in> \<D> \<Longrightarrow> \<exists>x \<in> S \<inter> K. K \<subseteq> g x"
    "\<And>u v. cbox u v \<in> \<D> \<Longrightarrow> \<exists>n. \<forall>i \<in> Basis. v \<bullet> i - u \<bullet> i = (b \<bullet> i - a \<bullet> i) / 2^n"
    "S \<subseteq> \<Union>\<D>"
proof -
  have aibi: "\<And>i. i \<in> Basis \<Longrightarrow> a \<bullet> i \<le> b \<bullet> i" and normab: "0 < norm(b - a)"
    using \<open>box a b \<noteq> {}\<close> box_eq_empty box_sing by fastforce+
  let ?K0 = "\<lambda>(n, f::'a\<Rightarrow>nat).
                    cbox (\<Sum>i \<in> Basis. (a \<bullet> i + (f i / 2^n) * (b \<bullet> i - a \<bullet> i)) *\<^sub>R i)
                         (\<Sum>i \<in> Basis. (a \<bullet> i + ((f i + 1) / 2^n) * (b \<bullet> i - a \<bullet> i)) *\<^sub>R i)"
  let ?D0 = "?K0 ` (SIGMA n:UNIV. Pi\<^sub>E Basis (\<lambda>i::'a. lessThan (2^n)))"
  obtain \<D>0 where count: "countable \<D>0"
             and sub: "\<Union>\<D>0 \<subseteq> cbox a b"
             and int:  "\<And>K. K \<in> \<D>0 \<Longrightarrow> (interior K \<noteq> {}) \<and> (\<exists>c d. K = cbox c d)"
             and intdj: "\<And>A B. \<lbrakk>A \<in> \<D>0; B \<in> \<D>0\<rbrakk> \<Longrightarrow> A \<subseteq> B \<or> B \<subseteq> A \<or> interior A \<inter> interior B = {}"
             and SK: "\<And>x. x \<in> S \<Longrightarrow> \<exists>K \<in> \<D>0. x \<in> K \<and> K \<subseteq> g x"
             and cbox: "\<And>u v. cbox u v \<in> \<D>0 \<Longrightarrow> \<exists>n. \<forall>i \<in> Basis. v \<bullet> i - u \<bullet> i = (b \<bullet> i - a \<bullet> i) / 2^n"
             and fin: "\<And>K. K \<in> \<D>0 \<Longrightarrow> finite {L \<in> \<D>0. K \<subseteq> L}"
  proof
    show "countable ?D0"
      by (simp add: countable_PiE)
  next
    show "\<Union>?D0 \<subseteq> cbox a b"
      apply (simp add: UN_subset_iff)
      apply (intro conjI allI ballI subset_box_imp)
       apply (simp add: field_simps)
      apply (auto intro: mult_right_mono aibi)
      apply (force simp: aibi scaling_mono nat_less_real_le dest: PiE_mem intro: mult_right_mono)
      done
  next
    show "\<And>K. K \<in> ?D0 \<Longrightarrow> interior K \<noteq> {} \<and> (\<exists>c d. K = cbox c d)"
      using \<open>box a b \<noteq> {}\<close>
      by (clarsimp simp: box_eq_empty) (fastforce simp add: field_split_simps dest: PiE_mem)
  next
    have realff: "(real w) * 2^m < (real v) * 2^n \<longleftrightarrow> w * 2^m < v * 2^n" for m n v w
      using of_nat_less_iff less_imp_of_nat_less by fastforce
    have *: "\<forall>v w. ?K0(m,v) \<subseteq> ?K0(n,w) \<or> ?K0(n,w) \<subseteq> ?K0(m,v) \<or> interior(?K0(m,v)) \<inter> interior(?K0(n,w)) = {}"
      for m n \<comment> \<open>The symmetry argument requires a single HOL formula\<close>
    proof (rule linorder_wlog [where a=m and b=n], intro allI impI)
      fix v w m and n::nat
      assume "m \<le> n" \<comment> \<open>WLOG we can assume \<^term>\<open>m \<le> n\<close>, when the first disjunct becomes impossible\<close>
      have "?K0(n,w) \<subseteq> ?K0(m,v) \<or> interior(?K0(m,v)) \<inter> interior(?K0(n,w)) = {}"
        apply (simp add: subset_box disjoint_interval)
        apply (rule ccontr)
        apply (clarsimp simp add: aibi mult_le_cancel_right divide_le_cancel not_less not_le)
        apply (drule_tac x=i in bspec, assumption)
        using \<open>m\<le>n\<close> realff [of _ _ "1+_"] realff [of "1+_"_ "1+_"]
        apply (auto simp: divide_simps add.commute not_le nat_le_iff_add realff)
         apply (simp_all add: power_add)
        apply (metis (no_types, opaque_lifting) mult_Suc mult_less_cancel2 not_less_eq mult.assoc)
        apply (metis (no_types, opaque_lifting) mult_Suc mult_less_cancel2 not_less_eq mult.assoc)
        done
      then show "?K0(m,v) \<subseteq> ?K0(n,w) \<or> ?K0(n,w) \<subseteq> ?K0(m,v) \<or> interior(?K0(m,v)) \<inter> interior(?K0(n,w)) = {}"
        by meson
    qed auto
    show "\<And>A B. \<lbrakk>A \<in> ?D0; B \<in> ?D0\<rbrakk> \<Longrightarrow> A \<subseteq> B \<or> B \<subseteq> A \<or> interior A \<inter> interior B = {}"
      apply (erule imageE SigmaE)+
      using * by simp
  next
    show "\<exists>K \<in> ?D0. x \<in> K \<and> K \<subseteq> g x" if "x \<in> S" for x
    proof (simp only: bex_simps split_paired_Bex_Sigma)
      show "\<exists>n. \<exists>f \<in> Basis \<rightarrow>\<^sub>E {..<2 ^ n}. x \<in> ?K0(n,f) \<and> ?K0(n,f) \<subseteq> g x"
      proof -
        obtain e where "0 < e"
                   and e: "\<And>y. (\<And>i. i \<in> Basis \<Longrightarrow> \<bar>x \<bullet> i - y \<bullet> i\<bar> \<le> e) \<Longrightarrow> y \<in> g x"
        proof -
          have "x \<in> g x" "open (g x)"
            using \<open>gauge g\<close> by (auto simp: gauge_def)
          then obtain \<epsilon> where "0 < \<epsilon>" and \<epsilon>: "ball x \<epsilon> \<subseteq> g x"
            using openE by blast
          have "norm (x - y) < \<epsilon>"
               if "(\<And>i. i \<in> Basis \<Longrightarrow> \<bar>x \<bullet> i - y \<bullet> i\<bar> \<le> \<epsilon> / (2 * real DIM('a)))" for y
          proof -
            have "norm (x - y) \<le> (\<Sum>i\<in>Basis. \<bar>x \<bullet> i - y \<bullet> i\<bar>)"
              by (metis (no_types, lifting) inner_diff_left norm_le_l1 sum.cong)
            also have "... \<le> DIM('a) * (\<epsilon> / (2 * real DIM('a)))"
              by (meson sum_bounded_above that)
            also have "... = \<epsilon> / 2"
              by (simp add: field_split_simps)
            also have "... < \<epsilon>"
              by (simp add: \<open>0 < \<epsilon>\<close>)
            finally show ?thesis .
          qed
          then show ?thesis
            by (rule_tac e = "\<epsilon> / 2 / DIM('a)" in that) (simp_all add:  \<open>0 < \<epsilon>\<close> dist_norm subsetD [OF \<epsilon>])
        qed
        have xab: "x \<in> cbox a b"
          using \<open>x \<in> S\<close> \<open>S \<subseteq> cbox a b\<close> by blast
        obtain n where n: "norm (b - a) / 2^n < e"
          using real_arch_pow_inv [of "e / norm(b - a)" "1/2"] normab \<open>0 < e\<close>
          by (auto simp: field_split_simps)
        then have "norm (b - a) < e * 2^n"
          by (auto simp: field_split_simps)
        then have bai: "b \<bullet> i - a \<bullet> i < e * 2 ^ n" if "i \<in> Basis" for i
        proof -
          have "b \<bullet> i - a \<bullet> i \<le> norm (b - a)"
            by (metis abs_of_nonneg dual_order.trans inner_diff_left linear norm_ge_zero Basis_le_norm that)
          also have "... < e * 2 ^ n"
            using \<open>norm (b - a) < e * 2 ^ n\<close> by blast
          finally show ?thesis .
        qed
        have D: "(a + n \<le> x \<and> x \<le> a + m) \<Longrightarrow> (a + n \<le> y \<and> y \<le> a + m) \<Longrightarrow> abs(x - y) \<le> m - n"
                 for a m n x and y::real
          by auto
        have "\<forall>i\<in>Basis. \<exists>k<2 ^ n. (a \<bullet> i + real k * (b \<bullet> i - a \<bullet> i) / 2 ^ n \<le> x \<bullet> i \<and>
               x \<bullet> i \<le> a \<bullet> i + (real k + 1) * (b \<bullet> i - a \<bullet> i) / 2 ^ n)"
        proof
          fix i::'a assume "i \<in> Basis"
          consider "x \<bullet> i = b \<bullet> i" | "x \<bullet> i < b \<bullet> i"
            using \<open>i \<in> Basis\<close> mem_box(2) xab by force
          then show "\<exists>k<2 ^ n. (a \<bullet> i + real k * (b \<bullet> i - a \<bullet> i) / 2 ^ n \<le> x \<bullet> i \<and>
                          x \<bullet> i \<le> a \<bullet> i + (real k + 1) * (b \<bullet> i - a \<bullet> i) / 2 ^ n)"
          proof cases
            case 1 then show ?thesis
              by (rule_tac x = "2^n - 1" in exI) (auto simp: algebra_simps field_split_simps of_nat_diff \<open>i \<in> Basis\<close> aibi)
          next
            case 2
            then have abi_less: "a \<bullet> i < b \<bullet> i"
              using \<open>i \<in> Basis\<close> xab by (auto simp: mem_box)
            let ?k = "nat \<lfloor>2 ^ n * (x \<bullet> i - a \<bullet> i) / (b \<bullet> i - a \<bullet> i)\<rfloor>"
            show ?thesis
            proof (intro exI conjI)
              show "?k < 2 ^ n"
                using aibi xab \<open>i \<in> Basis\<close>
                by (force simp: nat_less_iff floor_less_iff field_split_simps 2 mem_box)
            next
              have "a \<bullet> i + real ?k * (b \<bullet> i - a \<bullet> i) / 2 ^ n \<le>
                    a \<bullet> i + (2 ^ n * (x \<bullet> i - a \<bullet> i) / (b \<bullet> i - a \<bullet> i)) * (b \<bullet> i - a \<bullet> i) / 2 ^ n"
                apply (intro add_left_mono mult_right_mono divide_right_mono of_nat_floor)
                using aibi [OF \<open>i \<in> Basis\<close>] xab 2
                  apply (simp_all add: \<open>i \<in> Basis\<close> mem_box field_split_simps)
                done
              also have "... = x \<bullet> i"
                using abi_less by (simp add: field_split_simps)
              finally show "a \<bullet> i + real ?k * (b \<bullet> i - a \<bullet> i) / 2 ^ n \<le> x \<bullet> i" .
            next
              have "x \<bullet> i \<le> a \<bullet> i + (2 ^ n * (x \<bullet> i - a \<bullet> i) / (b \<bullet> i - a \<bullet> i)) * (b \<bullet> i - a \<bullet> i) / 2 ^ n"
                using abi_less by (simp add: field_split_simps)
              also have "... \<le> a \<bullet> i + (real ?k + 1) * (b \<bullet> i - a \<bullet> i) / 2 ^ n"
                apply (intro add_left_mono mult_right_mono divide_right_mono of_nat_floor)
                using aibi [OF \<open>i \<in> Basis\<close>] xab
                  apply (auto simp: \<open>i \<in> Basis\<close> mem_box divide_simps)
                done
              finally show "x \<bullet> i \<le> a \<bullet> i + (real ?k + 1) * (b \<bullet> i - a \<bullet> i) / 2 ^ n" .
            qed
          qed
        qed
        then have "\<exists>f\<in>Basis \<rightarrow>\<^sub>E {..<2 ^ n}. x \<in> ?K0(n,f)"
          apply (simp add: mem_box Bex_def)
          apply (clarify dest!: bchoice)
          apply (rule_tac x="restrict f Basis" in exI, simp)
          done
        moreover have "\<And>f. x \<in> ?K0(n,f) \<Longrightarrow> ?K0(n,f) \<subseteq> g x"
          apply (clarsimp simp add: mem_box)
          apply (rule e)
          apply (drule bspec D, assumption)+
          apply (erule order_trans)
          apply (simp add: divide_simps)
          using bai apply (force simp add: algebra_simps)
          done
        ultimately show ?thesis by auto
      qed
    qed
  next
    show "\<And>u v. cbox u v \<in> ?D0 \<Longrightarrow> \<exists>n. \<forall>i \<in> Basis. v \<bullet> i - u \<bullet> i = (b \<bullet> i - a \<bullet> i) / 2^n"
      by (force simp: eq_cbox box_eq_empty field_simps dest!: aibi)
  next
    obtain j::'a where "j \<in> Basis"
      using nonempty_Basis by blast
    have "finite {L \<in> ?D0. ?K0(n,f) \<subseteq> L}" if "f \<in> Basis \<rightarrow>\<^sub>E {..<2 ^ n}" for n f
    proof (rule finite_subset)
      let ?B = "(\<lambda>(n, f::'a\<Rightarrow>nat). cbox (\<Sum>i\<in>Basis. (a \<bullet> i + (f i) / 2^n * (b \<bullet> i - a \<bullet> i)) *\<^sub>R i)
                                        (\<Sum>i\<in>Basis. (a \<bullet> i + ((f i) + 1) / 2^n * (b \<bullet> i - a \<bullet> i)) *\<^sub>R i))
                ` (SIGMA m:atMost n. Pi\<^sub>E Basis (\<lambda>i::'a. lessThan (2^m)))"
      have "?K0(m,g) \<in> ?B" if "g \<in> Basis \<rightarrow>\<^sub>E {..<2 ^ m}" "?K0(n,f) \<subseteq> ?K0(m,g)" for m g
      proof -
        have dd: "w / m \<le> v / n \<and> (v+1) / n \<le> (w+1) / m
                  \<Longrightarrow> inverse n \<le> inverse m" for w m v n::real
          by (auto simp: field_split_simps)
        have bjaj: "b \<bullet> j - a \<bullet> j > 0"
          using \<open>j \<in> Basis\<close> \<open>box a b \<noteq> {}\<close> box_eq_empty(1) by fastforce
        have "((g j) / 2 ^ m) * (b \<bullet> j - a \<bullet> j) \<le> ((f j) / 2 ^ n) * (b \<bullet> j - a \<bullet> j) \<and>
              (((f j) + 1) / 2 ^ n) * (b \<bullet> j - a \<bullet> j) \<le> (((g j) + 1) / 2 ^ m) * (b \<bullet> j - a \<bullet> j)"
          using that \<open>j \<in> Basis\<close> by (simp add: subset_box field_split_simps aibi)
        then have "((g j) / 2 ^ m) \<le> ((f j) / 2 ^ n) \<and>
                   ((real(f j) + 1) / 2 ^ n) \<le> ((real(g j) + 1) / 2 ^ m)"
          by (metis bjaj mult.commute of_nat_1 of_nat_add mult_le_cancel_iff2)
        then have "inverse (2^n) \<le> (inverse (2^m) :: real)"
          by (rule dd)
        then have "m \<le> n"
          by auto
        show ?thesis
          by (rule imageI) (simp add: \<open>m \<le> n\<close> that)
      qed
      then show "{L \<in> ?D0. ?K0(n,f) \<subseteq> L} \<subseteq> ?B"
        by auto
      show "finite ?B"
        by (intro finite_imageI finite_SigmaI finite_atMost finite_lessThan finite_PiE finite_Basis)
    qed
    then show "finite {L \<in> ?D0. K \<subseteq> L}" if "K \<in> ?D0" for K
      using that by auto
  qed
  let ?D1 = "{K \<in> \<D>0. \<exists>x \<in> S \<inter> K. K \<subseteq> g x}"
  obtain \<D> where count: "countable \<D>"
             and sub: "\<Union>\<D> \<subseteq> cbox a b"  "S \<subseteq> \<Union>\<D>"
             and int:  "\<And>K. K \<in> \<D> \<Longrightarrow> (interior K \<noteq> {}) \<and> (\<exists>c d. K = cbox c d)"
             and intdj: "\<And>A B. \<lbrakk>A \<in> \<D>; B \<in> \<D>\<rbrakk> \<Longrightarrow> A \<subseteq> B \<or> B \<subseteq> A \<or> interior A \<inter> interior B = {}"
             and SK: "\<And>K. K \<in> \<D> \<Longrightarrow> \<exists>x. x \<in> S \<inter> K \<and> K \<subseteq> g x"
             and cbox: "\<And>u v. cbox u v \<in> \<D> \<Longrightarrow> \<exists>n. \<forall>i \<in> Basis. v \<bullet> i - u \<bullet> i = (b \<bullet> i - a \<bullet> i) / 2^n"
             and fin: "\<And>K. K \<in> \<D> \<Longrightarrow> finite {L. L \<in> \<D> \<and> K \<subseteq> L}"
  proof
    show "countable ?D1" using count countable_subset
      by (simp add: count countable_subset)
    show "\<Union>?D1 \<subseteq> cbox a b"
      using sub by blast
    show "S \<subseteq> \<Union>?D1"
      using SK by (force simp:)
    show "\<And>K. K \<in> ?D1 \<Longrightarrow> (interior K \<noteq> {}) \<and> (\<exists>c d. K = cbox c d)"
      using int by blast
    show "\<And>A B. \<lbrakk>A \<in> ?D1; B \<in> ?D1\<rbrakk> \<Longrightarrow> A \<subseteq> B \<or> B \<subseteq> A \<or> interior A \<inter> interior B = {}"
      using intdj by blast
    show "\<And>K. K \<in> ?D1 \<Longrightarrow> \<exists>x. x \<in> S \<inter> K \<and> K \<subseteq> g x"
      by auto
    show "\<And>u v. cbox u v \<in> ?D1 \<Longrightarrow> \<exists>n. \<forall>i \<in> Basis. v \<bullet> i - u \<bullet> i = (b \<bullet> i - a \<bullet> i) / 2^n"
      using cbox by blast
    show "\<And>K. K \<in> ?D1 \<Longrightarrow> finite {L. L \<in> ?D1 \<and> K \<subseteq> L}"
      using fin by simp (metis (mono_tags, lifting) Collect_mono rev_finite_subset)
  qed
  let ?\<D> = "{K \<in> \<D>. \<forall>K'. K' \<in> \<D> \<and> K \<noteq> K' \<longrightarrow> \<not>(K \<subseteq> K')}"
  show ?thesis
  proof (rule that)
    show "countable ?\<D>"
      by (blast intro: countable_subset [OF _ count])
    show "\<Union>?\<D> \<subseteq> cbox a b"
      using sub by blast
    show "S \<subseteq> \<Union>?\<D>"
    proof clarsimp
      fix x
      assume "x \<in> S"
      then obtain X where "x \<in> X" "X \<in> \<D>" using \<open>S \<subseteq> \<Union>\<D>\<close> by blast
      let ?R = "{(K,L). K \<in> \<D> \<and> L \<in> \<D> \<and> L \<subset> K}"
      have irrR: "irrefl ?R" by (force simp: irrefl_def)
      have traR: "trans ?R" by (force simp: trans_def)
      have finR: "\<And>x. finite {y. (y, x) \<in> ?R}"
        by simp (metis (mono_tags, lifting) fin \<open>X \<in> \<D>\<close> finite_subset mem_Collect_eq psubset_imp_subset subsetI)
      have "{X \<in> \<D>. x \<in> X} \<noteq> {}"
        using \<open>X \<in> \<D>\<close> \<open>x \<in> X\<close> by blast
      then obtain Y where "Y \<in> {X \<in> \<D>. x \<in> X}" "\<And>Y'. (Y', Y) \<in> ?R \<Longrightarrow> Y' \<notin> {X \<in> \<D>. x \<in> X}"
        by (rule wfE_min' [OF wf_finite_segments [OF irrR traR finR]]) blast
      then show "\<exists>Y. Y \<in> \<D> \<and> (\<forall>K'. K' \<in> \<D> \<and> Y \<noteq> K' \<longrightarrow> \<not> Y \<subseteq> K') \<and> x \<in> Y"
        by blast
    qed
    show "\<And>K. K \<in> ?\<D> \<Longrightarrow> interior K \<noteq> {} \<and> (\<exists>c d. K = cbox c d)"
      by (blast intro: dest: int)
    show "pairwise (\<lambda>A B. interior A \<inter> interior B = {}) ?\<D>"
      using intdj by (simp add: pairwise_def) metis
    show "\<And>K. K \<in> ?\<D> \<Longrightarrow> \<exists>x \<in> S \<inter> K. K \<subseteq> g x"
      using SK by force
    show "\<And>u v. cbox u v \<in> ?\<D> \<Longrightarrow> \<exists>n. \<forall>i\<in>Basis. v \<bullet> i - u \<bullet> i = (b \<bullet> i - a \<bullet> i) / 2^n"
      using cbox by force
    qed
qed

subsection \<open>Division filter\<close>

text \<open>Divisions over all gauges towards finer divisions.\<close>

definition\<^marker>\<open>tag important\<close> division_filter :: "'a::euclidean_space set \<Rightarrow> ('a \<times> 'a set) set filter"
  where "division_filter s = (INF g\<in>{g. gauge g}. principal {p. p tagged_division_of s \<and> g fine p})"

proposition eventually_division_filter:
  "(\<forall>\<^sub>F p in division_filter s. P p) \<longleftrightarrow>
    (\<exists>g. gauge g \<and> (\<forall>p. p tagged_division_of s \<and> g fine p \<longrightarrow> P p))"
  unfolding division_filter_def
proof (subst eventually_INF_base; clarsimp)
  fix g1 g2 :: "'a \<Rightarrow> 'a set" show "gauge g1 \<Longrightarrow> gauge g2 \<Longrightarrow> \<exists>x. gauge x \<and>
    {p. p tagged_division_of s \<and> x fine p} \<subseteq> {p. p tagged_division_of s \<and> g1 fine p} \<and>
    {p. p tagged_division_of s \<and> x fine p} \<subseteq> {p. p tagged_division_of s \<and> g2 fine p}"
    by (intro exI[of _ "\<lambda>x. g1 x \<inter> g2 x"]) (auto simp: fine_Int)
qed (auto simp: eventually_principal)

lemma division_filter_not_empty: "division_filter (cbox a b) \<noteq> bot"
  unfolding trivial_limit_def eventually_division_filter
  by (auto elim: fine_division_exists)

lemma eventually_division_filter_tagged_division:
  "eventually (\<lambda>p. p tagged_division_of s) (division_filter s)"
  unfolding eventually_division_filter by (intro exI[of _ "\<lambda>x. ball x 1"]) auto

end
