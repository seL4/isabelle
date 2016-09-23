(*  Author:     John Harrison
    Author:     Robert Himmelmann, TU Muenchen (Translation from HOL light); proofs reworked by LCP
*)

section \<open>Henstock-Kurzweil gauge integration in many dimensions.\<close>

theory Henstock_Kurzweil_Integration
imports
  Lebesgue_Measure
begin

lemmas scaleR_simps = scaleR_zero_left scaleR_minus_left scaleR_left_diff_distrib
  scaleR_zero_right scaleR_minus_right scaleR_right_diff_distrib scaleR_eq_0_iff
  scaleR_cancel_left scaleR_cancel_right scaleR_add_right scaleR_add_left real_vector_class.scaleR_one


subsection \<open>Sundries\<close>

lemma conjunctD2: assumes "a \<and> b" shows a b using assms by auto
lemma conjunctD3: assumes "a \<and> b \<and> c" shows a b c using assms by auto
lemma conjunctD4: assumes "a \<and> b \<and> c \<and> d" shows a b c d using assms by auto

lemma cond_cases: "(P \<Longrightarrow> Q x) \<Longrightarrow> (\<not> P \<Longrightarrow> Q y) \<Longrightarrow> Q (if P then x else y)"
  by auto

declare norm_triangle_ineq4[intro]

lemma transitive_stepwise_le:
  assumes "\<And>x. R x x" "\<And>x y z. R x y \<Longrightarrow> R y z \<Longrightarrow> R x z" and "\<And>n. R n (Suc n)"
  shows "\<forall>n\<ge>m. R m n"
proof (intro allI impI)
  show "m \<le> n \<Longrightarrow> R m n" for n
    by (induction rule: dec_induct)
       (use assms in blast)+
qed

subsection \<open>Some useful lemmas about intervals.\<close>

lemma empty_as_interval: "{} = cbox One (0::'a::euclidean_space)"
  using nonempty_Basis
  by (fastforce simp add: set_eq_iff mem_box)

lemma interior_subset_union_intervals:
  assumes "i = cbox a b"
    and "j = cbox c d"
    and "interior j \<noteq> {}"
    and "i \<subseteq> j \<union> s"
    and "interior i \<inter> interior j = {}"
  shows "interior i \<subseteq> interior s"
proof -
  have "box a b \<inter> cbox c d = {}"
     using inter_interval_mixed_eq_empty[of c d a b] and assms(3,5)
     unfolding assms(1,2) interior_cbox by auto
  moreover
  have "box a b \<subseteq> cbox c d \<union> s"
    apply (rule order_trans,rule box_subset_cbox)
    using assms(4) unfolding assms(1,2)
    apply auto
    done
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
      by (simp add: closure_box)
  qed
  finally show ?thesis .
qed

lemma inter_interior_unions_intervals:
    "finite f \<Longrightarrow> open s \<Longrightarrow> \<forall>t\<in>f. \<exists>a b. t = cbox a b \<Longrightarrow> \<forall>t\<in>f. s \<inter> (interior t) = {} \<Longrightarrow> s \<inter> interior (\<Union>f) = {}"
  using interior_Union_subset_cbox[of f "UNIV - s"] by auto

lemma interval_split:
  fixes a :: "'a::euclidean_space"
  assumes "k \<in> Basis"
  shows
    "cbox a b \<inter> {x. x\<bullet>k \<le> c} = cbox a (\<Sum>i\<in>Basis. (if i = k then min (b\<bullet>k) c else b\<bullet>i) *\<^sub>R i)"
    "cbox a b \<inter> {x. x\<bullet>k \<ge> c} = cbox (\<Sum>i\<in>Basis. (if i = k then max (a\<bullet>k) c else a\<bullet>i) *\<^sub>R i) b"
  apply (rule_tac[!] set_eqI)
  unfolding Int_iff mem_box mem_Collect_eq
  using assms
  apply auto
  done

lemma interval_not_empty: "\<forall>i\<in>Basis. a\<bullet>i \<le> b\<bullet>i \<Longrightarrow> cbox a b \<noteq> {}"
  by (simp add: box_ne_empty)

subsection \<open>Bounds on intervals where they exist.\<close>

definition interval_upperbound :: "('a::euclidean_space) set \<Rightarrow> 'a"
  where "interval_upperbound s = (\<Sum>i\<in>Basis. (SUP x:s. x\<bullet>i) *\<^sub>R i)"

definition interval_lowerbound :: "('a::euclidean_space) set \<Rightarrow> 'a"
  where "interval_lowerbound s = (\<Sum>i\<in>Basis. (INF x:s. x\<bullet>i) *\<^sub>R i)"

lemma interval_upperbound[simp]:
  "\<forall>i\<in>Basis. a\<bullet>i \<le> b\<bullet>i \<Longrightarrow>
    interval_upperbound (cbox a b) = (b::'a::euclidean_space)"
  unfolding interval_upperbound_def euclidean_representation_setsum cbox_def
  by (safe intro!: cSup_eq) auto

lemma interval_lowerbound[simp]:
  "\<forall>i\<in>Basis. a\<bullet>i \<le> b\<bullet>i \<Longrightarrow>
    interval_lowerbound (cbox a b) = (a::'a::euclidean_space)"
  unfolding interval_lowerbound_def euclidean_representation_setsum cbox_def
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
  have "(\<Sum>i\<in>Basis. (SUP x:A \<times> B. x \<bullet> (i, 0)) *\<^sub>R i) = (\<Sum>i\<in>Basis. (SUP x:A. x \<bullet> i) *\<^sub>R i)"
      by (subst (2) fst_image_times') (simp del: fst_image_times add: o_def inner_Pair_0)
  moreover from assms have snd_image_times': "B = snd ` (A \<times> B)" by simp
  have "(\<Sum>i\<in>Basis. (SUP x:A \<times> B. x \<bullet> (0, i)) *\<^sub>R i) = (\<Sum>i\<in>Basis. (SUP x:B. x \<bullet> i) *\<^sub>R i)"
      by (subst (2) snd_image_times') (simp del: snd_image_times add: o_def inner_Pair_0)
  ultimately show ?thesis unfolding interval_upperbound_def
      by (subst setsum_Basis_prod_eq) (auto simp add: setsum_prod)
qed

lemma interval_lowerbound_Times:
  assumes "A \<noteq> {}" and "B \<noteq> {}"
  shows "interval_lowerbound (A \<times> B) = (interval_lowerbound A, interval_lowerbound B)"
proof-
  from assms have fst_image_times': "A = fst ` (A \<times> B)" by simp
  have "(\<Sum>i\<in>Basis. (INF x:A \<times> B. x \<bullet> (i, 0)) *\<^sub>R i) = (\<Sum>i\<in>Basis. (INF x:A. x \<bullet> i) *\<^sub>R i)"
      by (subst (2) fst_image_times') (simp del: fst_image_times add: o_def inner_Pair_0)
  moreover from assms have snd_image_times': "B = snd ` (A \<times> B)" by simp
  have "(\<Sum>i\<in>Basis. (INF x:A \<times> B. x \<bullet> (0, i)) *\<^sub>R i) = (\<Sum>i\<in>Basis. (INF x:B. x \<bullet> i) *\<^sub>R i)"
      by (subst (2) snd_image_times') (simp del: snd_image_times add: o_def inner_Pair_0)
  ultimately show ?thesis unfolding interval_lowerbound_def
      by (subst setsum_Basis_prod_eq) (auto simp add: setsum_prod)
qed

subsection \<open>Content (length, area, volume...) of an interval.\<close>

abbreviation content :: "'a::euclidean_space set \<Rightarrow> real"
  where "content s \<equiv> measure lborel s"

lemma content_cbox_cases:
  "content (cbox a b) = (if \<forall>i\<in>Basis. a\<bullet>i \<le> b\<bullet>i then setprod (\<lambda>i. b\<bullet>i - a\<bullet>i) Basis else 0)"
  by (simp add: measure_lborel_cbox_eq inner_diff)

lemma content_cbox: "\<forall>i\<in>Basis. a\<bullet>i \<le> b\<bullet>i \<Longrightarrow> content (cbox a b) = (\<Prod>i\<in>Basis. b\<bullet>i - a\<bullet>i)"
  unfolding content_cbox_cases by simp

lemma content_cbox': "cbox a b \<noteq> {} \<Longrightarrow> content (cbox a b) = (\<Prod>i\<in>Basis. b\<bullet>i - a\<bullet>i)"
  by (simp add: box_ne_empty inner_diff)

lemma content_real: "a \<le> b \<Longrightarrow> content {a..b} = b - a"
  by simp

lemma abs_eq_content: "\<bar>y - x\<bar> = (if x\<le>y then content {x .. y} else content {y..x})"
  by (auto simp: content_real)

lemma content_singleton: "content {a} = 0"
  by simp

lemma content_unit[iff]: "content (cbox 0 (One::'a::euclidean_space)) = 1"
  by simp

lemma content_pos_le[intro]: "0 \<le> content (cbox a b)"
  by simp

corollary content_nonneg [simp]: "~ content (cbox a b) < 0"
  using not_le by blast

lemma content_pos_lt: "\<forall>i\<in>Basis. a\<bullet>i < b\<bullet>i \<Longrightarrow> 0 < content (cbox a b)"
  by (auto simp: less_imp_le inner_diff box_eq_empty intro!: setprod_pos)

lemma content_eq_0: "content (cbox a b) = 0 \<longleftrightarrow> (\<exists>i\<in>Basis. b\<bullet>i \<le> a\<bullet>i)"
  by (auto simp: content_cbox_cases not_le intro: less_imp_le antisym eq_refl)

lemma content_eq_0_interior: "content (cbox a b) = 0 \<longleftrightarrow> interior(cbox a b) = {}"
  unfolding content_eq_0 interior_cbox box_eq_empty by auto

lemma content_pos_lt_eq: "0 < content (cbox a (b::'a::euclidean_space)) \<longleftrightarrow> (\<forall>i\<in>Basis. a\<bullet>i < b\<bullet>i)"
  by (auto simp add: content_cbox_cases less_le setprod_nonneg)

lemma content_empty [simp]: "content {} = 0"
  by simp

lemma content_real_if [simp]: "content {a..b} = (if a \<le> b then b - a else 0)"
  by (simp add: content_real)

lemma content_subset: "cbox a b \<subseteq> cbox c d \<Longrightarrow> content (cbox a b) \<le> content (cbox c d)"
  unfolding measure_def
  by (intro enn2real_mono emeasure_mono) (auto simp: emeasure_lborel_cbox_eq)

lemma content_lt_nz: "0 < content (cbox a b) \<longleftrightarrow> content (cbox a b) \<noteq> 0"
  unfolding content_pos_lt_eq content_eq_0 unfolding not_ex not_le by fastforce

lemma content_Pair: "content (cbox (a,c) (b,d)) = content (cbox a b) * content (cbox c d)"
  unfolding measure_lborel_cbox_eq Basis_prod_def
  apply (subst setprod.union_disjoint)
  apply (auto simp: bex_Un ball_Un)
  apply (subst (1 2) setprod.reindex_nontrivial)
  apply auto
  done

lemma content_cbox_pair_eq0_D:
   "content (cbox (a,c) (b,d)) = 0 \<Longrightarrow> content (cbox a b) = 0 \<or> content (cbox c d) = 0"
  by (simp add: content_Pair)

lemma content_0_subset: "content(cbox a b) = 0 \<Longrightarrow> s \<subseteq> cbox a b \<Longrightarrow> content s = 0"
  using emeasure_mono[of s "cbox a b" lborel]
  by (auto simp: measure_def enn2real_eq_0_iff emeasure_lborel_cbox_eq)

lemma content_split:
  fixes a :: "'a::euclidean_space"
  assumes "k \<in> Basis"
  shows "content (cbox a b) = content(cbox a b \<inter> {x. x\<bullet>k \<le> c}) + content(cbox a b \<inter> {x. x\<bullet>k \<ge> c})"
  -- \<open>Prove using measure theory\<close>
proof cases
  note simps = interval_split[OF assms] content_cbox_cases
  have *: "Basis = insert k (Basis - {k})" "\<And>x. finite (Basis-{x})" "\<And>x. x\<notin>Basis-{x}"
    using assms by auto
  have *: "\<And>X Y Z. (\<Prod>i\<in>Basis. Z i (if i = k then X else Y i)) = Z k X * (\<Prod>i\<in>Basis-{k}. Z i (Y i))"
    "(\<Prod>i\<in>Basis. b\<bullet>i - a\<bullet>i) = (\<Prod>i\<in>Basis-{k}. b\<bullet>i - a\<bullet>i) * (b\<bullet>k - a\<bullet>k)"
    apply (subst *(1))
    defer
    apply (subst *(1))
    unfolding setprod.insert[OF *(2-)]
    apply auto
    done
  assume as: "\<forall>i\<in>Basis. a \<bullet> i \<le> b \<bullet> i"
  moreover
  have "\<And>x. min (b \<bullet> k) c = max (a \<bullet> k) c \<Longrightarrow>
    x * (b\<bullet>k - a\<bullet>k) = x * (max (a \<bullet> k) c - a \<bullet> k) + x * (b \<bullet> k - max (a \<bullet> k) c)"
    by  (auto simp add: field_simps)
  moreover
  have **: "(\<Prod>i\<in>Basis. ((\<Sum>i\<in>Basis. (if i = k then min (b \<bullet> k) c else b \<bullet> i) *\<^sub>R i) \<bullet> i - a \<bullet> i)) =
      (\<Prod>i\<in>Basis. (if i = k then min (b \<bullet> k) c else b \<bullet> i) - a \<bullet> i)"
    "(\<Prod>i\<in>Basis. b \<bullet> i - ((\<Sum>i\<in>Basis. (if i = k then max (a \<bullet> k) c else a \<bullet> i) *\<^sub>R i) \<bullet> i)) =
      (\<Prod>i\<in>Basis. b \<bullet> i - (if i = k then max (a \<bullet> k) c else a \<bullet> i))"
    by (auto intro!: setprod.cong)
  have "\<not> a \<bullet> k \<le> c \<Longrightarrow> \<not> c \<le> b \<bullet> k \<Longrightarrow> False"
    unfolding not_le
    using as[unfolded ,rule_format,of k] assms
    by auto
  ultimately show ?thesis
    using assms
    unfolding simps **
    unfolding *(1)[of "\<lambda>i x. b\<bullet>i - x"] *(1)[of "\<lambda>i x. x - a\<bullet>i"]
    unfolding *(2)
    by auto
next
  assume "\<not> (\<forall>i\<in>Basis. a \<bullet> i \<le> b \<bullet> i)"
  then have "cbox a b = {}"
    unfolding box_eq_empty by (auto simp: not_le)
  then show ?thesis
    by (auto simp: not_le)
qed

subsection \<open>The notion of a gauge --- simply an open set containing the point.\<close>

definition "gauge d \<longleftrightarrow> (\<forall>x. x \<in> d x \<and> open (d x))"

lemma gaugeI:
  assumes "\<And>x. x \<in> g x"
    and "\<And>x. open (g x)"
  shows "gauge g"
  using assms unfolding gauge_def by auto

lemma gaugeD[dest]:
  assumes "gauge d"
  shows "x \<in> d x"
    and "open (d x)"
  using assms unfolding gauge_def by auto

lemma gauge_ball_dependent: "\<forall>x. 0 < e x \<Longrightarrow> gauge (\<lambda>x. ball x (e x))"
  unfolding gauge_def by auto

lemma gauge_ball[intro]: "0 < e \<Longrightarrow> gauge (\<lambda>x. ball x e)"
  unfolding gauge_def by auto

lemma gauge_trivial[intro!]: "gauge (\<lambda>x. ball x 1)"
  by (rule gauge_ball) auto

lemma gauge_inter[intro]: "gauge d1 \<Longrightarrow> gauge d2 \<Longrightarrow> gauge (\<lambda>x. d1 x \<inter> d2 x)"
  unfolding gauge_def by auto

lemma gauge_inters:
  assumes "finite s"
    and "\<forall>d\<in>s. gauge (f d)"
  shows "gauge (\<lambda>x. \<Inter>{f d x | d. d \<in> s})"
proof -
  have *: "\<And>x. {f d x |d. d \<in> s} = (\<lambda>d. f d x) ` s"
    by auto
  show ?thesis
    unfolding gauge_def unfolding *
    using assms unfolding Ball_def Inter_iff mem_Collect_eq gauge_def by auto
qed

lemma gauge_existence_lemma:
  "(\<forall>x. \<exists>d :: real. p x \<longrightarrow> 0 < d \<and> q d x) \<longleftrightarrow> (\<forall>x. \<exists>d>0. p x \<longrightarrow> q d x)"
  by (metis zero_less_one)


subsection \<open>Divisions.\<close>

definition division_of (infixl "division'_of" 40)
where
  "s division_of i \<longleftrightarrow>
    finite s \<and>
    (\<forall>k\<in>s. k \<subseteq> i \<and> k \<noteq> {} \<and> (\<exists>a b. k = cbox a b)) \<and>
    (\<forall>k1\<in>s. \<forall>k2\<in>s. k1 \<noteq> k2 \<longrightarrow> interior(k1) \<inter> interior(k2) = {}) \<and>
    (\<Union>s = i)"

lemma division_ofD[dest]:
  assumes "s division_of i"
  shows "finite s"
    and "\<And>k. k \<in> s \<Longrightarrow> k \<subseteq> i"
    and "\<And>k. k \<in> s \<Longrightarrow> k \<noteq> {}"
    and "\<And>k. k \<in> s \<Longrightarrow> \<exists>a b. k = cbox a b"
    and "\<And>k1 k2. k1 \<in> s \<Longrightarrow> k2 \<in> s \<Longrightarrow> k1 \<noteq> k2 \<Longrightarrow> interior(k1) \<inter> interior(k2) = {}"
    and "\<Union>s = i"
  using assms unfolding division_of_def by auto

lemma division_ofI:
  assumes "finite s"
    and "\<And>k. k \<in> s \<Longrightarrow> k \<subseteq> i"
    and "\<And>k. k \<in> s \<Longrightarrow> k \<noteq> {}"
    and "\<And>k. k \<in> s \<Longrightarrow> \<exists>a b. k = cbox a b"
    and "\<And>k1 k2. k1 \<in> s \<Longrightarrow> k2 \<in> s \<Longrightarrow> k1 \<noteq> k2 \<Longrightarrow> interior k1 \<inter> interior k2 = {}"
    and "\<Union>s = i"
  shows "s division_of i"
  using assms unfolding division_of_def by auto

lemma division_of_finite: "s division_of i \<Longrightarrow> finite s"
  unfolding division_of_def by auto

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
  { fix k
    assume "s = {{a}}" "k\<in>s"
    then have "\<exists>x y. k = cbox x y"
      apply (rule_tac x=a in exI)+
      apply (force simp: cbox_sing)
      done
  }
  ultimately show ?l
    unfolding division_of_def cbox_sing by auto
next
  assume ?l
  note * = conjunctD4[OF this[unfolded division_of_def cbox_sing]]
  {
    fix x
    assume x: "x \<in> s" have "x = {a}"
      using *(2)[rule_format,OF x] by auto
  }
  moreover have "s \<noteq> {}"
    using *(4) by auto
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

lemma division_of_content_0:
  assumes "content (cbox a b) = 0" "d division_of (cbox a b)"
  shows "\<forall>k\<in>d. content k = 0"
  unfolding forall_in_division[OF assms(2)]
  by (metis antisym_conv assms content_pos_le content_subset division_ofD(2))

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
      apply (rule set_eqI)
      unfolding * and UN_iff
      using division_ofD(6)[OF assms(1)] and division_ofD(6)[OF assms(2)]
      apply auto
      done
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
        unfolding k k1 k2 unfolding inter_interval by auto
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

lemma elementary_inter:
  fixes s t :: "'a::euclidean_space set"
  assumes "p1 division_of s"
    and "p2 division_of t"
  shows "\<exists>p. p division_of (s \<inter> t)"
using assms division_inter by blast

lemma elementary_inters:
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
      by (simp add: elementary_inter Inter_insert)
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
  {
    fix i :: 'a
    assume "i \<in> Basis"
    with incl nonempty have "a \<bullet> i \<le> c \<bullet> i" "c \<bullet> i \<le> d \<bullet> i" "d \<bullet> i \<le> b \<bullet> i"
      unfolding box_eq_empty subset_box by (auto simp: not_le)
  }
  note ord = this

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
            by (auto simp: PiE_iff extensional_def intro!: ext)
          with \<open>l \<noteq> k\<close> show False
            by (simp add: l k)
        qed
        then obtain i where *: "i \<in> Basis" "f i \<noteq> g i" ..
        then have "f i = (a, c) \<or> f i = (c, d) \<or> f i = (d, b)"
                  "g i = (a, c) \<or> g i = (c, d) \<or> g i = (d, b)"
          using f g by (auto simp: PiE_iff)
        with * ord[of i] show "interior l \<inter> interior k = {}"
          by (auto simp add: l k interior_cbox disjoint_interval intro!: bexI[of _ i])
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

lemma partial_division_extend_interval:
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
  { fix x
    assume x: "x \<in> p"
    have "q x division_of \<Union>q x"
      apply (rule division_ofI)
      using division_ofD[OF q(1)[OF x]]
      apply auto
      done }
  then have "\<And>x. x \<in> p \<Longrightarrow> \<exists>d. d division_of \<Union>(q x - {x})"
    by (meson Diff_subset division_of_subset)
  then have "\<exists>d. d division_of \<Inter>((\<lambda>i. \<Union>(q i - {i})) ` p)"
    apply -
    apply (rule elementary_inters [OF finite_imageI[OF p(1)]])
    apply (auto simp: False elementary_inters [OF finite_imageI[OF p(1)]])
    done
  then obtain d where d: "d division_of \<Inter>((\<lambda>i. \<Union>(q i - {i})) ` p)" ..
  have "d \<union> p division_of cbox a b"
  proof -
    have te: "\<And>s f t. s \<noteq> {} \<Longrightarrow> \<forall>i\<in>s. f i \<union> i = t \<Longrightarrow> t = \<Inter>(f ` s) \<union> \<Union>s" by auto
    have cbox_eq: "cbox a b = \<Inter>((\<lambda>i. \<Union>(q i - {i})) ` p) \<union> \<Union>p"
    proof (rule te[OF False], clarify)
      fix i
      assume i: "i \<in> p"
      show "\<Union>(q i - {i}) \<union> i = cbox a b"
        using division_ofD(6)[OF q(1)[OF i]] using q(2)[OF i] by auto
    qed
    { fix k
      assume k: "k \<in> p"
      have *: "\<And>u t s. t \<inter> s = {} \<Longrightarrow> u \<subseteq> s \<Longrightarrow> u \<inter> t = {}"
        by auto
      have "interior (\<Inter>i\<in>p. \<Union>(q i - {i})) \<inter> interior k = {}"
      proof (rule *[OF inter_interior_unions_intervals])
        note qk=division_ofD[OF q(1)[OF k]]
        show "finite (q k - {k})" "open (interior k)" "\<forall>t\<in>q k - {k}. \<exists>a b. t = cbox a b"
          using qk by auto
        show "\<forall>t\<in>q k - {k}. interior k \<inter> interior t = {}"
          using qk(5) using q(2)[OF k] by auto
        show "interior (\<Inter>i\<in>p. \<Union>(q i - {i})) \<subseteq> interior (\<Union>(q k - {k}))"
          apply (rule interior_mono)+
          using k
          apply auto
          done
      qed } note [simp] = this
    show "d \<union> p division_of (cbox a b)"
      unfolding cbox_eq
      apply (rule division_disjoint_union[OF d assms(1)])
      apply (rule inter_interior_unions_intervals)
      apply (rule p open_interior ballI)+
      apply simp_all
      done
  qed
  then show ?thesis
    by (meson Un_upper2 that)
qed

lemma elementary_bounded[dest]:
  fixes s :: "'a::euclidean_space set"
  shows "p division_of s \<Longrightarrow> bounded s"
  unfolding division_of_def by (metis bounded_Union bounded_cbox)

lemma elementary_subset_cbox:
  "p division_of s \<Longrightarrow> \<exists>a b. s \<subseteq> cbox a (b::'a::euclidean_space)"
  by (meson elementary_bounded bounded_subset_cbox)

lemma division_union_intervals_exists:
  fixes a b :: "'a::euclidean_space"
  assumes "cbox a b \<noteq> {}"
  obtains p where "(insert (cbox a b) p) division_of (cbox a b \<union> cbox c d)"
proof (cases "cbox c d = {}")
  case True
  show ?thesis
    apply (rule that[of "{}"])
    unfolding True
    using assms
    apply auto
    done
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
      unfolding inter_interval by auto
    have uv_sub: "cbox u v \<subseteq> cbox c d" using uv by auto
    obtain p where "p division_of cbox c d" "cbox u v \<in> p"
      by (rule partial_division_extend_1[OF uv_sub False[unfolded uv]])
    note p = this division_ofD[OF this(1)]
    have "interior (cbox a b \<inter> \<Union>(p - {cbox u v})) = interior(cbox u v \<inter> \<Union>(p - {cbox u v}))"
      apply (rule arg_cong[of _ _ interior])
      using p(8) uv by auto
    also have "\<dots> = {}"
      unfolding interior_Int
      apply (rule inter_interior_unions_intervals)
      using p(6) p(7)[OF p(2)] p(3)
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

lemma division_of_unions:
  assumes "finite f"
    and "\<And>p. p \<in> f \<Longrightarrow> p division_of (\<Union>p)"
    and "\<And>k1 k2. k1 \<in> \<Union>f \<Longrightarrow> k2 \<in> \<Union>f \<Longrightarrow> k1 \<noteq> k2 \<Longrightarrow> interior k1 \<inter> interior k2 = {}"
  shows "\<Union>f division_of \<Union>\<Union>f"
  using assms
  by (auto intro!: division_ofI)

lemma elementary_union_interval:
  fixes a b :: "'a::euclidean_space"
  assumes "p division_of \<Union>p"
  obtains q where "q division_of (cbox a b \<union> \<Union>p)"
proof -
  note assm = division_ofD[OF assms]
  have lem1: "\<And>f s. \<Union>\<Union>(f ` s) = \<Union>((\<lambda>x. \<Union>(f x)) ` s)"
    by auto
  have lem2: "\<And>f s. f \<noteq> {} \<Longrightarrow> \<Union>{s \<union> t |t. t \<in> f} = s \<union> \<Union>f"
    by auto
  {
    presume "p = {} \<Longrightarrow> thesis"
      "cbox a b = {} \<Longrightarrow> thesis"
      "cbox a b \<noteq> {} \<Longrightarrow> interior (cbox a b) = {} \<Longrightarrow> thesis"
      "p \<noteq> {} \<Longrightarrow> interior (cbox a b)\<noteq>{} \<Longrightarrow> cbox a b \<noteq> {} \<Longrightarrow> thesis"
    then show thesis by auto
  next
    assume as: "p = {}"
    obtain p where "p division_of (cbox a b)"
      by (rule elementary_interval)
    then show thesis
      using as that by auto
  next
    assume as: "cbox a b = {}"
    show thesis
      using as assms that by auto
  next
    assume as: "interior (cbox a b) = {}" "cbox a b \<noteq> {}"
    show thesis
      apply (rule that[of "insert (cbox a b) p"],rule division_ofI)
      unfolding finite_insert
      apply (rule assm(1)) unfolding Union_insert
      using assm(2-4) as
      apply -
      apply (fast dest: assm(5))+
      done
  next
    assume as: "p \<noteq> {}" "interior (cbox a b) \<noteq> {}" "cbox a b \<noteq> {}"
    have "\<forall>k\<in>p. \<exists>q. (insert (cbox a b) q) division_of (cbox a b \<union> k)"
    proof
      fix k
      assume kp: "k \<in> p"
      from assm(4)[OF kp] obtain c d where "k = cbox c d" by blast
      then show "\<exists>q. (insert (cbox a b) q) division_of (cbox a b \<union> k)"
        by (meson as(3) division_union_intervals_exists)
    qed
    from bchoice[OF this] obtain q where "\<forall>x\<in>p. insert (cbox a b) (q x) division_of (cbox a b) \<union> x" ..
    note q = division_ofD[OF this[rule_format]]
    let ?D = "\<Union>{insert (cbox a b) (q k) | k. k \<in> p}"
    show thesis
    proof (rule that[OF division_ofI])
      have *: "{insert (cbox a b) (q k) |k. k \<in> p} = (\<lambda>k. insert (cbox a b) (q k)) ` p"
        by auto
      show "finite ?D"
        using "*" assm(1) q(1) by auto
      show "\<Union>?D = cbox a b \<union> \<Union>p"
        unfolding * lem1
        unfolding lem2[OF as(1), of "cbox a b", symmetric]
        using q(6)
        by auto
      fix k
      assume k: "k \<in> ?D"
      then show "k \<subseteq> cbox a b \<union> \<Union>p"
        using q(2) by auto
      show "k \<noteq> {}"
        using q(3) k by auto
      show "\<exists>a b. k = cbox a b"
        using q(4) k by auto
      fix k'
      assume k': "k' \<in> ?D" "k \<noteq> k'"
      obtain x where x: "k \<in> insert (cbox a b) (q x)" "x\<in>p"
        using k by auto
      obtain x' where x': "k'\<in>insert (cbox a b) (q x')" "x'\<in>p"
        using k' by auto
      show "interior k \<inter> interior k' = {}"
      proof (cases "x = x'")
        case True
        show ?thesis
          using True k' q(5) x' x by auto
      next
        case False
        {
          presume "k = cbox a b \<Longrightarrow> ?thesis"
            and "k' = cbox a b \<Longrightarrow> ?thesis"
            and "k \<noteq> cbox a b \<Longrightarrow> k' \<noteq> cbox a b \<Longrightarrow> ?thesis"
          then show ?thesis by linarith
        next
          assume as': "k  = cbox a b"
          show ?thesis
            using as' k' q(5) x' by blast
        next
          assume as': "k' = cbox a b"
          show ?thesis
            using as' k'(2) q(5) x by blast
        }
        assume as': "k \<noteq> cbox a b" "k' \<noteq> cbox a b"
        obtain c d where k: "k = cbox c d"
          using q(4)[OF x(2,1)] by blast
        have "interior k \<inter> interior (cbox a b) = {}"
          using as' k'(2) q(5) x by blast
        then have "interior k \<subseteq> interior x"
        using interior_subset_union_intervals
          by (metis as(2) k q(2) x interior_subset_union_intervals)
        moreover
        obtain c d where c_d: "k' = cbox c d"
          using q(4)[OF x'(2,1)] by blast
        have "interior k' \<inter> interior (cbox a b) = {}"
          using as'(2) q(5) x' by blast
        then have "interior k' \<subseteq> interior x'"
          by (metis as(2) c_d interior_subset_union_intervals q(2) x'(1) x'(2))
        ultimately show ?thesis
          using assm(5)[OF x(2) x'(2) False] by auto
      qed
    qed
  }
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
    show "\<exists>p. p division_of \<Union>insert x F"
      using elementary_union_interval[OF p[unfolded *], of a b]
      unfolding Union_insert x * by metis
  qed (insert assms, auto)
  then show ?thesis
    using that by auto
qed

lemma elementary_union:
  fixes s t :: "'a::euclidean_space set"
  assumes "ps division_of s" "pt division_of t"
  obtains p where "p division_of (s \<union> t)"
proof -
  have *: "s \<union> t = \<Union>ps \<union> \<Union>pt"
    using assms unfolding division_of_def by auto
  show ?thesis
    apply (rule elementary_unions_intervals[of "ps \<union> pt"])
    using assms apply auto
    by (simp add: * that)
qed

lemma partial_division_extend:
  fixes t :: "'a::euclidean_space set"
  assumes "p division_of s"
    and "q division_of t"
    and "s \<subseteq> t"
  obtains r where "p \<subseteq> r" and "r division_of t"
proof -
  note divp = division_ofD[OF assms(1)] and divq = division_ofD[OF assms(2)]
  obtain a b where ab: "t \<subseteq> cbox a b"
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
    by (metis assms(2) divq(6) elementary_inter)
  {
    fix x
    assume x: "x \<in> t" "x \<notin> s"
    then have "x\<in>\<Union>r1"
      unfolding r1 using ab by auto
    then obtain r where r: "r \<in> r1" "x \<in> r"
      unfolding Union_iff ..
    moreover
    have "r \<notin> p"
    proof
      assume "r \<in> p"
      then have "x \<in> s" using divp(2) r by auto
      then show False using x by auto
    qed
    ultimately have "x\<in>\<Union>(r1 - p)" by auto
  }
  then have *: "t = \<Union>p \<union> (\<Union>(r1 - p) \<inter> \<Union>q)"
    unfolding divp divq using assms(3) by auto
  show ?thesis
    apply (rule that[of "p \<union> r2"])
    unfolding *
    defer
    apply (rule division_disjoint_union)
    unfolding divp(6)
    apply(rule assms r2)+
  proof -
    have "interior s \<inter> interior (\<Union>(r1-p)) = {}"
    proof (rule inter_interior_unions_intervals)
      show "finite (r1 - p)" and "open (interior s)" and "\<forall>t\<in>r1-p. \<exists>a b. t = cbox a b"
        using r1 by auto
      have *: "\<And>s. (\<And>x. x \<in> s \<Longrightarrow> False) \<Longrightarrow> s = {}"
        by auto
      show "\<forall>t\<in>r1-p. interior s \<inter> interior t = {}"
      proof
        fix m x
        assume as: "m \<in> r1 - p"
        have "interior m \<inter> interior (\<Union>p) = {}"
        proof (rule inter_interior_unions_intervals)
          show "finite p" and "open (interior m)" and "\<forall>t\<in>p. \<exists>a b. t = cbox a b"
            using divp by auto
          show "\<forall>t\<in>p. interior m \<inter> interior t = {}"
            by (metis DiffD1 DiffD2 as r1(1) r1(7) set_rev_mp)
        qed
        then show "interior s \<inter> interior m = {}"
          unfolding divp by auto
      qed
    qed
    then show "interior s \<inter> interior (\<Union>(r1-p) \<inter> (\<Union>q)) = {}"
      using interior_subset by auto
  qed auto
qed

lemma division_split_left_inj:
  fixes type :: "'a::euclidean_space"
  assumes "d division_of i"
    and "k1 \<in> d"
    and "k2 \<in> d"
    and "k1 \<noteq> k2"
    and "k1 \<inter> {x::'a. x\<bullet>k \<le> c} = k2 \<inter> {x. x\<bullet>k \<le> c}"
    and k: "k\<in>Basis"
  shows "content(k1 \<inter> {x. x\<bullet>k \<le> c}) = 0"
proof -
  note d=division_ofD[OF assms(1)]
  have *: "\<And>(a::'a) b c. content (cbox a b \<inter> {x. x\<bullet>k \<le> c}) = 0 \<longleftrightarrow>
    interior(cbox a b \<inter> {x. x\<bullet>k \<le> c}) = {}"
    unfolding  interval_split[OF k] content_eq_0_interior by auto
  guess u1 v1 using d(4)[OF assms(2)] by (elim exE) note uv1=this
  guess u2 v2 using d(4)[OF assms(3)] by (elim exE) note uv2=this
  have **: "\<And>s t u. s \<inter> t = {} \<Longrightarrow> u \<subseteq> s \<Longrightarrow> u \<subseteq> t \<Longrightarrow> u = {}"
    by auto
  show ?thesis
    unfolding uv1 uv2 *
    apply (rule **[OF d(5)[OF assms(2-4)]])
    apply (simp add: uv1)
    using assms(5) uv1 by auto
qed

lemma division_split_right_inj:
  fixes type :: "'a::euclidean_space"
  assumes "d division_of i"
    and "k1 \<in> d"
    and "k2 \<in> d"
    and "k1 \<noteq> k2"
    and "k1 \<inter> {x::'a. x\<bullet>k \<ge> c} = k2 \<inter> {x. x\<bullet>k \<ge> c}"
    and k: "k \<in> Basis"
  shows "content (k1 \<inter> {x. x\<bullet>k \<ge> c}) = 0"
proof -
  note d=division_ofD[OF assms(1)]
  have *: "\<And>a b::'a. \<And>c. content(cbox a b \<inter> {x. x\<bullet>k \<ge> c}) = 0 \<longleftrightarrow>
    interior(cbox a b \<inter> {x. x\<bullet>k \<ge> c}) = {}"
    unfolding interval_split[OF k] content_eq_0_interior by auto
  guess u1 v1 using d(4)[OF assms(2)] by (elim exE) note uv1=this
  guess u2 v2 using d(4)[OF assms(3)] by (elim exE) note uv2=this
  have **: "\<And>s t u. s \<inter> t = {} \<Longrightarrow> u \<subseteq> s \<Longrightarrow> u \<subseteq> t \<Longrightarrow> u = {}"
    by auto
  show ?thesis
    unfolding uv1 uv2 *
    apply (rule **[OF d(5)[OF assms(2-4)]])
    apply (simp add: uv1)
    using assms(5) uv1 by auto
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
    fix k
    assume "k \<in> ?p1"
    then guess l unfolding mem_Collect_eq by (elim exE conjE) note l=this
    guess u v using p(4)[OF l(2)] by (elim exE) note uv=this
    show "k \<subseteq> ?I1"
      using l p(2) uv by force
    show  "k \<noteq> {}"
      by (simp add: l)
    show  "\<exists>a b. k = cbox a b"
      apply (simp add: l uv p(2-3)[OF l(2)])
      apply (subst interval_split[OF k])
      apply (auto intro: order.trans)
      done
    fix k'
    assume "k' \<in> ?p1"
    then guess l' unfolding mem_Collect_eq by (elim exE conjE) note l'=this
    assume "k \<noteq> k'"
    then show "interior k \<inter> interior k' = {}"
      unfolding l l' using p(5)[OF l(2) l'(2)] by auto
  }
  {
    fix k
    assume "k \<in> ?p2"
    then guess l unfolding mem_Collect_eq by (elim exE conjE) note l=this
    guess u v using p(4)[OF l(2)] by (elim exE) note uv=this
    show "k \<subseteq> ?I2"
      using l p(2) uv by force
    show  "k \<noteq> {}"
      by (simp add: l)
    show  "\<exists>a b. k = cbox a b"
      apply (simp add: l uv p(2-3)[OF l(2)])
      apply (subst interval_split[OF k])
      apply (auto intro: order.trans)
      done
    fix k'
    assume "k' \<in> ?p2"
    then guess l' unfolding mem_Collect_eq by (elim exE conjE) note l'=this
    assume "k \<noteq> k'"
    then show "interior k \<inter> interior k' = {}"
      unfolding l l' using p(5)[OF l(2) l'(2)] by auto
  }
qed

subsection \<open>Tagged (partial) divisions.\<close>

definition tagged_partial_division_of (infixr "tagged'_partial'_division'_of" 40)
  where "s tagged_partial_division_of i \<longleftrightarrow>
    finite s \<and>
    (\<forall>x k. (x, k) \<in> s \<longrightarrow> x \<in> k \<and> k \<subseteq> i \<and> (\<exists>a b. k = cbox a b)) \<and>
    (\<forall>x1 k1 x2 k2. (x1, k1) \<in> s \<and> (x2, k2) \<in> s \<and> (x1, k1) \<noteq> (x2, k2) \<longrightarrow>
      interior k1 \<inter> interior k2 = {})"

lemma tagged_partial_division_ofD[dest]:
  assumes "s tagged_partial_division_of i"
  shows "finite s"
    and "\<And>x k. (x,k) \<in> s \<Longrightarrow> x \<in> k"
    and "\<And>x k. (x,k) \<in> s \<Longrightarrow> k \<subseteq> i"
    and "\<And>x k. (x,k) \<in> s \<Longrightarrow> \<exists>a b. k = cbox a b"
    and "\<And>x1 k1 x2 k2. (x1,k1) \<in> s \<Longrightarrow>
      (x2, k2) \<in> s \<Longrightarrow> (x1, k1) \<noteq> (x2, k2) \<Longrightarrow> interior k1 \<inter> interior k2 = {}"
  using assms unfolding tagged_partial_division_of_def by blast+

definition tagged_division_of (infixr "tagged'_division'_of" 40)
  where "s tagged_division_of i \<longleftrightarrow> s tagged_partial_division_of i \<and> (\<Union>{k. \<exists>x. (x,k) \<in> s} = i)"

lemma tagged_division_of_finite: "s tagged_division_of i \<Longrightarrow> finite s"
  unfolding tagged_division_of_def tagged_partial_division_of_def by auto

lemma tagged_division_of:
  "s tagged_division_of i \<longleftrightarrow>
    finite s \<and>
    (\<forall>x k. (x, k) \<in> s \<longrightarrow> x \<in> k \<and> k \<subseteq> i \<and> (\<exists>a b. k = cbox a b)) \<and>
    (\<forall>x1 k1 x2 k2. (x1, k1) \<in> s \<and> (x2, k2) \<in> s \<and> (x1, k1) \<noteq> (x2, k2) \<longrightarrow>
      interior k1 \<inter> interior k2 = {}) \<and>
    (\<Union>{k. \<exists>x. (x,k) \<in> s} = i)"
  unfolding tagged_division_of_def tagged_partial_division_of_def by auto

lemma tagged_division_ofI:
  assumes "finite s"
    and "\<And>x k. (x,k) \<in> s \<Longrightarrow> x \<in> k"
    and "\<And>x k. (x,k) \<in> s \<Longrightarrow> k \<subseteq> i"
    and "\<And>x k. (x,k) \<in> s \<Longrightarrow> \<exists>a b. k = cbox a b"
    and "\<And>x1 k1 x2 k2. (x1,k1) \<in> s \<Longrightarrow> (x2, k2) \<in> s \<Longrightarrow> (x1, k1) \<noteq> (x2, k2) \<Longrightarrow>
      interior k1 \<inter> interior k2 = {}"
    and "(\<Union>{k. \<exists>x. (x,k) \<in> s} = i)"
  shows "s tagged_division_of i"
  unfolding tagged_division_of
  using assms
  apply auto
  apply fastforce+
  done

lemma tagged_division_ofD[dest]:  (*FIXME USE A LOCALE*)
  assumes "s tagged_division_of i"
  shows "finite s"
    and "\<And>x k. (x,k) \<in> s \<Longrightarrow> x \<in> k"
    and "\<And>x k. (x,k) \<in> s \<Longrightarrow> k \<subseteq> i"
    and "\<And>x k. (x,k) \<in> s \<Longrightarrow> \<exists>a b. k = cbox a b"
    and "\<And>x1 k1 x2 k2. (x1, k1) \<in> s \<Longrightarrow> (x2, k2) \<in> s \<Longrightarrow> (x1, k1) \<noteq> (x2, k2) \<Longrightarrow>
      interior k1 \<inter> interior k2 = {}"
    and "(\<Union>{k. \<exists>x. (x,k) \<in> s} = i)"
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
  using assms
  unfolding tagged_partial_division_of_def
  using finite_subset[OF assms(2)]
  by blast

lemma (in comm_monoid_set) over_tagged_division_lemma:
  assumes "p tagged_division_of i"
    and "\<And>u v. cbox u v \<noteq> {} \<Longrightarrow> content (cbox u v) = 0 \<Longrightarrow> d (cbox u v) = \<^bold>1"
  shows "F (\<lambda>(x,k). d k) p = F d (snd ` p)"
proof -
  have *: "(\<lambda>(x,k). d k) = d \<circ> snd"
    unfolding o_def by (rule ext) auto
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
      by (metis prod.collapse \<open>x\<in>p\<close> \<open>snd x = snd y\<close> \<open>x \<noteq> y\<close>)+
    with \<open>x\<in>p\<close> \<open>y\<in>p\<close> have "interior (snd x) \<inter> interior (snd y) = {}"
      by (intro assm(5)[of "fst x" _ "fst y"]) auto
    then have "content (cbox a b) = 0"
      unfolding \<open>snd x = snd y\<close>[symmetric] ab content_eq_0_interior by auto
    then have "d (cbox a b) = \<^bold>1"
      using assm(2)[of "fst x" "snd x"] \<open>x\<in>p\<close> ab[symmetric] by (intro assms(2)) auto
    then show "d (snd x) = \<^bold>1"
      unfolding ab by auto
  qed
qed

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

lemma tagged_division_union:
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

lemma tagged_division_unions:
  assumes "finite iset"
    and "\<forall>i\<in>iset. pfn i tagged_division_of i"
    and "\<forall>i1\<in>iset. \<forall>i2\<in>iset. i1 \<noteq> i2 \<longrightarrow> interior(i1) \<inter> interior(i2) = {}"
  shows "\<Union>(pfn ` iset) tagged_division_of (\<Union>iset)"
proof (rule tagged_division_ofI)
  note assm = tagged_division_ofD[OF assms(2)[rule_format]]
  show "finite (\<Union>(pfn ` iset))"
    using assms by auto
  have "\<Union>{k. \<exists>x. (x, k) \<in> \<Union>(pfn ` iset)} = \<Union>((\<lambda>i. \<Union>{k. \<exists>x. (x, k) \<in> pfn i}) ` iset)"
    by blast
  also have "\<dots> = \<Union>iset"
    using assm(6) by auto
  finally show "\<Union>{k. \<exists>x. (x, k) \<in> \<Union>(pfn ` iset)} = \<Union>iset" .
  fix x k
  assume xk: "(x, k) \<in> \<Union>(pfn ` iset)"
  then obtain i where i: "i \<in> iset" "(x, k) \<in> pfn i"
    by auto
  show "x \<in> k" "\<exists>a b. k = cbox a b" "k \<subseteq> \<Union>iset"
    using assm(2-4)[OF i] using i(1) by auto
  fix x' k'
  assume xk': "(x', k') \<in> \<Union>(pfn ` iset)" "(x, k) \<noteq> (x', k')"
  then obtain i' where i': "i' \<in> iset" "(x', k') \<in> pfn i'"
    by auto
  have *: "\<And>a b. i \<noteq> i' \<Longrightarrow> a \<subseteq> i \<Longrightarrow> b \<subseteq> i' \<Longrightarrow> interior a \<inter> interior b = {}"
    using i(1) i'(1)
    using assms(3)[rule_format] interior_mono
    by blast
  show "interior k \<inter> interior k' = {}"
    apply (cases "i = i'")
    using assm(5) i' i(2) xk'(2) apply blast
    using "*" assm(3) i' i by auto
qed

lemma tagged_partial_division_of_union_self:
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

subsection \<open>Functions closed on boxes: morphisms from boxes to monoids\<close>

text \<open>This auxiliary structure is used to sum up over the elements of a division. Main theorem is
  @{text operative_division}. Instances for the monoid are @{typ "'a option"}, @{typ real}, and
  @{typ bool}.\<close>

lemma property_empty_interval: "\<forall>a b. content (cbox a b) = 0 \<longrightarrow> P (cbox a b) \<Longrightarrow> P {}"
  using content_empty unfolding empty_as_interval by auto

paragraph \<open>Using additivity of lifted function to encode definedness.\<close>

definition lift_option :: "('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> 'a option \<Rightarrow> 'b option \<Rightarrow> 'c option"
where
  "lift_option f a' b' = Option.bind a' (\<lambda>a. Option.bind b' (\<lambda>b. Some (f a b)))"

lemma lift_option_simps[simp]:
  "lift_option f (Some a) (Some b) = Some (f a b)"
  "lift_option f None b' = None"
  "lift_option f a' None = None"
  by (auto simp: lift_option_def)

lemma comm_monoid_lift_option:
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

paragraph \<open>Operative\<close>

definition (in comm_monoid) operative :: "('b::euclidean_space set \<Rightarrow> 'a) \<Rightarrow> bool"
  where "operative g \<longleftrightarrow>
    (\<forall>a b. content (cbox a b) = 0 \<longrightarrow> g (cbox a b) = \<^bold>1) \<and>
    (\<forall>a b c. \<forall>k\<in>Basis. g (cbox a b) = g (cbox a b \<inter> {x. x\<bullet>k \<le> c}) \<^bold>* g (cbox a b \<inter> {x. x\<bullet>k \<ge> c}))"

lemma (in comm_monoid) operativeD[dest]:
  assumes "operative g"
  shows "\<And>a b. content (cbox a b) = 0 \<Longrightarrow> g (cbox a b) = \<^bold>1"
    and "\<And>a b c k. k \<in> Basis \<Longrightarrow> g (cbox a b) = g (cbox a b \<inter> {x. x\<bullet>k \<le> c}) \<^bold>* g (cbox a b \<inter> {x. x\<bullet>k \<ge> c})"
  using assms unfolding operative_def by auto

lemma (in comm_monoid) operative_empty: "operative g \<Longrightarrow> g {} = \<^bold>1"
  unfolding operative_def by (rule property_empty_interval) auto

lemma operative_content[intro]: "add.operative content"
  by (force simp add: add.operative_def content_split[symmetric])

definition "division_points (k::('a::euclidean_space) set) d =
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
    and "division_points (cbox a b \<inter> {x. x\<bullet>k \<ge> c}) {l \<inter> {x. x\<bullet>k \<ge> c} | l . l \<in> d \<and> ~(l \<inter> {x. x\<bullet>k \<ge> c} = {})} \<subseteq>
      division_points (cbox a b) d" (is ?t2)
proof -
  note assm = division_ofD[OF assms(1)]
  have *: "\<forall>i\<in>Basis. a\<bullet>i \<le> b\<bullet>i"
    "\<forall>i\<in>Basis. a\<bullet>i \<le> (\<Sum>i\<in>Basis. (if i = k then min (b \<bullet> k) c else  b \<bullet> i) *\<^sub>R i) \<bullet> i"
    "\<forall>i\<in>Basis. (\<Sum>i\<in>Basis. (if i = k then max (a \<bullet> k) c else a \<bullet> i) *\<^sub>R i) \<bullet> i \<le> b\<bullet>i"
    "min (b \<bullet> k) c = c" "max (a \<bullet> k) c = c"
    using assms using less_imp_le by auto
  show ?t1 (*FIXME a horrible mess*)
    unfolding division_points_def interval_split[OF k, of a b]
    unfolding interval_bounds[OF *(1)] interval_bounds[OF *(2)] interval_bounds[OF *(3)]
    unfolding *
    apply (rule subsetI)
    unfolding mem_Collect_eq split_beta
    apply (erule bexE conjE)+
    apply (simp add: )
    apply (erule exE conjE)+
  proof
    fix i l x
    assume as:
      "a \<bullet> fst x < snd x" "snd x < (if fst x = k then c else b \<bullet> fst x)"
      "interval_lowerbound i \<bullet> fst x = snd x \<or> interval_upperbound i \<bullet> fst x = snd x"
      "i = l \<inter> {x. x \<bullet> k \<le> c}" "l \<in> d" "l \<inter> {x. x \<bullet> k \<le> c} \<noteq> {}"
      and fstx: "fst x \<in> Basis"
    from assm(4)[OF this(5)] guess u v apply-by(erule exE)+ note l=this
    have *: "\<forall>i\<in>Basis. u \<bullet> i \<le> (\<Sum>i\<in>Basis. (if i = k then min (v \<bullet> k) c else v \<bullet> i) *\<^sub>R i) \<bullet> i"
      using as(6) unfolding l interval_split[OF k] box_ne_empty as .
    have **: "\<forall>i\<in>Basis. u\<bullet>i \<le> v\<bullet>i"
      using l using as(6) unfolding box_ne_empty[symmetric] by auto
    show "\<exists>i\<in>d. interval_lowerbound i \<bullet> fst x = snd x \<or> interval_upperbound i \<bullet> fst x = snd x"
      apply (rule bexI[OF _ \<open>l \<in> d\<close>])
      using as(1-3,5) fstx
      unfolding l interval_bounds[OF **] interval_bounds[OF *] interval_split[OF k] as
      apply (auto split: if_split_asm)
      done
    show "snd x < b \<bullet> fst x"
      using as(2) \<open>c < b\<bullet>k\<close> by (auto split: if_split_asm)
  qed
  show ?t2
    unfolding division_points_def interval_split[OF k, of a b]
    unfolding interval_bounds[OF *(1)] interval_bounds[OF *(2)] interval_bounds[OF *(3)]
    unfolding *
    unfolding subset_eq
    apply rule
    unfolding mem_Collect_eq split_beta
    apply (erule bexE conjE)+
    apply (simp only: mem_Collect_eq inner_setsum_left_Basis simp_thms)
    apply (erule exE conjE)+
  proof
    fix i l x
    assume as:
      "(if fst x = k then c else a \<bullet> fst x) < snd x" "snd x < b \<bullet> fst x"
      "interval_lowerbound i \<bullet> fst x = snd x \<or> interval_upperbound i \<bullet> fst x = snd x"
      "i = l \<inter> {x. c \<le> x \<bullet> k}" "l \<in> d" "l \<inter> {x. c \<le> x \<bullet> k} \<noteq> {}"
      and fstx: "fst x \<in> Basis"
    from assm(4)[OF this(5)] guess u v by (elim exE) note l=this
    have *: "\<forall>i\<in>Basis. (\<Sum>i\<in>Basis. (if i = k then max (u \<bullet> k) c else u \<bullet> i) *\<^sub>R i) \<bullet> i \<le> v \<bullet> i"
      using as(6) unfolding l interval_split[OF k] box_ne_empty as .
    have **: "\<forall>i\<in>Basis. u\<bullet>i \<le> v\<bullet>i"
      using l using as(6) unfolding box_ne_empty[symmetric] by auto
    show "\<exists>i\<in>d. interval_lowerbound i \<bullet> fst x = snd x \<or> interval_upperbound i \<bullet> fst x = snd x"
      apply (rule bexI[OF _ \<open>l \<in> d\<close>])
      using as(1-3,5) fstx
      unfolding l interval_bounds[OF **] interval_bounds[OF *] interval_split[OF k] as
      apply (auto split: if_split_asm)
      done
    show "a \<bullet> fst x < snd x"
      using as(1) \<open>a\<bullet>k < c\<close> by (auto split: if_split_asm)
   qed
qed

lemma division_points_psubset:
  fixes a :: "'a::euclidean_space"
  assumes "d division_of (cbox a b)"
      and "\<forall>i\<in>Basis. a\<bullet>i < b\<bullet>i"  "a\<bullet>k < c" "c < b\<bullet>k"
      and "l \<in> d"
      and "interval_lowerbound l\<bullet>k = c \<or> interval_upperbound l\<bullet>k = c"
      and k: "k \<in> Basis"
  shows "division_points (cbox a b \<inter> {x. x\<bullet>k \<le> c}) {l \<inter> {x. x\<bullet>k \<le> c} | l. l\<in>d \<and> l \<inter> {x. x\<bullet>k \<le> c} \<noteq> {}} \<subset>
         division_points (cbox a b) d" (is "?D1 \<subset> ?D")
    and "division_points (cbox a b \<inter> {x. x\<bullet>k \<ge> c}) {l \<inter> {x. x\<bullet>k \<ge> c} | l. l\<in>d \<and> l \<inter> {x. x\<bullet>k \<ge> c} \<noteq> {}} \<subset>
         division_points (cbox a b) d" (is "?D2 \<subset> ?D")
proof -
  have ab: "\<forall>i\<in>Basis. a\<bullet>i \<le> b\<bullet>i"
    using assms(2) by (auto intro!:less_imp_le)
  guess u v using division_ofD(4)[OF assms(1,5)] by (elim exE) note l=this
  have uv: "\<forall>i\<in>Basis. u\<bullet>i \<le> v\<bullet>i" "\<forall>i\<in>Basis. a\<bullet>i \<le> u\<bullet>i \<and> v\<bullet>i \<le> b\<bullet>i"
    using division_ofD(2,2,3)[OF assms(1,5)] unfolding l box_ne_empty
    using subset_box(1)
    apply auto
    apply blast+
    done
  have *: "interval_upperbound (cbox a b \<inter> {x. x \<bullet> k \<le> interval_upperbound l \<bullet> k}) \<bullet> k = interval_upperbound l \<bullet> k"
          "interval_upperbound (cbox a b \<inter> {x. x \<bullet> k \<le> interval_lowerbound l \<bullet> k}) \<bullet> k = interval_lowerbound l \<bullet> k"
    unfolding l interval_split[OF k] interval_bounds[OF uv(1)]
    using uv[rule_format, of k] ab k
    by auto
  have "\<exists>x. x \<in> ?D - ?D1"
    using assms(3-)
    unfolding division_points_def interval_bounds[OF ab]
    apply -
    apply (erule disjE)
    apply (rule_tac x="(k,(interval_lowerbound l)\<bullet>k)" in exI, force simp add: *)
    apply (rule_tac x="(k,(interval_upperbound l)\<bullet>k)" in exI, force simp add: *)
    done
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
    apply -
    apply (erule disjE)
    apply (rule_tac x="(k,(interval_lowerbound l)\<bullet>k)" in exI, force simp add: *)
    apply (rule_tac x="(k,(interval_upperbound l)\<bullet>k)" in exI, force simp add: *)
    done
  moreover have "?D2 \<subseteq> ?D"
    by (auto simp add: assms division_points_subset)
  ultimately show "?D2 \<subset> ?D"
    by blast
qed

lemma (in comm_monoid_set) operative_division:
  fixes g :: "'b::euclidean_space set \<Rightarrow> 'a"
  assumes g: "operative g" and d: "d division_of (cbox a b)" shows "F g d = g (cbox a b)"
proof -
  define C where [abs_def]: "C = card (division_points (cbox a b) d)"
  then show ?thesis
    using d
  proof (induction C arbitrary: a b d rule: less_induct)
    case (less a b d)
    show ?case
    proof cases
      show "content (cbox a b) = 0 \<Longrightarrow> F g d = g (cbox a b)"
        using division_of_content_0[OF _ less.prems] operativeD(1)[OF  g] division_ofD(4)[OF less.prems]
        by (fastforce intro!: neutral)
    next
      assume "content (cbox a b) \<noteq> 0"
      note ab = this[unfolded content_lt_nz[symmetric] content_pos_lt_eq]
      then have ab': "\<forall>i\<in>Basis. a\<bullet>i \<le> b\<bullet>i"
        by (auto intro!: less_imp_le)
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
          unfolding mem_box using ab by(auto intro!: less_imp_le simp: inner_simps)
        note this[unfolded division_ofD(6)[OF \<open>d division_of cbox a b\<close>,symmetric] Union_iff]
        then guess i .. note i=this
        guess u v using d'[rule_format,OF i(1)] by (elim exE conjE) note uv=this
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
          then guess u v by (elim exE conjE) note uv=this
          have "u \<noteq> a \<or> v \<noteq> b"
            using x[unfolded uv] by auto
          then obtain j where "u\<bullet>j \<noteq> a\<bullet>j \<or> v\<bullet>j \<noteq> b\<bullet>j" and j: "j \<in> Basis"
            unfolding euclidean_eq_iff[where 'a='b] by auto
          then have "u\<bullet>j = v\<bullet>j"
            using uv(2)[rule_format,OF j] by auto
          then have "content (cbox u v) = 0"
            unfolding content_eq_0 using j
            by force
          then show "g x = \<^bold>1"
            unfolding uv(1) by (rule operativeD(1)[OF g])
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
        then guess k c
          unfolding split_paired_Ex division_points_def mem_Collect_eq split_conv
          apply (elim exE conjE)
          done
        note this(2-4,1) note kc=this[unfolded interval_bounds[OF ab']]
        from this(3) guess j .. note j=this
        define d1 where "d1 = {l \<inter> {x. x\<bullet>k \<le> c} | l. l \<in> d \<and> l \<inter> {x. x\<bullet>k \<le> c} \<noteq> {}}"
        define d2 where "d2 = {l \<inter> {x. x\<bullet>k \<ge> c} | l. l \<in> d \<and> l \<inter> {x. x\<bullet>k \<ge> c} \<noteq> {}}"
        define cb where "cb = (\<Sum>i\<in>Basis. (if i = k then c else b\<bullet>i) *\<^sub>R i)"
        define ca where "ca = (\<Sum>i\<in>Basis. (if i = k then c else a\<bullet>i) *\<^sub>R i)"
        note division_points_psubset[OF \<open>d division_of cbox a b\<close> ab kc(1-2) j]
        note psubset_card_mono[OF _ this(1)] psubset_card_mono[OF _ this(2)]
        then have *: "F g d1 = g (cbox a b \<inter> {x. x\<bullet>k \<le> c})" "F g d2 = g (cbox a b \<inter> {x. x\<bullet>k \<ge> c})"
          unfolding interval_split[OF kc(4)]
          apply (rule_tac[!] "less.hyps"[rule_format])
          using division_split[OF \<open>d division_of cbox a b\<close>, where k=k and c=c]
          apply (simp_all add: interval_split kc d1_def d2_def division_points_finite[OF \<open>d division_of cbox a b\<close>])
          done
        { fix l y
          assume as: "l \<in> d" "y \<in> d" "l \<inter> {x. x \<bullet> k \<le> c} = y \<inter> {x. x \<bullet> k \<le> c}" "l \<noteq> y"
          from division_ofD(4)[OF \<open>d division_of cbox a b\<close> this(1)] guess u v by (elim exE) note leq=this
          have "g (l \<inter> {x. x \<bullet> k \<le> c}) = \<^bold>1"
            unfolding leq interval_split[OF kc(4)]
            apply (rule operativeD[OF g])
            unfolding interval_split[symmetric, OF kc(4)]
            using division_split_left_inj less as kc leq by blast
        } note fxk_le = this
        { fix l y
          assume as: "l \<in> d" "y \<in> d" "l \<inter> {x. c \<le> x \<bullet> k} = y \<inter> {x. c \<le> x \<bullet> k}" "l \<noteq> y"
          from division_ofD(4)[OF \<open>d division_of cbox a b\<close> this(1)] guess u v by (elim exE) note leq=this
          have "g (l \<inter> {x. x \<bullet> k \<ge> c}) = \<^bold>1"
            unfolding leq interval_split[OF kc(4)]
            apply (rule operativeD(1)[OF g])
            unfolding interval_split[symmetric,OF kc(4)]
            using division_split_right_inj less leq as kc by blast
        } note fxk_ge = this
        have d1_alt: "d1 = (\<lambda>l. l \<inter> {x. x\<bullet>k \<le> c}) ` {l \<in> d. l \<inter> {x. x\<bullet>k \<le> c} \<noteq> {}}"
          using d1_def by auto
        have d2_alt: "d2 = (\<lambda>l. l \<inter> {x. x\<bullet>k \<ge> c}) ` {l \<in> d. l \<inter> {x. x\<bullet>k \<ge> c} \<noteq> {}}"
          using d2_def by auto
        have "g (cbox a b) = F g d1 \<^bold>* F g d2" (is "_ = ?prev")
          unfolding * using g kc(4) by blast
        also have "F g d1 = F (\<lambda>l. g (l \<inter> {x. x\<bullet>k \<le> c})) d"
          unfolding d1_alt using division_of_finite[OF less.prems] fxk_le
          by (subst reindex_nontrivial) (auto intro!: mono_neutral_cong_left simp: operative_empty[OF g])
        also have "F g d2 = F (\<lambda>l. g (l \<inter> {x. x\<bullet>k \<ge> c})) d"
          unfolding d2_alt using division_of_finite[OF less.prems] fxk_ge
          by (subst reindex_nontrivial) (auto intro!: mono_neutral_cong_left simp: operative_empty[OF g])
        also have *: "\<forall>x\<in>d. g x = g (x \<inter> {x. x \<bullet> k \<le> c}) \<^bold>* g (x \<inter> {x. c \<le> x \<bullet> k})"
          unfolding forall_in_division[OF \<open>d division_of cbox a b\<close>]
          using g kc(4) by blast
        have "F (\<lambda>l. g (l \<inter> {x. x\<bullet>k \<le> c})) d \<^bold>* F (\<lambda>l. g (l \<inter> {x. x\<bullet>k \<ge> c})) d = F g d"
          using * by (simp add: distrib)
        finally show ?thesis by auto
      qed
    qed
  qed
qed

lemma (in comm_monoid_set) operative_tagged_division:
  assumes f: "operative g" and d: "d tagged_division_of (cbox a b)"
  shows "F (\<lambda>(x, l). g l) d = g (cbox a b)"
  unfolding d[THEN division_of_tagged_division, THEN operative_division[OF f], symmetric]
  by (simp add: f[THEN operativeD(1)] over_tagged_division_lemma[OF d])

lemma additive_content_division: "d division_of (cbox a b) \<Longrightarrow> setsum content d = content (cbox a b)"
  by (metis operative_content setsum.operative_division)

lemma additive_content_tagged_division:
  "d tagged_division_of (cbox a b) \<Longrightarrow> setsum (\<lambda>(x,l). content l) d = content (cbox a b)"
  unfolding setsum.operative_tagged_division[OF operative_content, symmetric] by blast

lemma content_real_eq_0: "content {a .. b::real} = 0 \<longleftrightarrow> a \<ge> b"
  by (metis atLeastatMost_empty_iff2 content_empty content_real diff_self eq_iff le_cases le_iff_diff_le_0)

lemma interval_real_split:
  "{a .. b::real} \<inter> {x. x \<le> c} = {a .. min b c}"
  "{a .. b} \<inter> {x. c \<le> x} = {max a c .. b}"
  apply (metis Int_atLeastAtMostL1 atMost_def)
  apply (metis Int_atLeastAtMostL2 atLeast_def)
  done

lemma (in comm_monoid) operative_1_lt:
  "operative (g :: real set \<Rightarrow> 'a) \<longleftrightarrow>
    ((\<forall>a b. b \<le> a \<longrightarrow> g {a .. b} = \<^bold>1) \<and> (\<forall>a b c. a < c \<and> c < b \<longrightarrow> g {a .. c} \<^bold>* g {c .. b} = g {a .. b}))"
  apply (simp add: operative_def content_real_eq_0 atMost_def[symmetric] atLeast_def[symmetric]
              del: content_real_if)
proof safe
  fix a b c :: real
  assume *: "\<forall>a b c. g {a..b} = g {a..min b c} \<^bold>* g {max a c..b}"
  assume "a < c" "c < b"
  with *[rule_format, of a b c] show "g {a..c} \<^bold>* g {c..b} = g {a..b}"
    by (simp add: less_imp_le min.absorb2 max.absorb2)
next
  fix a b c :: real
  assume as: "\<forall>a b. b \<le> a \<longrightarrow> g {a..b} = \<^bold>1"
    "\<forall>a b c. a < c \<and> c < b \<longrightarrow> g {a..c} \<^bold>* g {c..b} = g {a..b}"
  from as(1)[rule_format, of 0 1] as(1)[rule_format, of a a for a] as(2)
  have [simp]: "g {} = \<^bold>1" "\<And>a. g {a} = \<^bold>1"
    "\<And>a b c. a < c \<Longrightarrow> c < b \<Longrightarrow> g {a..c} \<^bold>* g {c..b} = g {a..b}"
    by auto
  show "g {a..b} = g {a..min b c} \<^bold>* g {max a c..b}"
    by (auto simp: min_def max_def le_less)
qed

lemma (in comm_monoid) operative_1_le:
  "operative (g :: real set \<Rightarrow> 'a) \<longleftrightarrow>
    ((\<forall>a b. b \<le> a \<longrightarrow> g {a..b} = \<^bold>1) \<and> (\<forall>a b c. a \<le> c \<and> c \<le> b \<longrightarrow> g {a .. c} \<^bold>* g {c .. b} = g {a .. b}))"
  unfolding operative_1_lt
proof safe
  fix a b c :: real
  assume as: "\<forall>a b c. a \<le> c \<and> c \<le> b \<longrightarrow> g {a..c} \<^bold>* g {c..b} = g {a..b}" "a < c" "c < b"
  show "g {a..c} \<^bold>* g {c..b} = g {a..b}"
    apply (rule as(1)[rule_format])
    using as(2-)
    apply auto
    done
next
  fix a b c :: real
  assume "\<forall>a b. b \<le> a \<longrightarrow> g {a .. b} = \<^bold>1"
    and "\<forall>a b c. a < c \<and> c < b \<longrightarrow> g {a..c} \<^bold>* g {c..b} = g {a..b}"
    and "a \<le> c"
    and "c \<le> b"
  note as = this[rule_format]
  show "g {a..c} \<^bold>* g {c..b} = g {a..b}"
  proof (cases "c = a \<or> c = b")
    case False
    then show ?thesis
      apply -
      apply (subst as(2))
      using as(3-)
      apply auto
      done
  next
    case True
    then show ?thesis
    proof
      assume *: "c = a"
      then have "g {a .. c} = \<^bold>1"
        apply -
        apply (rule as(1)[rule_format])
        apply auto
        done
      then show ?thesis
        unfolding * by auto
    next
      assume *: "c = b"
      then have "g {c .. b} = \<^bold>1"
        apply -
        apply (rule as(1)[rule_format])
        apply auto
        done
      then show ?thesis
        unfolding * by auto
    qed
  qed
qed

subsection \<open>Fine-ness of a partition w.r.t. a gauge.\<close>

definition fine  (infixr "fine" 46)
  where "d fine s \<longleftrightarrow> (\<forall>(x,k) \<in> s. k \<subseteq> d x)"

lemma fineI:
  assumes "\<And>x k. (x, k) \<in> s \<Longrightarrow> k \<subseteq> d x"
  shows "d fine s"
  using assms unfolding fine_def by auto

lemma fineD[dest]:
  assumes "d fine s"
  shows "\<And>x k. (x,k) \<in> s \<Longrightarrow> k \<subseteq> d x"
  using assms unfolding fine_def by auto

lemma fine_inter: "(\<lambda>x. d1 x \<inter> d2 x) fine p \<longleftrightarrow> d1 fine p \<and> d2 fine p"
  unfolding fine_def by auto

lemma fine_inters:
 "(\<lambda>x. \<Inter>{f d x | d.  d \<in> s}) fine p \<longleftrightarrow> (\<forall>d\<in>s. (f d) fine p)"
  unfolding fine_def by blast

lemma fine_union: "d fine p1 \<Longrightarrow> d fine p2 \<Longrightarrow> d fine (p1 \<union> p2)"
  unfolding fine_def by blast

lemma fine_unions: "(\<And>p. p \<in> ps \<Longrightarrow> d fine p) \<Longrightarrow> d fine (\<Union>ps)"
  unfolding fine_def by auto

lemma fine_subset: "p \<subseteq> q \<Longrightarrow> d fine q \<Longrightarrow> d fine p"
  unfolding fine_def by blast


subsection \<open>Gauge integral. Define on compact intervals first, then use a limit.\<close>

definition has_integral_compact_interval (infixr "has'_integral'_compact'_interval" 46)
  where "(f has_integral_compact_interval y) i \<longleftrightarrow>
    (\<forall>e>0. \<exists>d. gauge d \<and>
      (\<forall>p. p tagged_division_of i \<and> d fine p \<longrightarrow> norm ((\<Sum>(x,k)\<in>p. content k *\<^sub>R f x) - y) < e))"

definition has_integral ::
    "('n::euclidean_space \<Rightarrow> 'b::real_normed_vector) \<Rightarrow> 'b \<Rightarrow> 'n set \<Rightarrow> bool"
  (infixr "has'_integral" 46)
  where "(f has_integral y) i \<longleftrightarrow>
    (if \<exists>a b. i = cbox a b
     then (f has_integral_compact_interval y) i
     else (\<forall>e>0. \<exists>B>0. \<forall>a b. ball 0 B \<subseteq> cbox a b \<longrightarrow>
      (\<exists>z. ((\<lambda>x. if x \<in> i then f x else 0) has_integral_compact_interval z) (cbox a b) \<and>
        norm (z - y) < e)))"

lemma has_integral:
  "(f has_integral y) (cbox a b) \<longleftrightarrow>
    (\<forall>e>0. \<exists>d. gauge d \<and>
      (\<forall>p. p tagged_division_of (cbox a b) \<and> d fine p \<longrightarrow>
        norm (setsum (\<lambda>(x,k). content(k) *\<^sub>R f x) p - y) < e))"
  unfolding has_integral_def has_integral_compact_interval_def
  by auto

lemma has_integral_real:
  "(f has_integral y) {a .. b::real} \<longleftrightarrow>
    (\<forall>e>0. \<exists>d. gauge d \<and>
      (\<forall>p. p tagged_division_of {a .. b} \<and> d fine p \<longrightarrow>
        norm (setsum (\<lambda>(x,k). content(k) *\<^sub>R f x) p - y) < e))"
  unfolding box_real[symmetric]
  by (rule has_integral)

lemma has_integralD[dest]:
  assumes "(f has_integral y) (cbox a b)"
    and "e > 0"
  obtains d where "gauge d"
    and "\<And>p. p tagged_division_of (cbox a b) \<Longrightarrow> d fine p \<Longrightarrow>
      norm (setsum (\<lambda>(x,k). content(k) *\<^sub>R f(x)) p - y) < e"
  using assms unfolding has_integral by auto

lemma has_integral_alt:
  "(f has_integral y) i \<longleftrightarrow>
    (if \<exists>a b. i = cbox a b
     then (f has_integral y) i
     else (\<forall>e>0. \<exists>B>0. \<forall>a b. ball 0 B \<subseteq> cbox a b \<longrightarrow>
      (\<exists>z. ((\<lambda>x. if x \<in> i then f(x) else 0) has_integral z) (cbox a b) \<and> norm (z - y) < e)))"
  unfolding has_integral
  unfolding has_integral_compact_interval_def has_integral_def
  by auto

lemma has_integral_altD:
  assumes "(f has_integral y) i"
    and "\<not> (\<exists>a b. i = cbox a b)"
    and "e>0"
  obtains B where "B > 0"
    and "\<forall>a b. ball 0 B \<subseteq> cbox a b \<longrightarrow>
      (\<exists>z. ((\<lambda>x. if x \<in> i then f(x) else 0) has_integral z) (cbox a b) \<and> norm(z - y) < e)"
  using assms
  unfolding has_integral
  unfolding has_integral_compact_interval_def has_integral_def
  by auto

definition integrable_on (infixr "integrable'_on" 46)
  where "f integrable_on i \<longleftrightarrow> (\<exists>y. (f has_integral y) i)"

definition "integral i f = (SOME y. (f has_integral y) i \<or> ~ f integrable_on i \<and> y=0)"

lemma integrable_integral[dest]: "f integrable_on i \<Longrightarrow> (f has_integral (integral i f)) i"
  unfolding integrable_on_def integral_def by (metis (mono_tags, lifting) someI_ex)

lemma not_integrable_integral: "~ f integrable_on i \<Longrightarrow> integral i f = 0"
  unfolding integrable_on_def integral_def by blast

lemma has_integral_integrable[intro]: "(f has_integral i) s \<Longrightarrow> f integrable_on s"
  unfolding integrable_on_def by auto

lemma has_integral_integral: "f integrable_on s \<longleftrightarrow> (f has_integral (integral s f)) s"
  by auto

lemma setsum_content_null:
  assumes "content (cbox a b) = 0"
    and "p tagged_division_of (cbox a b)"
  shows "setsum (\<lambda>(x,k). content k *\<^sub>R f x) p = (0::'a::real_normed_vector)"
proof (rule setsum.neutral, rule)
  fix y
  assume y: "y \<in> p"
  obtain x k where xk: "y = (x, k)"
    using surj_pair[of y] by blast
  note assm = tagged_division_ofD(3-4)[OF assms(2) y[unfolded xk]]
  from this(2) obtain c d where k: "k = cbox c d" by blast
  have "(\<lambda>(x, k). content k *\<^sub>R f x) y = content k *\<^sub>R f x"
    unfolding xk by auto
  also have "\<dots> = 0"
    using content_subset[OF assm(1)[unfolded k]] content_pos_le[of c d]
    unfolding assms(1) k
    by auto
  finally show "(\<lambda>(x, k). content k *\<^sub>R f x) y = 0" .
qed


subsection \<open>Some basic combining lemmas.\<close>

lemma tagged_division_unions_exists:
  assumes "finite iset"
    and "\<forall>i\<in>iset. \<exists>p. p tagged_division_of i \<and> d fine p"
    and "\<forall>i1\<in>iset. \<forall>i2\<in>iset. i1 \<noteq> i2 \<longrightarrow> interior i1 \<inter> interior i2 = {}"
    and "\<Union>iset = i"
   obtains p where "p tagged_division_of i" and "d fine p"
proof -
  obtain pfn where pfn:
    "\<And>x. x \<in> iset \<Longrightarrow> pfn x tagged_division_of x"
    "\<And>x. x \<in> iset \<Longrightarrow> d fine pfn x"
    using bchoice[OF assms(2)] by auto
  show thesis
    apply (rule_tac p="\<Union>(pfn ` iset)" in that)
    using assms(1) assms(3) assms(4) pfn(1) tagged_division_unions apply force
    by (metis (mono_tags, lifting) fine_unions imageE pfn(2))
qed


subsection \<open>The set we're concerned with must be closed.\<close>

lemma division_of_closed:
  fixes i :: "'n::euclidean_space set"
  shows "s division_of i \<Longrightarrow> closed i"
  unfolding division_of_def by fastforce

subsection \<open>General bisection principle for intervals; might be useful elsewhere.\<close>

lemma interval_bisection_step:
  fixes type :: "'a::euclidean_space"
  assumes "P {}"
    and "\<forall>s t. P s \<and> P t \<and> interior(s) \<inter> interior(t) = {} \<longrightarrow> P (s \<union> t)"
    and "\<not> P (cbox a (b::'a))"
  obtains c d where "\<not> P (cbox c d)"
    and "\<forall>i\<in>Basis. a\<bullet>i \<le> c\<bullet>i \<and> c\<bullet>i \<le> d\<bullet>i \<and> d\<bullet>i \<le> b\<bullet>i \<and> 2 * (d\<bullet>i - c\<bullet>i) \<le> b\<bullet>i - a\<bullet>i"
proof -
  have "cbox a b \<noteq> {}"
    using assms(1,3) by metis
  then have ab: "\<And>i. i\<in>Basis \<Longrightarrow> a \<bullet> i \<le> b \<bullet> i"
    by (force simp: mem_box)
  { fix f
    have "\<lbrakk>finite f;
           \<And>s. s\<in>f \<Longrightarrow> P s;
           \<And>s. s\<in>f \<Longrightarrow> \<exists>a b. s = cbox a b;
           \<And>s t. s\<in>f \<Longrightarrow> t\<in>f \<Longrightarrow> s \<noteq> t \<Longrightarrow> interior s \<inter> interior t = {}\<rbrakk> \<Longrightarrow> P (\<Union>f)"
    proof (induct f rule: finite_induct)
      case empty
      show ?case
        using assms(1) by auto
    next
      case (insert x f)
      show ?case
        unfolding Union_insert
        apply (rule assms(2)[rule_format])
        using inter_interior_unions_intervals [of f "interior x"]
        apply (auto simp: insert)
        by (metis IntI empty_iff insert.hyps(2) insert.prems(3) insert_iff)
    qed
  } note UN_cases = this
  let ?A = "{cbox c d | c d::'a. \<forall>i\<in>Basis. (c\<bullet>i = a\<bullet>i) \<and> (d\<bullet>i = (a\<bullet>i + b\<bullet>i) / 2) \<or>
    (c\<bullet>i = (a\<bullet>i + b\<bullet>i) / 2) \<and> (d\<bullet>i = b\<bullet>i)}"
  let ?PP = "\<lambda>c d. \<forall>i\<in>Basis. a\<bullet>i \<le> c\<bullet>i \<and> c\<bullet>i \<le> d\<bullet>i \<and> d\<bullet>i \<le> b\<bullet>i \<and> 2 * (d\<bullet>i - c\<bullet>i) \<le> b\<bullet>i - a\<bullet>i"
  {
    presume "\<forall>c d. ?PP c d \<longrightarrow> P (cbox c d) \<Longrightarrow> False"
    then show thesis
      unfolding atomize_not not_all
      by (blast intro: that)
  }
  assume as: "\<forall>c d. ?PP c d \<longrightarrow> P (cbox c d)"
  have "P (\<Union>?A)"
  proof (rule UN_cases)
    let ?B = "(\<lambda>s. cbox (\<Sum>i\<in>Basis. (if i \<in> s then a\<bullet>i else (a\<bullet>i + b\<bullet>i) / 2) *\<^sub>R i::'a)
      (\<Sum>i\<in>Basis. (if i \<in> s then (a\<bullet>i + b\<bullet>i) / 2 else b\<bullet>i) *\<^sub>R i)) ` {s. s \<subseteq> Basis}"
    have "?A \<subseteq> ?B"
    proof
      fix x
      assume "x \<in> ?A"
      then obtain c d
        where x:  "x = cbox c d"
                  "\<And>i. i \<in> Basis \<Longrightarrow>
                        c \<bullet> i = a \<bullet> i \<and> d \<bullet> i = (a \<bullet> i + b \<bullet> i) / 2 \<or>
                        c \<bullet> i = (a \<bullet> i + b \<bullet> i) / 2 \<and> d \<bullet> i = b \<bullet> i" by blast
      show "x \<in> ?B"
        unfolding image_iff x
        apply (rule_tac x="{i. i\<in>Basis \<and> c\<bullet>i = a\<bullet>i}" in bexI)
        apply (rule arg_cong2 [where f = cbox])
        using x(2) ab
        apply (auto simp add: euclidean_eq_iff[where 'a='a])
        by fastforce
    qed
    then show "finite ?A"
      by (rule finite_subset) auto
  next
    fix s
    assume "s \<in> ?A"
    then obtain c d
      where s: "s = cbox c d"
               "\<And>i. i \<in> Basis \<Longrightarrow>
                     c \<bullet> i = a \<bullet> i \<and> d \<bullet> i = (a \<bullet> i + b \<bullet> i) / 2 \<or>
                     c \<bullet> i = (a \<bullet> i + b \<bullet> i) / 2 \<and> d \<bullet> i = b \<bullet> i"
      by blast
    show "P s"
      unfolding s
      apply (rule as[rule_format])
      using ab s(2) by force
    show "\<exists>a b. s = cbox a b"
      unfolding s by auto
    fix t
    assume "t \<in> ?A"
    then obtain e f where t:
      "t = cbox e f"
      "\<And>i. i \<in> Basis \<Longrightarrow>
        e \<bullet> i = a \<bullet> i \<and> f \<bullet> i = (a \<bullet> i + b \<bullet> i) / 2 \<or>
        e \<bullet> i = (a \<bullet> i + b \<bullet> i) / 2 \<and> f \<bullet> i = b \<bullet> i"
      by blast
    assume "s \<noteq> t"
    then have "\<not> (c = e \<and> d = f)"
      unfolding s t by auto
    then obtain i where "c\<bullet>i \<noteq> e\<bullet>i \<or> d\<bullet>i \<noteq> f\<bullet>i" and i': "i \<in> Basis"
      unfolding euclidean_eq_iff[where 'a='a] by auto
    then have i: "c\<bullet>i \<noteq> e\<bullet>i" "d\<bullet>i \<noteq> f\<bullet>i"
      using s(2) t(2) apply fastforce
      using t(2)[OF i'] \<open>c \<bullet> i \<noteq> e \<bullet> i \<or> d \<bullet> i \<noteq> f \<bullet> i\<close> i' s(2) t(2) by fastforce
    have *: "\<And>s t. (\<And>a. a \<in> s \<Longrightarrow> a \<in> t \<Longrightarrow> False) \<Longrightarrow> s \<inter> t = {}"
      by auto
    show "interior s \<inter> interior t = {}"
      unfolding s t interior_cbox
    proof (rule *)
      fix x
      assume "x \<in> box c d" "x \<in> box e f"
      then have x: "c\<bullet>i < d\<bullet>i" "e\<bullet>i < f\<bullet>i" "c\<bullet>i < f\<bullet>i" "e\<bullet>i < d\<bullet>i"
        unfolding mem_box using i'
        by force+
      show False  using s(2)[OF i']
      proof safe
        assume as: "c \<bullet> i = a \<bullet> i" "d \<bullet> i = (a \<bullet> i + b \<bullet> i) / 2"
        show False
          using t(2)[OF i'] and i x unfolding as by (fastforce simp add:field_simps)
      next
        assume as: "c \<bullet> i = (a \<bullet> i + b \<bullet> i) / 2" "d \<bullet> i = b \<bullet> i"
        show False
          using t(2)[OF i'] and i x unfolding as by(fastforce simp add:field_simps)
      qed
    qed
  qed
  also have "\<Union>?A = cbox a b"
  proof (rule set_eqI,rule)
    fix x
    assume "x \<in> \<Union>?A"
    then obtain c d where x:
      "x \<in> cbox c d"
      "\<And>i. i \<in> Basis \<Longrightarrow>
        c \<bullet> i = a \<bullet> i \<and> d \<bullet> i = (a \<bullet> i + b \<bullet> i) / 2 \<or>
        c \<bullet> i = (a \<bullet> i + b \<bullet> i) / 2 \<and> d \<bullet> i = b \<bullet> i"
      by blast
    show "x\<in>cbox a b"
      unfolding mem_box
    proof safe
      fix i :: 'a
      assume i: "i \<in> Basis"
      then show "a \<bullet> i \<le> x \<bullet> i" "x \<bullet> i \<le> b \<bullet> i"
        using x(2)[OF i] x(1)[unfolded mem_box,THEN bspec, OF i] by auto
    qed
  next
    fix x
    assume x: "x \<in> cbox a b"
    have "\<forall>i\<in>Basis.
      \<exists>c d. (c = a\<bullet>i \<and> d = (a\<bullet>i + b\<bullet>i) / 2 \<or> c = (a\<bullet>i + b\<bullet>i) / 2 \<and> d = b\<bullet>i) \<and> c\<le>x\<bullet>i \<and> x\<bullet>i \<le> d"
      (is "\<forall>i\<in>Basis. \<exists>c d. ?P i c d")
      unfolding mem_box
    proof
      fix i :: 'a
      assume i: "i \<in> Basis"
      have "?P i (a\<bullet>i) ((a \<bullet> i + b \<bullet> i) / 2) \<or> ?P i ((a \<bullet> i + b \<bullet> i) / 2) (b\<bullet>i)"
        using x[unfolded mem_box,THEN bspec, OF i] by auto
      then show "\<exists>c d. ?P i c d"
        by blast
    qed
    then show "x\<in>\<Union>?A"
      unfolding Union_iff Bex_def mem_Collect_eq choice_Basis_iff
      apply auto
      apply (rule_tac x="cbox xa xaa" in exI)
      unfolding mem_box
      apply auto
      done
  qed
  finally show False
    using assms by auto
qed

lemma interval_bisection:
  fixes type :: "'a::euclidean_space"
  assumes "P {}"
    and "(\<forall>s t. P s \<and> P t \<and> interior(s) \<inter> interior(t) = {} \<longrightarrow> P(s \<union> t))"
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
      case as: False
      obtain c d where "\<not> P (cbox c d)"
        "\<forall>i\<in>Basis.
           fst x \<bullet> i \<le> c \<bullet> i \<and>
           c \<bullet> i \<le> d \<bullet> i \<and>
           d \<bullet> i \<le> snd x \<bullet> i \<and>
           2 * (d \<bullet> i - c \<bullet> i) \<le> snd x \<bullet> i - fst x \<bullet> i"
        by (rule interval_bisection_step[of P, OF assms(1-2) as])
      then show ?thesis
        apply -
        apply (rule_tac x="(c,d)" in exI)
        apply auto
        done
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
            2 * (snd (f x) \<bullet> i - fst (f x) \<bullet> i) \<le> snd x \<bullet> i - fst x \<bullet> i)"
    apply -
    apply (drule choice)
    apply blast
    done
  define AB A B where ab_def: "AB n = (f ^^ n) (a,b)" "A n = fst(AB n)" "B n = snd(AB n)" for n
  have "A 0 = a" "B 0 = b" "\<And>n. \<not> P (cbox (A(Suc n)) (B(Suc n))) \<and>
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
        unfolding S
        apply (rule f[rule_format]) using assms(3)
        apply auto
        done
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
  note AB = this(1-2) conjunctD2[OF this(3),rule_format]

  have interv: "\<exists>n. \<forall>x\<in>cbox (A n) (B n). \<forall>y\<in>cbox (A n) (B n). dist x y < e"
    if e: "0 < e" for e
  proof -
    obtain n where n: "(\<Sum>i\<in>Basis. b \<bullet> i - a \<bullet> i) / e < 2 ^ n"
      using real_arch_pow[of 2 "(setsum (\<lambda>i. b\<bullet>i - a\<bullet>i) Basis) / e"] by auto
    show ?thesis
    proof (rule exI [where x=n], clarify)
      fix x y
      assume xy: "x\<in>cbox (A n) (B n)" "y\<in>cbox (A n) (B n)"
      have "dist x y \<le> setsum (\<lambda>i. \<bar>(x - y)\<bullet>i\<bar>) Basis"
        unfolding dist_norm by(rule norm_le_l1)
      also have "\<dots> \<le> setsum (\<lambda>i. B n\<bullet>i - A n\<bullet>i) Basis"
      proof (rule setsum_mono)
        fix i :: 'a
        assume i: "i \<in> Basis"
        show "\<bar>(x - y) \<bullet> i\<bar> \<le> B n \<bullet> i - A n \<bullet> i"
          using xy[unfolded mem_box,THEN bspec, OF i]
          by (auto simp: inner_diff_left)
      qed
      also have "\<dots> \<le> setsum (\<lambda>i. b\<bullet>i - a\<bullet>i) Basis / 2^n"
        unfolding setsum_divide_distrib
      proof (rule setsum_mono)
        show "B n \<bullet> i - A n \<bullet> i \<le> (b \<bullet> i - a \<bullet> i) / 2 ^ n" if i: "i \<in> Basis" for i
        proof (induct n)
          case 0
          then show ?case
            unfolding AB by auto
        next
          case (Suc n)
          have "B (Suc n) \<bullet> i - A (Suc n) \<bullet> i \<le> (B n \<bullet> i - A n \<bullet> i) / 2"
            using AB(4)[of i n] using i by auto
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
        using AB(4) by (intro order_trans[OF step.IH] subset_box_imp) auto
    qed simp
  } note ABsubset = this
  have "\<exists>a. \<forall>n. a\<in> cbox (A n) (B n)"
    by (rule decreasing_closed_nest[rule_format,OF closed_cbox _ ABsubset interv])
      (metis nat.exhaust AB(1-3) assms(1,3))
  then obtain x0 where x0: "\<And>n. x0 \<in> cbox (A n) (B n)"
    by blast
  show thesis
  proof (rule that[rule_format, of x0])
    show "x0\<in>cbox a b"
      using x0[of 0] unfolding AB .
    fix e :: real
    assume "e > 0"
    from interv[OF this] obtain n
      where n: "\<forall>x\<in>cbox (A n) (B n). \<forall>y\<in>cbox (A n) (B n). dist x y < e" ..
    have "\<not> P (cbox (A n) (B n))"
      apply (cases "0 < n")
      using AB(3)[of "n - 1"] assms(3) AB(1-2)
      apply auto
      done
    moreover have "cbox (A n) (B n) \<subseteq> ball x0 e"
      using n using x0[of n] by auto
    moreover have "cbox (A n) (B n) \<subseteq> cbox a b"
      unfolding AB(1-2)[symmetric] by (rule ABsubset) auto
    ultimately show "\<exists>c d. x0 \<in> cbox c d \<and> cbox c d \<subseteq> ball x0 e \<and> cbox c d \<subseteq> cbox a b \<and> \<not> P (cbox c d)"
      apply (rule_tac x="A n" in exI)
      apply (rule_tac x="B n" in exI)
      apply (auto simp: x0)
      done
  qed
qed


subsection \<open>Cousin's lemma.\<close>

lemma fine_division_exists:
  fixes a b :: "'a::euclidean_space"
  assumes "gauge g"
  obtains p where "p tagged_division_of (cbox a b)" "g fine p"
proof -
  presume "\<not> (\<exists>p. p tagged_division_of (cbox a b) \<and> g fine p) \<Longrightarrow> False"
  then obtain p where "p tagged_division_of (cbox a b)" "g fine p"
    by blast
  then show thesis ..
next
  assume as: "\<not> (\<exists>p. p tagged_division_of (cbox a b) \<and> g fine p)"
  obtain x where x:
      "x \<in> (cbox a b)"
      "\<And>e. 0 < e \<Longrightarrow>
        \<exists>c d.
          x \<in> cbox c d \<and>
          cbox c d \<subseteq> ball x e \<and>
          cbox c d \<subseteq> (cbox a b) \<and>
          \<not> (\<exists>p. p tagged_division_of cbox c d \<and> g fine p)"
    apply (rule interval_bisection[of "\<lambda>s. \<exists>p. p tagged_division_of s \<and> g fine p", OF _ _ as])
    apply (simp add: fine_def)
    apply (metis tagged_division_union fine_union)
    apply (auto simp: )
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
  then show False
    using tagged_division_of_self[OF c_d(1)] using c_d by auto
qed

lemma fine_division_exists_real:
  fixes a b :: real
  assumes "gauge g"
  obtains p where "p tagged_division_of {a .. b}" "g fine p"
  by (metis assms box_real(2) fine_division_exists)

subsection \<open>Basic theorems about integrals.\<close>

lemma has_integral_unique:
  fixes f :: "'n::euclidean_space \<Rightarrow> 'a::real_normed_vector"
  assumes "(f has_integral k1) i"
    and "(f has_integral k2) i"
  shows "k1 = k2"
proof (rule ccontr)
  let ?e = "norm (k1 - k2) / 2"
  assume as: "k1 \<noteq> k2"
  then have e: "?e > 0"
    by auto
  have lem: False
    if f_k1: "(f has_integral k1) (cbox a b)"
    and f_k2: "(f has_integral k2) (cbox a b)"
    and "k1 \<noteq> k2"
    for f :: "'n \<Rightarrow> 'a" and a b k1 k2
  proof -
    let ?e = "norm (k1 - k2) / 2"
    from \<open>k1 \<noteq> k2\<close> have e: "?e > 0" by auto
    obtain d1 where d1:
        "gauge d1"
        "\<And>p. p tagged_division_of cbox a b \<Longrightarrow>
          d1 fine p \<Longrightarrow> norm ((\<Sum>(x, k)\<in>p. content k *\<^sub>R f x) - k1) < norm (k1 - k2) / 2"
      by (rule has_integralD[OF f_k1 e]) blast
    obtain d2 where d2:
        "gauge d2"
        "\<And>p. p tagged_division_of cbox a b \<Longrightarrow>
          d2 fine p \<Longrightarrow> norm ((\<Sum>(x, k)\<in>p. content k *\<^sub>R f x) - k2) < norm (k1 - k2) / 2"
      by (rule has_integralD[OF f_k2 e]) blast
    obtain p where p:
        "p tagged_division_of cbox a b"
        "(\<lambda>x. d1 x \<inter> d2 x) fine p"
      by (rule fine_division_exists[OF gauge_inter[OF d1(1) d2(1)]])
    let ?c = "(\<Sum>(x, k)\<in>p. content k *\<^sub>R f x)"
    have "norm (k1 - k2) \<le> norm (?c - k2) + norm (?c - k1)"
      using norm_triangle_ineq4[of "k1 - ?c" "k2 - ?c"]
      by (auto simp add:algebra_simps norm_minus_commute)
    also have "\<dots> < norm (k1 - k2) / 2 + norm (k1 - k2) / 2"
      apply (rule add_strict_mono)
      apply (rule_tac[!] d2(2) d1(2))
      using p unfolding fine_def
      apply auto
      done
    finally show False by auto
  qed
  {
    presume "\<not> (\<exists>a b. i = cbox a b) \<Longrightarrow> False"
    then show False
      using as assms lem by blast
  }
  assume as: "\<not> (\<exists>a b. i = cbox a b)"
  obtain B1 where B1:
      "0 < B1"
      "\<And>a b. ball 0 B1 \<subseteq> cbox a b \<Longrightarrow>
        \<exists>z. ((\<lambda>x. if x \<in> i then f x else 0) has_integral z) (cbox a b) \<and>
          norm (z - k1) < norm (k1 - k2) / 2"
    by (rule has_integral_altD[OF assms(1) as,OF e]) blast
  obtain B2 where B2:
      "0 < B2"
      "\<And>a b. ball 0 B2 \<subseteq> cbox a b \<Longrightarrow>
        \<exists>z. ((\<lambda>x. if x \<in> i then f x else 0) has_integral z) (cbox a b) \<and>
          norm (z - k2) < norm (k1 - k2) / 2"
    by (rule has_integral_altD[OF assms(2) as,OF e]) blast
  have "\<exists>a b::'n. ball 0 B1 \<union> ball 0 B2 \<subseteq> cbox a b"
    apply (rule bounded_subset_cbox)
    using bounded_Un bounded_ball
    apply auto
    done
  then obtain a b :: 'n where ab: "ball 0 B1 \<subseteq> cbox a b" "ball 0 B2 \<subseteq> cbox a b"
    by blast
  obtain w where w:
    "((\<lambda>x. if x \<in> i then f x else 0) has_integral w) (cbox a b)"
    "norm (w - k1) < norm (k1 - k2) / 2"
    using B1(2)[OF ab(1)] by blast
  obtain z where z:
    "((\<lambda>x. if x \<in> i then f x else 0) has_integral z) (cbox a b)"
    "norm (z - k2) < norm (k1 - k2) / 2"
    using B2(2)[OF ab(2)] by blast
  have "z = w"
    using lem[OF w(1) z(1)] by auto
  then have "norm (k1 - k2) \<le> norm (z - k2) + norm (w - k1)"
    using norm_triangle_ineq4 [of "k1 - w" "k2 - z"]
    by (auto simp add: norm_minus_commute)
  also have "\<dots> < norm (k1 - k2) / 2 + norm (k1 - k2) / 2"
    apply (rule add_strict_mono)
    apply (rule_tac[!] z(2) w(2))
    done
  finally show False by auto
qed

lemma integral_unique [intro]: "(f has_integral y) k \<Longrightarrow> integral k f = y"
  unfolding integral_def
  by (rule some_equality) (auto intro: has_integral_unique)

lemma eq_integralD: "integral k f = y \<Longrightarrow> (f has_integral y) k \<or> ~ f integrable_on k \<and> y=0"
  unfolding integral_def integrable_on_def
  apply (erule subst)
  apply (rule someI_ex)
  by blast

lemma has_integral_is_0:
  fixes f :: "'n::euclidean_space \<Rightarrow> 'a::real_normed_vector"
  assumes "\<forall>x\<in>s. f x = 0"
  shows "(f has_integral 0) s"
proof -
  have lem: "\<And>a b. \<And>f::'n \<Rightarrow> 'a.
    (\<forall>x\<in>cbox a b. f(x) = 0) \<Longrightarrow> (f has_integral 0) (cbox a b)"
    unfolding has_integral
  proof clarify
    fix a b e
    fix f :: "'n \<Rightarrow> 'a"
    assume as: "\<forall>x\<in>cbox a b. f x = 0" "0 < (e::real)"
    have "norm ((\<Sum>(x, k)\<in>p. content k *\<^sub>R f x) - 0) < e"
      if p: "p tagged_division_of cbox a b" for p
    proof -
      have "(\<Sum>(x, k)\<in>p. content k *\<^sub>R f x) = 0"
      proof (rule setsum.neutral, rule)
        fix x
        assume x: "x \<in> p"
        have "f (fst x) = 0"
          using tagged_division_ofD(2-3)[OF p, of "fst x" "snd x"] using as x by auto
        then show "(\<lambda>(x, k). content k *\<^sub>R f x) x = 0"
          apply (subst surjective_pairing[of x])
          unfolding split_conv
          apply auto
          done
      qed
      then show ?thesis
        using as by auto
    qed
    then show "\<exists>d. gauge d \<and>
        (\<forall>p. p tagged_division_of (cbox a b) \<and> d fine p \<longrightarrow> norm ((\<Sum>(x, k)\<in>p. content k *\<^sub>R f x) - 0) < e)"
      by auto
  qed
  {
    presume "\<not> (\<exists>a b. s = cbox a b) \<Longrightarrow> ?thesis"
    with assms lem show ?thesis
      by blast
  }
  have *: "(\<lambda>x. if x \<in> s then f x else 0) = (\<lambda>x. 0)"
    apply (rule ext)
    using assms
    apply auto
    done
  assume "\<not> (\<exists>a b. s = cbox a b)"
  then show ?thesis
    using lem
    by (subst has_integral_alt) (force simp add: *)
qed

lemma has_integral_0[simp]: "((\<lambda>x::'n::euclidean_space. 0) has_integral 0) s"
  by (rule has_integral_is_0) auto

lemma has_integral_0_eq[simp]: "((\<lambda>x. 0) has_integral i) s \<longleftrightarrow> i = 0"
  using has_integral_unique[OF has_integral_0] by auto

lemma has_integral_linear:
  fixes f :: "'n::euclidean_space \<Rightarrow> 'a::real_normed_vector"
  assumes "(f has_integral y) s"
    and "bounded_linear h"
  shows "((h \<circ> f) has_integral ((h y))) s"
proof -
  interpret bounded_linear h
    using assms(2) .
  from pos_bounded obtain B where B: "0 < B" "\<And>x. norm (h x) \<le> norm x * B"
    by blast
  have lem: "\<And>(f :: 'n \<Rightarrow> 'a) y a b.
    (f has_integral y) (cbox a b) \<Longrightarrow> ((h \<circ> f) has_integral h y) (cbox a b)"
    unfolding has_integral
  proof (clarify, goal_cases)
    case prems: (1 f y a b e)
    from pos_bounded
    obtain B where B: "0 < B" "\<And>x. norm (h x) \<le> norm x * B"
      by blast
    have "e / B > 0" using prems(2) B by simp
    then obtain g
      where g: "gauge g"
               "\<And>p. p tagged_division_of (cbox a b) \<Longrightarrow> g fine p \<Longrightarrow>
                    norm ((\<Sum>(x, k)\<in>p. content k *\<^sub>R f x) - y) < e / B"
        using prems(1) by auto
    {
      fix p
      assume as: "p tagged_division_of (cbox a b)" "g fine p"
      have hc: "\<And>x k. h ((\<lambda>(x, k). content k *\<^sub>R f x) x) = (\<lambda>(x, k). h (content k *\<^sub>R f x)) x"
        by auto
      then have "(\<Sum>(x, k)\<in>p. content k *\<^sub>R (h \<circ> f) x) = setsum (h \<circ> (\<lambda>(x, k). content k *\<^sub>R f x)) p"
        unfolding o_def unfolding scaleR[symmetric] hc by simp
      also have "\<dots> = h (\<Sum>(x, k)\<in>p. content k *\<^sub>R f x)"
        using setsum[of "\<lambda>(x,k). content k *\<^sub>R f x" p] using as by auto
      finally have "(\<Sum>(x, k)\<in>p. content k *\<^sub>R (h \<circ> f) x) = h (\<Sum>(x, k)\<in>p. content k *\<^sub>R f x)" .
      then have "norm ((\<Sum>(x, k)\<in>p. content k *\<^sub>R (h \<circ> f) x) - h y) < e"
        apply (simp add: diff[symmetric])
        apply (rule le_less_trans[OF B(2)])
        using g(2)[OF as] B(1)
        apply (auto simp add: field_simps)
        done
    }
    with g show ?case
      by (rule_tac x=g in exI) auto
  qed
  {
    presume "\<not> (\<exists>a b. s = cbox a b) \<Longrightarrow> ?thesis"
    then show ?thesis
      using assms(1) lem by blast
  }
  assume as: "\<not> (\<exists>a b. s = cbox a b)"
  then show ?thesis
  proof (subst has_integral_alt, clarsimp)
    fix e :: real
    assume e: "e > 0"
    have *: "0 < e/B" using e B(1) by simp
    obtain M where M:
      "M > 0"
      "\<And>a b. ball 0 M \<subseteq> cbox a b \<Longrightarrow>
        \<exists>z. ((\<lambda>x. if x \<in> s then f x else 0) has_integral z) (cbox a b) \<and> norm (z - y) < e / B"
      using has_integral_altD[OF assms(1) as *] by blast
    show "\<exists>B>0. \<forall>a b. ball 0 B \<subseteq> cbox a b \<longrightarrow>
      (\<exists>z. ((\<lambda>x. if x \<in> s then (h \<circ> f) x else 0) has_integral z) (cbox a b) \<and> norm (z - h y) < e)"
    proof (rule_tac x=M in exI, clarsimp simp add: M, goal_cases)
      case prems: (1 a b)
      obtain z where z:
        "((\<lambda>x. if x \<in> s then f x else 0) has_integral z) (cbox a b)"
        "norm (z - y) < e / B"
        using M(2)[OF prems(1)] by blast
      have *: "(\<lambda>x. if x \<in> s then (h \<circ> f) x else 0) = h \<circ> (\<lambda>x. if x \<in> s then f x else 0)"
        using zero by auto
      show ?case
        apply (rule_tac x="h z" in exI)
        apply (simp add: * lem z(1))
        apply (metis B diff le_less_trans pos_less_divide_eq z(2))
        done
    qed
  qed
qed

lemma has_integral_scaleR_left:
  "(f has_integral y) s \<Longrightarrow> ((\<lambda>x. f x *\<^sub>R c) has_integral (y *\<^sub>R c)) s"
  using has_integral_linear[OF _ bounded_linear_scaleR_left] by (simp add: comp_def)

lemma has_integral_mult_left:
  fixes c :: "_ :: real_normed_algebra"
  shows "(f has_integral y) s \<Longrightarrow> ((\<lambda>x. f x * c) has_integral (y * c)) s"
  using has_integral_linear[OF _ bounded_linear_mult_left] by (simp add: comp_def)

text\<open>The case analysis eliminates the condition @{term "f integrable_on s"} at the cost
     of the type class constraint \<open>division_ring\<close>\<close>
corollary integral_mult_left [simp]:
  fixes c:: "'a::{real_normed_algebra,division_ring}"
  shows "integral s (\<lambda>x. f x * c) = integral s f * c"
proof (cases "f integrable_on s \<or> c = 0")
  case True then show ?thesis
    by (force intro: has_integral_mult_left)
next
  case False then have "~ (\<lambda>x. f x * c) integrable_on s"
    using has_integral_mult_left [of "(\<lambda>x. f x * c)" _ s "inverse c"]
    by (force simp add: mult.assoc)
  with False show ?thesis by (simp add: not_integrable_integral)
qed

corollary integral_mult_right [simp]:
  fixes c:: "'a::{real_normed_field}"
  shows "integral s (\<lambda>x. c * f x) = c * integral s f"
by (simp add: mult.commute [of c])

corollary integral_divide [simp]:
  fixes z :: "'a::real_normed_field"
  shows "integral S (\<lambda>x. f x / z) = integral S (\<lambda>x. f x) / z"
using integral_mult_left [of S f "inverse z"]
  by (simp add: divide_inverse_commute)

lemma has_integral_mult_right:
  fixes c :: "'a :: real_normed_algebra"
  shows "(f has_integral y) i \<Longrightarrow> ((\<lambda>x. c * f x) has_integral (c * y)) i"
  using has_integral_linear[OF _ bounded_linear_mult_right] by (simp add: comp_def)

lemma has_integral_cmul: "(f has_integral k) s \<Longrightarrow> ((\<lambda>x. c *\<^sub>R f x) has_integral (c *\<^sub>R k)) s"
  unfolding o_def[symmetric]
  by (metis has_integral_linear bounded_linear_scaleR_right)

lemma has_integral_cmult_real:
  fixes c :: real
  assumes "c \<noteq> 0 \<Longrightarrow> (f has_integral x) A"
  shows "((\<lambda>x. c * f x) has_integral c * x) A"
proof (cases "c = 0")
  case True
  then show ?thesis by simp
next
  case False
  from has_integral_cmul[OF assms[OF this], of c] show ?thesis
    unfolding real_scaleR_def .
qed

lemma has_integral_neg: "(f has_integral k) s \<Longrightarrow> ((\<lambda>x. -(f x)) has_integral -k) s"
  by (drule_tac c="-1" in has_integral_cmul) auto

lemma has_integral_add:
  fixes f :: "'n::euclidean_space \<Rightarrow> 'a::real_normed_vector"
  assumes "(f has_integral k) s"
    and "(g has_integral l) s"
  shows "((\<lambda>x. f x + g x) has_integral (k + l)) s"
proof -
  have lem: "((\<lambda>x. f x + g x) has_integral (k + l)) (cbox a b)"
    if f_k: "(f has_integral k) (cbox a b)"
    and g_l: "(g has_integral l) (cbox a b)"
    for f :: "'n \<Rightarrow> 'a" and g a b k l
    unfolding has_integral
  proof clarify
    fix e :: real
    assume e: "e > 0"
    then have *: "e / 2 > 0"
      by auto
    obtain d1 where d1:
      "gauge d1"
      "\<And>p. p tagged_division_of (cbox a b) \<Longrightarrow> d1 fine p \<Longrightarrow>
        norm ((\<Sum>(x, k)\<in>p. content k *\<^sub>R f x) - k) < e / 2"
      using has_integralD[OF f_k *] by blast
    obtain d2 where d2:
      "gauge d2"
      "\<And>p. p tagged_division_of (cbox a b) \<Longrightarrow> d2 fine p \<Longrightarrow>
        norm ((\<Sum>(x, k)\<in>p. content k *\<^sub>R g x) - l) < e / 2"
      using has_integralD[OF g_l *] by blast
    show "\<exists>d. gauge d \<and> (\<forall>p. p tagged_division_of (cbox a b) \<and> d fine p \<longrightarrow>
              norm ((\<Sum>(x, k)\<in>p. content k *\<^sub>R (f x + g x)) - (k + l)) < e)"
    proof (rule exI [where x="\<lambda>x. (d1 x) \<inter> (d2 x)"], clarsimp simp add: gauge_inter[OF d1(1) d2(1)])
      fix p
      assume as: "p tagged_division_of (cbox a b)" "(\<lambda>x. d1 x \<inter> d2 x) fine p"
      have *: "(\<Sum>(x, k)\<in>p. content k *\<^sub>R (f x + g x)) =
        (\<Sum>(x, k)\<in>p. content k *\<^sub>R f x) + (\<Sum>(x, k)\<in>p. content k *\<^sub>R g x)"
        unfolding scaleR_right_distrib setsum.distrib[of "\<lambda>(x,k). content k *\<^sub>R f x" "\<lambda>(x,k). content k *\<^sub>R g x" p,symmetric]
        by (rule setsum.cong) auto
      from as have fine: "d1 fine p" "d2 fine p"
        unfolding fine_inter by auto
      have "norm ((\<Sum>(x, k)\<in>p. content k *\<^sub>R (f x + g x)) - (k + l)) =
            norm (((\<Sum>(x, k)\<in>p. content k *\<^sub>R f x) - k) + ((\<Sum>(x, k)\<in>p. content k *\<^sub>R g x) - l))"
        unfolding * by (auto simp add: algebra_simps)
      also have "\<dots> < e/2 + e/2"
        apply (rule le_less_trans[OF norm_triangle_ineq])
        using as d1 d2 fine
        apply (blast intro: add_strict_mono)
        done
      finally show "norm ((\<Sum>(x, k)\<in>p. content k *\<^sub>R (f x + g x)) - (k + l)) < e"
        by auto
    qed
  qed
  {
    presume "\<not> (\<exists>a b. s = cbox a b) \<Longrightarrow> ?thesis"
    then show ?thesis
      using assms lem by force
  }
  assume as: "\<not> (\<exists>a b. s = cbox a b)"
  then show ?thesis
  proof (subst has_integral_alt, clarsimp, goal_cases)
    case (1 e)
    then have *: "e / 2 > 0"
      by auto
    from has_integral_altD[OF assms(1) as *]
    obtain B1 where B1:
        "0 < B1"
        "\<And>a b. ball 0 B1 \<subseteq> cbox a b \<Longrightarrow>
          \<exists>z. ((\<lambda>x. if x \<in> s then f x else 0) has_integral z) (cbox a b) \<and> norm (z - k) < e / 2"
      by blast
    from has_integral_altD[OF assms(2) as *]
    obtain B2 where B2:
        "0 < B2"
        "\<And>a b. ball 0 B2 \<subseteq> (cbox a b) \<Longrightarrow>
          \<exists>z. ((\<lambda>x. if x \<in> s then g x else 0) has_integral z) (cbox a b) \<and> norm (z - l) < e / 2"
      by blast
    show ?case
    proof (rule_tac x="max B1 B2" in exI, clarsimp simp add: max.strict_coboundedI1 B1)
      fix a b
      assume "ball 0 (max B1 B2) \<subseteq> cbox a (b::'n)"
      then have *: "ball 0 B1 \<subseteq> cbox a (b::'n)" "ball 0 B2 \<subseteq> cbox a (b::'n)"
        by auto
      obtain w where w:
        "((\<lambda>x. if x \<in> s then f x else 0) has_integral w) (cbox a b)"
        "norm (w - k) < e / 2"
        using B1(2)[OF *(1)] by blast
      obtain z where z:
        "((\<lambda>x. if x \<in> s then g x else 0) has_integral z) (cbox a b)"
        "norm (z - l) < e / 2"
        using B2(2)[OF *(2)] by blast
      have *: "\<And>x. (if x \<in> s then f x + g x else 0) =
        (if x \<in> s then f x else 0) + (if x \<in> s then g x else 0)"
        by auto
      show "\<exists>z. ((\<lambda>x. if x \<in> s then f x + g x else 0) has_integral z) (cbox a b) \<and> norm (z - (k + l)) < e"
        apply (rule_tac x="w + z" in exI)
        apply (simp add: lem[OF w(1) z(1), unfolded *[symmetric]])
        using norm_triangle_ineq[of "w - k" "z - l"] w(2) z(2)
        apply (auto simp add: field_simps)
        done
    qed
  qed
qed

lemma has_integral_sub:
  "(f has_integral k) s \<Longrightarrow> (g has_integral l) s \<Longrightarrow>
    ((\<lambda>x. f x - g x) has_integral (k - l)) s"
  using has_integral_add[OF _ has_integral_neg, of f k s g l]
  by (auto simp: algebra_simps)

lemma integral_0 [simp]:
  "integral s (\<lambda>x::'n::euclidean_space. 0::'m::real_normed_vector) = 0"
  by (rule integral_unique has_integral_0)+

lemma integral_add: "f integrable_on s \<Longrightarrow> g integrable_on s \<Longrightarrow>
    integral s (\<lambda>x. f x + g x) = integral s f + integral s g"
  by (rule integral_unique) (metis integrable_integral has_integral_add)

lemma integral_cmul [simp]: "integral s (\<lambda>x. c *\<^sub>R f x) = c *\<^sub>R integral s f"
proof (cases "f integrable_on s \<or> c = 0")
  case True with has_integral_cmul show ?thesis by force
next
  case False then have "~ (\<lambda>x. c *\<^sub>R f x) integrable_on s"
    using has_integral_cmul [of "(\<lambda>x. c *\<^sub>R f x)" _ s "inverse c"]
    by force
  with False show ?thesis by (simp add: not_integrable_integral)
qed

lemma integral_neg [simp]: "integral s (\<lambda>x. - f x) = - integral s f"
proof (cases "f integrable_on s")
  case True then show ?thesis
    by (simp add: has_integral_neg integrable_integral integral_unique)
next
  case False then have "~ (\<lambda>x. - f x) integrable_on s"
    using has_integral_neg [of "(\<lambda>x. - f x)" _ s ]
    by force
  with False show ?thesis by (simp add: not_integrable_integral)
qed

lemma integral_diff: "f integrable_on s \<Longrightarrow> g integrable_on s \<Longrightarrow>
    integral s (\<lambda>x. f x - g x) = integral s f - integral s g"
  by (rule integral_unique) (metis integrable_integral has_integral_sub)

lemma integrable_0: "(\<lambda>x. 0) integrable_on s"
  unfolding integrable_on_def using has_integral_0 by auto

lemma integrable_add: "f integrable_on s \<Longrightarrow> g integrable_on s \<Longrightarrow> (\<lambda>x. f x + g x) integrable_on s"
  unfolding integrable_on_def by(auto intro: has_integral_add)

lemma integrable_cmul: "f integrable_on s \<Longrightarrow> (\<lambda>x. c *\<^sub>R f(x)) integrable_on s"
  unfolding integrable_on_def by(auto intro: has_integral_cmul)

lemma integrable_on_cmult_iff:
  fixes c :: real
  assumes "c \<noteq> 0"
  shows "(\<lambda>x. c * f x) integrable_on s \<longleftrightarrow> f integrable_on s"
  using integrable_cmul[of "\<lambda>x. c * f x" s "1 / c"] integrable_cmul[of f s c] \<open>c \<noteq> 0\<close>
  by auto

lemma integrable_on_cmult_left:
  assumes "f integrable_on s"
  shows "(\<lambda>x. of_real c * f x) integrable_on s"
    using integrable_cmul[of f s "of_real c"] assms
    by (simp add: scaleR_conv_of_real)

lemma integrable_neg: "f integrable_on s \<Longrightarrow> (\<lambda>x. -f(x)) integrable_on s"
  unfolding integrable_on_def by(auto intro: has_integral_neg)

lemma integrable_diff:
  "f integrable_on s \<Longrightarrow> g integrable_on s \<Longrightarrow> (\<lambda>x. f x - g x) integrable_on s"
  unfolding integrable_on_def by(auto intro: has_integral_sub)

lemma integrable_linear:
  "f integrable_on s \<Longrightarrow> bounded_linear h \<Longrightarrow> (h \<circ> f) integrable_on s"
  unfolding integrable_on_def by(auto intro: has_integral_linear)

lemma integral_linear:
  "f integrable_on s \<Longrightarrow> bounded_linear h \<Longrightarrow> integral s (h \<circ> f) = h (integral s f)"
  apply (rule has_integral_unique [where i=s and f = "h \<circ> f"])
  apply (simp_all add: integrable_integral integrable_linear has_integral_linear )
  done

lemma integral_component_eq[simp]:
  fixes f :: "'n::euclidean_space \<Rightarrow> 'm::euclidean_space"
  assumes "f integrable_on s"
  shows "integral s (\<lambda>x. f x \<bullet> k) = integral s f \<bullet> k"
  unfolding integral_linear[OF assms(1) bounded_linear_inner_left,unfolded o_def] ..

lemma has_integral_setsum:
  assumes "finite t"
    and "\<forall>a\<in>t. ((f a) has_integral (i a)) s"
  shows "((\<lambda>x. setsum (\<lambda>a. f a x) t) has_integral (setsum i t)) s"
  using assms(1) subset_refl[of t]
proof (induct rule: finite_subset_induct)
  case empty
  then show ?case by auto
next
  case (insert x F)
  with assms show ?case
    by (simp add: has_integral_add)
qed

lemma integral_setsum:
  "\<lbrakk>finite t;  \<forall>a\<in>t. (f a) integrable_on s\<rbrakk> \<Longrightarrow>
   integral s (\<lambda>x. setsum (\<lambda>a. f a x) t) = setsum (\<lambda>a. integral s (f a)) t"
  by (auto intro: has_integral_setsum integrable_integral)

lemma integrable_setsum:
  "\<lbrakk>finite t;  \<forall>a\<in>t. (f a) integrable_on s\<rbrakk> \<Longrightarrow> (\<lambda>x. setsum (\<lambda>a. f a x) t) integrable_on s"
  unfolding integrable_on_def
  apply (drule bchoice)
  using has_integral_setsum[of t]
  apply auto
  done

lemma has_integral_eq:
  assumes "\<And>x. x \<in> s \<Longrightarrow> f x = g x"
    and "(f has_integral k) s"
  shows "(g has_integral k) s"
  using has_integral_sub[OF assms(2), of "\<lambda>x. f x - g x" 0]
  using has_integral_is_0[of s "\<lambda>x. f x - g x"]
  using assms(1)
  by auto

lemma integrable_eq: "(\<And>x. x \<in> s \<Longrightarrow> f x = g x) \<Longrightarrow> f integrable_on s \<Longrightarrow> g integrable_on s"
  unfolding integrable_on_def
  using has_integral_eq[of s f g] has_integral_eq by blast

lemma has_integral_cong:
  assumes "\<And>x. x \<in> s \<Longrightarrow> f x = g x"
  shows "(f has_integral i) s = (g has_integral i) s"
  using has_integral_eq[of s f g] has_integral_eq[of s g f] assms
  by auto

lemma integral_cong:
  assumes "\<And>x. x \<in> s \<Longrightarrow> f x = g x"
  shows "integral s f = integral s g"
  unfolding integral_def
by (metis (full_types, hide_lams) assms has_integral_cong integrable_eq)

lemma integrable_on_cmult_left_iff [simp]:
  assumes "c \<noteq> 0"
  shows "(\<lambda>x. of_real c * f x) integrable_on s \<longleftrightarrow> f integrable_on s"
        (is "?lhs = ?rhs")
proof
  assume ?lhs
  then have "(\<lambda>x. of_real (1 / c) * (of_real c * f x)) integrable_on s"
    using integrable_cmul[of "\<lambda>x. of_real c * f x" s "1 / of_real c"]
    by (simp add: scaleR_conv_of_real)
  then have "(\<lambda>x. (of_real (1 / c) * of_real c * f x)) integrable_on s"
    by (simp add: algebra_simps)
  with \<open>c \<noteq> 0\<close> show ?rhs
    by (metis (no_types, lifting) integrable_eq mult.left_neutral nonzero_divide_eq_eq of_real_1 of_real_mult)
qed (blast intro: integrable_on_cmult_left)

lemma integrable_on_cmult_right:
  fixes f :: "_ \<Rightarrow> 'b :: {comm_ring,real_algebra_1,real_normed_vector}"
  assumes "f integrable_on s"
  shows "(\<lambda>x. f x * of_real c) integrable_on s"
using integrable_on_cmult_left [OF assms] by (simp add: mult.commute)

lemma integrable_on_cmult_right_iff [simp]:
  fixes f :: "_ \<Rightarrow> 'b :: {comm_ring,real_algebra_1,real_normed_vector}"
  assumes "c \<noteq> 0"
  shows "(\<lambda>x. f x * of_real c) integrable_on s \<longleftrightarrow> f integrable_on s"
using integrable_on_cmult_left_iff [OF assms] by (simp add: mult.commute)

lemma integrable_on_cdivide:
  fixes f :: "_ \<Rightarrow> 'b :: real_normed_field"
  assumes "f integrable_on s"
  shows "(\<lambda>x. f x / of_real c) integrable_on s"
by (simp add: integrable_on_cmult_right divide_inverse assms of_real_inverse [symmetric] del: of_real_inverse)

lemma integrable_on_cdivide_iff [simp]:
  fixes f :: "_ \<Rightarrow> 'b :: real_normed_field"
  assumes "c \<noteq> 0"
  shows "(\<lambda>x. f x / of_real c) integrable_on s \<longleftrightarrow> f integrable_on s"
by (simp add: divide_inverse assms of_real_inverse [symmetric] del: of_real_inverse)

lemma has_integral_null [intro]:
  assumes "content(cbox a b) = 0"
  shows "(f has_integral 0) (cbox a b)"
proof -
  have "gauge (\<lambda>x. ball x 1)"
    by auto
  moreover
  {
    fix e :: real
    fix p
    assume e: "e > 0"
    assume p: "p tagged_division_of (cbox a b)"
    have "norm ((\<Sum>(x, k)\<in>p. content k *\<^sub>R f x) - 0) = 0"
      unfolding norm_eq_zero diff_0_right
      using setsum_content_null[OF assms(1) p, of f] .
    then have "norm ((\<Sum>(x, k)\<in>p. content k *\<^sub>R f x) - 0) < e"
      using e by auto
  }
  ultimately show ?thesis
    by (auto simp: has_integral)
qed

lemma has_integral_null_real [intro]:
  assumes "content {a .. b::real} = 0"
  shows "(f has_integral 0) {a .. b}"
  by (metis assms box_real(2) has_integral_null)

lemma has_integral_null_eq[simp]: "content (cbox a b) = 0 \<Longrightarrow> (f has_integral i) (cbox a b) \<longleftrightarrow> i = 0"
  by (auto simp add: has_integral_null dest!: integral_unique)

lemma integral_null [simp]: "content (cbox a b) = 0 \<Longrightarrow> integral (cbox a b) f = 0"
  by (metis has_integral_null integral_unique)

lemma integrable_on_null [intro]: "content (cbox a b) = 0 \<Longrightarrow> f integrable_on (cbox a b)"
  by (simp add: has_integral_integrable)

lemma has_integral_empty[intro]: "(f has_integral 0) {}"
  by (simp add: has_integral_is_0)

lemma has_integral_empty_eq[simp]: "(f has_integral i) {} \<longleftrightarrow> i = 0"
  by (auto simp add: has_integral_empty has_integral_unique)

lemma integrable_on_empty[intro]: "f integrable_on {}"
  unfolding integrable_on_def by auto

lemma integral_empty[simp]: "integral {} f = 0"
  by (rule integral_unique) (rule has_integral_empty)

lemma has_integral_refl[intro]:
  fixes a :: "'a::euclidean_space"
  shows "(f has_integral 0) (cbox a a)"
    and "(f has_integral 0) {a}"
proof -
  have *: "{a} = cbox a a"
    apply (rule set_eqI)
    unfolding mem_box singleton_iff euclidean_eq_iff[where 'a='a]
    apply safe
    prefer 3
    apply (erule_tac x=b in ballE)
    apply (auto simp add: field_simps)
    done
  show "(f has_integral 0) (cbox a a)" "(f has_integral 0) {a}"
    unfolding *
    apply (rule_tac[!] has_integral_null)
    unfolding content_eq_0_interior
    unfolding interior_cbox
    using box_sing
    apply auto
    done
qed

lemma integrable_on_refl[intro]: "f integrable_on cbox a a"
  unfolding integrable_on_def by auto

lemma integral_refl [simp]: "integral (cbox a a) f = 0"
  by (rule integral_unique) auto

lemma integral_singleton [simp]: "integral {a} f = 0"
  by auto

lemma integral_blinfun_apply:
  assumes "f integrable_on s"
  shows "integral s (\<lambda>x. blinfun_apply h (f x)) = blinfun_apply h (integral s f)"
  by (subst integral_linear[symmetric, OF assms blinfun.bounded_linear_right]) (simp add: o_def)

lemma blinfun_apply_integral:
  assumes "f integrable_on s"
  shows "blinfun_apply (integral s f) x = integral s (\<lambda>y. blinfun_apply (f y) x)"
  by (metis (no_types, lifting) assms blinfun.prod_left.rep_eq integral_blinfun_apply integral_cong)

lemma has_integral_componentwise_iff:
  fixes f :: "'a :: euclidean_space \<Rightarrow> 'b :: euclidean_space"
  shows "(f has_integral y) A \<longleftrightarrow> (\<forall>b\<in>Basis. ((\<lambda>x. f x \<bullet> b) has_integral (y \<bullet> b)) A)"
proof safe
  fix b :: 'b assume "(f has_integral y) A"
  from has_integral_linear[OF this(1) bounded_linear_inner_left, of b]
    show "((\<lambda>x. f x \<bullet> b) has_integral (y \<bullet> b)) A" by (simp add: o_def)
next
  assume "(\<forall>b\<in>Basis. ((\<lambda>x. f x \<bullet> b) has_integral (y \<bullet> b)) A)"
  hence "\<forall>b\<in>Basis. (((\<lambda>x. x *\<^sub>R b) \<circ> (\<lambda>x. f x \<bullet> b)) has_integral ((y \<bullet> b) *\<^sub>R b)) A"
    by (intro ballI has_integral_linear) (simp_all add: bounded_linear_scaleR_left)
  hence "((\<lambda>x. \<Sum>b\<in>Basis. (f x \<bullet> b) *\<^sub>R b) has_integral (\<Sum>b\<in>Basis. (y \<bullet> b) *\<^sub>R b)) A"
    by (intro has_integral_setsum) (simp_all add: o_def)
  thus "(f has_integral y) A" by (simp add: euclidean_representation)
qed

lemma has_integral_componentwise:
  fixes f :: "'a :: euclidean_space \<Rightarrow> 'b :: euclidean_space"
  shows "(\<And>b. b \<in> Basis \<Longrightarrow> ((\<lambda>x. f x \<bullet> b) has_integral (y \<bullet> b)) A) \<Longrightarrow> (f has_integral y) A"
  by (subst has_integral_componentwise_iff) blast

lemma integrable_componentwise_iff:
  fixes f :: "'a :: euclidean_space \<Rightarrow> 'b :: euclidean_space"
  shows "f integrable_on A \<longleftrightarrow> (\<forall>b\<in>Basis. (\<lambda>x. f x \<bullet> b) integrable_on A)"
proof
  assume "f integrable_on A"
  then obtain y where "(f has_integral y) A" by (auto simp: integrable_on_def)
  hence "(\<forall>b\<in>Basis. ((\<lambda>x. f x \<bullet> b) has_integral (y \<bullet> b)) A)"
    by (subst (asm) has_integral_componentwise_iff)
  thus "(\<forall>b\<in>Basis. (\<lambda>x. f x \<bullet> b) integrable_on A)" by (auto simp: integrable_on_def)
next
  assume "(\<forall>b\<in>Basis. (\<lambda>x. f x \<bullet> b) integrable_on A)"
  then obtain y where "\<forall>b\<in>Basis. ((\<lambda>x. f x \<bullet> b) has_integral y b) A"
    unfolding integrable_on_def by (subst (asm) bchoice_iff) blast
  hence "\<forall>b\<in>Basis. (((\<lambda>x. x *\<^sub>R b) \<circ> (\<lambda>x. f x \<bullet> b)) has_integral (y b *\<^sub>R b)) A"
    by (intro ballI has_integral_linear) (simp_all add: bounded_linear_scaleR_left)
  hence "((\<lambda>x. \<Sum>b\<in>Basis. (f x \<bullet> b) *\<^sub>R b) has_integral (\<Sum>b\<in>Basis. y b *\<^sub>R b)) A"
    by (intro has_integral_setsum) (simp_all add: o_def)
  thus "f integrable_on A" by (auto simp: integrable_on_def o_def euclidean_representation)
qed

lemma integrable_componentwise:
  fixes f :: "'a :: euclidean_space \<Rightarrow> 'b :: euclidean_space"
  shows "(\<And>b. b \<in> Basis \<Longrightarrow> (\<lambda>x. f x \<bullet> b) integrable_on A) \<Longrightarrow> f integrable_on A"
  by (subst integrable_componentwise_iff) blast

lemma integral_componentwise:
  fixes f :: "'a :: euclidean_space \<Rightarrow> 'b :: euclidean_space"
  assumes "f integrable_on A"
  shows "integral A f = (\<Sum>b\<in>Basis. integral A (\<lambda>x. (f x \<bullet> b) *\<^sub>R b))"
proof -
  from assms have integrable: "\<forall>b\<in>Basis. (\<lambda>x. x *\<^sub>R b) \<circ> (\<lambda>x. (f x \<bullet> b)) integrable_on A"
    by (subst (asm) integrable_componentwise_iff, intro integrable_linear ballI)
       (simp_all add: bounded_linear_scaleR_left)
  have "integral A f = integral A (\<lambda>x. \<Sum>b\<in>Basis. (f x \<bullet> b) *\<^sub>R b)"
    by (simp add: euclidean_representation)
  also from integrable have "\<dots> = (\<Sum>a\<in>Basis. integral A (\<lambda>x. (f x \<bullet> a) *\<^sub>R a))"
    by (subst integral_setsum) (simp_all add: o_def)
  finally show ?thesis .
qed

lemma integrable_component:
  "f integrable_on A \<Longrightarrow> (\<lambda>x. f x \<bullet> (y :: 'b :: euclidean_space)) integrable_on A"
  by (drule integrable_linear[OF _ bounded_linear_inner_left[of y]]) (simp add: o_def)



subsection \<open>Cauchy-type criterion for integrability.\<close>

(* XXXXXXX *)
lemma integrable_cauchy:
  fixes f :: "'n::euclidean_space \<Rightarrow> 'a::{real_normed_vector,complete_space}"
  shows "f integrable_on cbox a b \<longleftrightarrow>
    (\<forall>e>0.\<exists>d. gauge d \<and>
      (\<forall>p1 p2. p1 tagged_division_of (cbox a b) \<and> d fine p1 \<and>
        p2 tagged_division_of (cbox a b) \<and> d fine p2 \<longrightarrow>
        norm (setsum (\<lambda>(x,k). content k *\<^sub>R f x) p1 -
        setsum (\<lambda>(x,k). content k *\<^sub>R f x) p2) < e))"
  (is "?l = (\<forall>e>0. \<exists>d. ?P e d)")
proof
  assume ?l
  then guess y unfolding integrable_on_def has_integral .. note y=this
  show "\<forall>e>0. \<exists>d. ?P e d"
  proof (clarify, goal_cases)
    case (1 e)
    then have "e/2 > 0" by auto
    then guess d
      apply -
      apply (drule y[rule_format])
      apply (elim exE conjE)
      done
    note d=this[rule_format]
    show ?case
    proof (rule_tac x=d in exI, clarsimp simp: d)
      fix p1 p2
      assume as: "p1 tagged_division_of (cbox a b)" "d fine p1"
                 "p2 tagged_division_of (cbox a b)" "d fine p2"
      show "norm ((\<Sum>(x, k)\<in>p1. content k *\<^sub>R f x) - (\<Sum>(x, k)\<in>p2. content k *\<^sub>R f x)) < e"
        apply (rule dist_triangle_half_l[where y=y,unfolded dist_norm])
        using d(2)[OF conjI[OF as(1-2)]] d(2)[OF conjI[OF as(3-4)]] .
    qed
  qed
next
  assume "\<forall>e>0. \<exists>d. ?P e d"
  then have "\<forall>n::nat. \<exists>d. ?P (inverse(of_nat (n + 1))) d"
    by auto
  from choice[OF this] guess d .. note d=conjunctD2[OF this[rule_format],rule_format]
  have "\<And>n. gauge (\<lambda>x. \<Inter>{d i x |i. i \<in> {0..n}})"
    apply (rule gauge_inters)
    using d(1)
    apply auto
    done
  then have "\<forall>n. \<exists>p. p tagged_division_of (cbox a b) \<and> (\<lambda>x. \<Inter>{d i x |i. i \<in> {0..n}}) fine p"
    by (meson fine_division_exists)
  from choice[OF this] guess p .. note p = conjunctD2[OF this[rule_format]]
  have dp: "\<And>i n. i\<le>n \<Longrightarrow> d i fine p n"
    using p(2) unfolding fine_inters by auto
  have "Cauchy (\<lambda>n. setsum (\<lambda>(x,k). content k *\<^sub>R (f x)) (p n))"
  proof (rule CauchyI, goal_cases)
    case (1 e)
    then guess N unfolding real_arch_inverse[of e] .. note N=this
    show ?case
      apply (rule_tac x=N in exI)
    proof clarify
      fix m n
      assume mn: "N \<le> m" "N \<le> n"
      have *: "N = (N - 1) + 1" using N by auto
      show "norm ((\<Sum>(x, k)\<in>p m. content k *\<^sub>R f x) - (\<Sum>(x, k)\<in>p n. content k *\<^sub>R f x)) < e"
        apply (rule less_trans[OF _ N[THEN conjunct2,THEN conjunct2]])
        apply(subst *)
        using dp p(1) mn d(2) by auto
    qed
  qed
  then guess y unfolding convergent_eq_cauchy[symmetric] .. note y=this[THEN LIMSEQ_D]
  show ?l
    unfolding integrable_on_def has_integral
  proof (rule_tac x=y in exI, clarify)
    fix e :: real
    assume "e>0"
    then have *:"e/2 > 0" by auto
    then guess N1 unfolding real_arch_inverse[of "e/2"] .. note N1=this
    then have N1': "N1 = N1 - 1 + 1"
      by auto
    guess N2 using y[OF *] .. note N2=this
    have "gauge (d (N1 + N2))"
      using d by auto
    moreover
    {
      fix q
      assume as: "q tagged_division_of (cbox a b)" "d (N1 + N2) fine q"
      have *: "inverse (of_nat (N1 + N2 + 1)) < e / 2"
        apply (rule less_trans)
        using N1
        apply auto
        done
      have "norm ((\<Sum>(x, k)\<in>q. content k *\<^sub>R f x) - y) < e"
        apply (rule norm_triangle_half_r)
        apply (rule less_trans[OF _ *])
        apply (subst N1', rule d(2)[of "p (N1+N2)"])
        using N1' as(1) as(2) dp
        apply (simp add: \<open>\<forall>x. p x tagged_division_of cbox a b \<and> (\<lambda>xa. \<Inter>{d i xa |i. i \<in> {0..x}}) fine p x\<close>)
        using N2 le_add2 by blast
    }
    ultimately show "\<exists>d. gauge d \<and>
      (\<forall>p. p tagged_division_of (cbox a b) \<and> d fine p \<longrightarrow>
        norm ((\<Sum>(x, k)\<in>p. content k *\<^sub>R f x) - y) < e)"
      by (rule_tac x="d (N1 + N2)" in exI) auto
  qed
qed


subsection \<open>Additivity of integral on abutting intervals.\<close>

lemma tagged_division_split_left_inj:
  fixes x1 :: "'a::euclidean_space"
  assumes d: "d tagged_division_of i"
    and k12: "(x1, k1) \<in> d"
             "(x2, k2) \<in> d"
             "k1 \<noteq> k2"
             "k1 \<inter> {x. x\<bullet>k \<le> c} = k2 \<inter> {x. x\<bullet>k \<le> c}"
             "k \<in> Basis"
  shows "content (k1 \<inter> {x. x\<bullet>k \<le> c}) = 0"
proof -
  have *: "\<And>a b c. (a,b) \<in> c \<Longrightarrow> b \<in> snd ` c"
    by force
  show ?thesis
    using k12
    by (fastforce intro!:  division_split_left_inj[OF division_of_tagged_division[OF d]] *)
qed

lemma tagged_division_split_right_inj:
  fixes x1 :: "'a::euclidean_space"
  assumes d: "d tagged_division_of i"
    and k12: "(x1, k1) \<in> d"
             "(x2, k2) \<in> d"
             "k1 \<noteq> k2"
             "k1 \<inter> {x. x\<bullet>k \<ge> c} = k2 \<inter> {x. x\<bullet>k \<ge> c}"
             "k \<in> Basis"
  shows "content (k1 \<inter> {x. x\<bullet>k \<ge> c}) = 0"
proof -
  have *: "\<And>a b c. (a,b) \<in> c \<Longrightarrow> b \<in> snd ` c"
    by force
  show ?thesis
    using k12
    by (fastforce intro!:  division_split_right_inj[OF division_of_tagged_division[OF d]] *)
qed

lemma has_integral_split:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::real_normed_vector"
  assumes fi: "(f has_integral i) (cbox a b \<inter> {x. x\<bullet>k \<le> c})"
      and fj: "(f has_integral j) (cbox a b \<inter> {x. x\<bullet>k \<ge> c})"
      and k: "k \<in> Basis"
  shows "(f has_integral (i + j)) (cbox a b)"
proof (unfold has_integral, rule, rule, goal_cases)
  case (1 e)
  then have e: "e/2 > 0"
    by auto
    obtain d1
    where d1: "gauge d1"
      and d1norm:
        "\<And>p. \<lbrakk>p tagged_division_of cbox a b \<inter> {x. x \<bullet> k \<le> c};
               d1 fine p\<rbrakk> \<Longrightarrow> norm ((\<Sum>(x, k) \<in> p. content k *\<^sub>R f x) - i) < e / 2"
       apply (rule has_integralD[OF fi[unfolded interval_split[OF k]] e])
       apply (simp add: interval_split[symmetric] k)
       done
    obtain d2
    where d2: "gauge d2"
      and d2norm:
        "\<And>p. \<lbrakk>p tagged_division_of cbox a b \<inter> {x. c \<le> x \<bullet> k};
               d2 fine p\<rbrakk> \<Longrightarrow> norm ((\<Sum>(x, k) \<in> p. content k *\<^sub>R f x) - j) < e / 2"
       apply (rule has_integralD[OF fj[unfolded interval_split[OF k]] e])
       apply (simp add: interval_split[symmetric] k)
       done
  let ?d = "\<lambda>x. if x\<bullet>k = c then (d1 x \<inter> d2 x) else ball x \<bar>x\<bullet>k - c\<bar> \<inter> d1 x \<inter> d2 x"
  have "gauge ?d"
    using d1 d2 unfolding gauge_def by auto
  then show ?case
  proof (rule_tac x="?d" in exI, safe)
    fix p
    assume "p tagged_division_of (cbox a b)" "?d fine p"
    note p = this tagged_division_ofD[OF this(1)]
    have xk_le_c: "\<And>x kk. (x, kk) \<in> p \<Longrightarrow> kk \<inter> {x. x\<bullet>k \<le> c} \<noteq> {} \<Longrightarrow> x\<bullet>k \<le> c"
    proof -
      fix x kk
      assume as: "(x, kk) \<in> p" and kk: "kk \<inter> {x. x\<bullet>k \<le> c} \<noteq> {}"
      show "x\<bullet>k \<le> c"
      proof (rule ccontr)
        assume **: "\<not> ?thesis"
        from this[unfolded not_le]
        have "kk \<subseteq> ball x \<bar>x \<bullet> k - c\<bar>"
          using p(2)[unfolded fine_def, rule_format,OF as] by auto
        with kk obtain y where y: "y \<in> ball x \<bar>x \<bullet> k - c\<bar>" "y\<bullet>k \<le> c"
          by blast
        then have "\<bar>x \<bullet> k - y \<bullet> k\<bar> < \<bar>x \<bullet> k - c\<bar>"
          using Basis_le_norm[OF k, of "x - y"]
          by (auto simp add: dist_norm inner_diff_left intro: le_less_trans)
        with y show False
          using ** by (auto simp add: field_simps)
      qed
    qed
    have xk_ge_c: "\<And>x kk. (x, kk) \<in> p \<Longrightarrow> kk \<inter> {x. x\<bullet>k \<ge> c} \<noteq> {} \<Longrightarrow> x\<bullet>k \<ge> c"
    proof -
      fix x kk
      assume as: "(x, kk) \<in> p" and kk: "kk \<inter> {x. x\<bullet>k \<ge> c} \<noteq> {}"
      show "x\<bullet>k \<ge> c"
      proof (rule ccontr)
        assume **: "\<not> ?thesis"
        from this[unfolded not_le] have "kk \<subseteq> ball x \<bar>x \<bullet> k - c\<bar>"
          using p(2)[unfolded fine_def,rule_format,OF as,unfolded split_conv] by auto
        with kk obtain y where y: "y \<in> ball x \<bar>x \<bullet> k - c\<bar>" "y\<bullet>k \<ge> c"
          by blast
        then have "\<bar>x \<bullet> k - y \<bullet> k\<bar> < \<bar>x \<bullet> k - c\<bar>"
          using Basis_le_norm[OF k, of "x - y"]
          by (auto simp add: dist_norm inner_diff_left intro: le_less_trans)
        with y show False
          using ** by (auto simp add: field_simps)
      qed
    qed

    have lem1: "\<And>f P Q. (\<forall>x k. (x, k) \<in> {(x, f k) | x k. P x k} \<longrightarrow> Q x k) \<longleftrightarrow>
                         (\<forall>x k. P x k \<longrightarrow> Q x (f k))"
      by auto
    have fin_finite: "finite {(x,f k) | x k. (x,k) \<in> s \<and> P x k}" if "finite s" for f s P
    proof -
      from that have "finite ((\<lambda>(x, k). (x, f k)) ` s)"
        by auto
      then show ?thesis
        by (rule rev_finite_subset) auto
    qed
    { fix g :: "'a set \<Rightarrow> 'a set"
      fix i :: "'a \<times> 'a set"
      assume "i \<in> (\<lambda>(x, k). (x, g k)) ` p - {(x, g k) |x k. (x, k) \<in> p \<and> g k \<noteq> {}}"
      then obtain x k where xk:
              "i = (x, g k)"  "(x, k) \<in> p"
              "(x, g k) \<notin> {(x, g k) |x k. (x, k) \<in> p \<and> g k \<noteq> {}}"
          by auto
      have "content (g k) = 0"
        using xk using content_empty by auto
      then have "(\<lambda>(x, k). content k *\<^sub>R f x) i = 0"
        unfolding xk split_conv by auto
    } note [simp] = this
    have lem3: "\<And>g :: 'a set \<Rightarrow> 'a set. finite p \<Longrightarrow>
                  setsum (\<lambda>(x, k). content k *\<^sub>R f x) {(x,g k) |x k. (x,k) \<in> p \<and> g k \<noteq> {}} =
                  setsum (\<lambda>(x, k). content k *\<^sub>R f x) ((\<lambda>(x, k). (x, g k)) ` p)"
      by (rule setsum.mono_neutral_left) auto
    let ?M1 = "{(x, kk \<inter> {x. x\<bullet>k \<le> c}) |x kk. (x, kk) \<in> p \<and> kk \<inter> {x. x\<bullet>k \<le> c} \<noteq> {}}"
    have d1_fine: "d1 fine ?M1"
      by (force intro: fineI dest: fineD[OF p(2)] simp add: split: if_split_asm)
    have "norm ((\<Sum>(x, k)\<in>?M1. content k *\<^sub>R f x) - i) < e/2"
    proof (rule d1norm [OF tagged_division_ofI d1_fine])
      show "finite ?M1"
        by (rule fin_finite p(3))+
      show "\<Union>{k. \<exists>x. (x, k) \<in> ?M1} = cbox a b \<inter> {x. x\<bullet>k \<le> c}"
        unfolding p(8)[symmetric] by auto
      fix x l
      assume xl: "(x, l) \<in> ?M1"
      then guess x' l' unfolding mem_Collect_eq unfolding prod.inject by (elim exE conjE) note xl'=this
      show "x \<in> l" "l \<subseteq> cbox a b \<inter> {x. x \<bullet> k \<le> c}"
        unfolding xl'
        using p(4-6)[OF xl'(3)] using xl'(4)
        using xk_le_c[OF xl'(3-4)] by auto
      show "\<exists>a b. l = cbox a b"
        unfolding xl'
        using p(6)[OF xl'(3)]
        by (fastforce simp add: interval_split[OF k,where c=c])
      fix y r
      let ?goal = "interior l \<inter> interior r = {}"
      assume yr: "(y, r) \<in> ?M1"
      then guess y' r' unfolding mem_Collect_eq unfolding prod.inject by (elim exE conjE) note yr'=this
      assume as: "(x, l) \<noteq> (y, r)"
      show "interior l \<inter> interior r = {}"
      proof (cases "l' = r' \<longrightarrow> x' = y'")
        case False
        then show ?thesis
          using p(7)[OF xl'(3) yr'(3)] using as unfolding xl' yr' by auto
      next
        case True
        then have "l' \<noteq> r'"
          using as unfolding xl' yr' by auto
        then show ?thesis
          using p(7)[OF xl'(3) yr'(3)] using as unfolding xl' yr' by auto
      qed
    qed
    moreover
    let ?M2 = "{(x,kk \<inter> {x. x\<bullet>k \<ge> c}) |x kk. (x,kk) \<in> p \<and> kk \<inter> {x. x\<bullet>k \<ge> c} \<noteq> {}}"
    have d2_fine: "d2 fine ?M2"
      by (force intro: fineI dest: fineD[OF p(2)] simp add: split: if_split_asm)
    have "norm ((\<Sum>(x, k)\<in>?M2. content k *\<^sub>R f x) - j) < e/2"
    proof (rule d2norm [OF tagged_division_ofI d2_fine])
      show "finite ?M2"
        by (rule fin_finite p(3))+
      show "\<Union>{k. \<exists>x. (x, k) \<in> ?M2} = cbox a b \<inter> {x. x\<bullet>k \<ge> c}"
        unfolding p(8)[symmetric] by auto
      fix x l
      assume xl: "(x, l) \<in> ?M2"
      then guess x' l' unfolding mem_Collect_eq unfolding prod.inject by (elim exE conjE) note xl'=this
      show "x \<in> l" "l \<subseteq> cbox a b \<inter> {x. x \<bullet> k \<ge> c}"
        unfolding xl'
        using p(4-6)[OF xl'(3)] xl'(4) xk_ge_c[OF xl'(3-4)]
        by auto
      show "\<exists>a b. l = cbox a b"
        unfolding xl'
        using p(6)[OF xl'(3)]
        by (fastforce simp add: interval_split[OF k, where c=c])
      fix y r
      let ?goal = "interior l \<inter> interior r = {}"
      assume yr: "(y, r) \<in> ?M2"
      then guess y' r' unfolding mem_Collect_eq unfolding prod.inject by (elim exE conjE) note yr'=this
      assume as: "(x, l) \<noteq> (y, r)"
      show "interior l \<inter> interior r = {}"
      proof (cases "l' = r' \<longrightarrow> x' = y'")
        case False
        then show ?thesis
          using p(7)[OF xl'(3) yr'(3)] using as unfolding xl' yr' by auto
      next
        case True
        then have "l' \<noteq> r'"
          using as unfolding xl' yr' by auto
        then show ?thesis
          using p(7)[OF xl'(3) yr'(3)] using as unfolding xl' yr' by auto
      qed
    qed
    ultimately
    have "norm (((\<Sum>(x, k)\<in>?M1. content k *\<^sub>R f x) - i) + ((\<Sum>(x, k)\<in>?M2. content k *\<^sub>R f x) - j)) < e/2 + e/2"
      using norm_add_less by blast
    also {
      have eq0: "\<And>x y. x = (0::real) \<Longrightarrow> x *\<^sub>R (y::'b) = 0"
        using scaleR_zero_left by auto
      have cont_eq: "\<And>g. (\<lambda>(x,l). content l *\<^sub>R f x) \<circ> (\<lambda>(x,l). (x,g l)) = (\<lambda>(x,l). content (g l) *\<^sub>R f x)"
        by auto
      have "((\<Sum>(x, k)\<in>?M1. content k *\<^sub>R f x) - i) + ((\<Sum>(x, k)\<in>?M2. content k *\<^sub>R f x) - j) =
        (\<Sum>(x, k)\<in>?M1. content k *\<^sub>R f x) + (\<Sum>(x, k)\<in>?M2. content k *\<^sub>R f x) - (i + j)"
        by auto
      also have "\<dots> = (\<Sum>(x, ka)\<in>p. content (ka \<inter> {x. x \<bullet> k \<le> c}) *\<^sub>R f x) +
        (\<Sum>(x, ka)\<in>p. content (ka \<inter> {x. c \<le> x \<bullet> k}) *\<^sub>R f x) - (i + j)"
        unfolding lem3[OF p(3)]
        by (subst setsum.reindex_nontrivial[OF p(3)], auto intro!: k eq0 tagged_division_split_left_inj[OF p(1)] tagged_division_split_right_inj[OF p(1)]
              simp: cont_eq)+
      also note setsum.distrib[symmetric]
      also have "\<And>x. x \<in> p \<Longrightarrow>
                    (\<lambda>(x,ka). content (ka \<inter> {x. x \<bullet> k \<le> c}) *\<^sub>R f x) x +
                    (\<lambda>(x,ka). content (ka \<inter> {x. c \<le> x \<bullet> k}) *\<^sub>R f x) x =
                    (\<lambda>(x,ka). content ka *\<^sub>R f x) x"
      proof clarify
        fix a b
        assume "(a, b) \<in> p"
        from p(6)[OF this] guess u v by (elim exE) note uv=this
        then show "content (b \<inter> {x. x \<bullet> k \<le> c}) *\<^sub>R f a + content (b \<inter> {x. c \<le> x \<bullet> k}) *\<^sub>R f a =
          content b *\<^sub>R f a"
          unfolding scaleR_left_distrib[symmetric]
          unfolding uv content_split[OF k,of u v c]
          by auto
      qed
      note setsum.cong [OF _ this]
      finally have "(\<Sum>(x, k)\<in>{(x, kk \<inter> {x. x \<bullet> k \<le> c}) |x kk. (x, kk) \<in> p \<and> kk \<inter> {x. x \<bullet> k \<le> c} \<noteq> {}}. content k *\<^sub>R f x) - i +
        ((\<Sum>(x, k)\<in>{(x, kk \<inter> {x. c \<le> x \<bullet> k}) |x kk. (x, kk) \<in> p \<and> kk \<inter> {x. c \<le> x \<bullet> k} \<noteq> {}}. content k *\<^sub>R f x) - j) =
        (\<Sum>(x, ka)\<in>p. content ka *\<^sub>R f x) - (i + j)"
        by auto
    }
    finally show "norm ((\<Sum>(x, k)\<in>p. content k *\<^sub>R f x) - (i + j)) < e"
      by auto
  qed
qed


subsection \<open>A sort of converse, integrability on subintervals.\<close>

lemma tagged_division_union_interval:
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
    apply (rule tagged_division_union[OF assms(1-2)])
    unfolding interval_split[OF k] interior_cbox
    using k
    apply (auto simp add: box_def elim!: ballE[where x=k])
    done
qed

lemma tagged_division_union_interval_real:
  fixes a :: real
  assumes "p1 tagged_division_of ({a .. b} \<inter> {x. x\<bullet>k \<le> (c::real)})"
    and "p2 tagged_division_of ({a .. b} \<inter> {x. x\<bullet>k \<ge> c})"
    and k: "k \<in> Basis"
  shows "(p1 \<union> p2) tagged_division_of {a .. b}"
  using assms
  unfolding box_real[symmetric]
  by (rule tagged_division_union_interval)

lemma has_integral_separate_sides:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::real_normed_vector"
  assumes "(f has_integral i) (cbox a b)"
    and "e > 0"
    and k: "k \<in> Basis"
  obtains d where "gauge d"
    "\<forall>p1 p2. p1 tagged_division_of (cbox a b \<inter> {x. x\<bullet>k \<le> c}) \<and> d fine p1 \<and>
        p2 tagged_division_of (cbox a b \<inter> {x. x\<bullet>k \<ge> c}) \<and> d fine p2 \<longrightarrow>
        norm ((setsum (\<lambda>(x,k). content k *\<^sub>R f x) p1 + setsum (\<lambda>(x,k). content k *\<^sub>R f x) p2) - i) < e"
proof -
  guess d using has_integralD[OF assms(1-2)] . note d=this
  { fix p1 p2
    assume "p1 tagged_division_of (cbox a b) \<inter> {x. x \<bullet> k \<le> c}" "d fine p1"
    note p1=tagged_division_ofD[OF this(1)] this
    assume "p2 tagged_division_of (cbox a b) \<inter> {x. c \<le> x \<bullet> k}" "d fine p2"
    note p2=tagged_division_ofD[OF this(1)] this
    note tagged_division_union_interval[OF p1(7) p2(7)] note p12 = tagged_division_ofD[OF this] this
    { fix a b
      assume ab: "(a, b) \<in> p1 \<inter> p2"
      have "(a, b) \<in> p1"
        using ab by auto
      with p1 obtain u v where uv: "b = cbox u v" by auto
      have "b \<subseteq> {x. x\<bullet>k = c}"
        using ab p1(3)[of a b] p2(3)[of a b] by fastforce
      moreover
      have "interior {x::'a. x \<bullet> k = c} = {}"
      proof (rule ccontr)
        assume "\<not> ?thesis"
        then obtain x where x: "x \<in> interior {x::'a. x\<bullet>k = c}"
          by auto
        then guess e unfolding mem_interior .. note e=this
        have x: "x\<bullet>k = c"
          using x interior_subset by fastforce
        have *: "\<And>i. i \<in> Basis \<Longrightarrow> \<bar>(x - (x + (e / 2) *\<^sub>R k)) \<bullet> i\<bar> = (if i = k then e/2 else 0)"
          using e k by (auto simp: inner_simps inner_not_same_Basis)
        have "(\<Sum>i\<in>Basis. \<bar>(x - (x + (e / 2 ) *\<^sub>R k)) \<bullet> i\<bar>) =
              (\<Sum>i\<in>Basis. (if i = k then e / 2 else 0))"
          using "*" by (blast intro: setsum.cong)
        also have "\<dots> < e"
          apply (subst setsum.delta)
          using e
          apply auto
          done
        finally have "x + (e/2) *\<^sub>R k \<in> ball x e"
          unfolding mem_ball dist_norm by(rule le_less_trans[OF norm_le_l1])
        then have "x + (e/2) *\<^sub>R k \<in> {x. x\<bullet>k = c}"
          using e by auto
        then show False
          unfolding mem_Collect_eq using e x k by (auto simp: inner_simps)
      qed
      ultimately have "content b = 0"
        unfolding uv content_eq_0_interior
        using interior_mono by blast
      then have "content b *\<^sub>R f a = 0"
        by auto
    }
    then have "norm ((\<Sum>(x, k)\<in>p1. content k *\<^sub>R f x) + (\<Sum>(x, k)\<in>p2. content k *\<^sub>R f x) - i) =
               norm ((\<Sum>(x, k)\<in>p1 \<union> p2. content k *\<^sub>R f x) - i)"
      by (subst setsum.union_inter_neutral) (auto simp: p1 p2)
    also have "\<dots> < e"
      by (rule k d(2) p12 fine_union p1 p2)+
    finally have "norm ((\<Sum>(x, k)\<in>p1. content k *\<^sub>R f x) + (\<Sum>(x, k)\<in>p2. content k *\<^sub>R f x) - i) < e" .
   }
  then show ?thesis
    by (auto intro: that[of d] d elim: )
qed

lemma integrable_split[intro]:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::{real_normed_vector,complete_space}"
  assumes "f integrable_on cbox a b"
    and k: "k \<in> Basis"
  shows "f integrable_on (cbox a b \<inter> {x. x\<bullet>k \<le> c})" (is ?t1)
    and "f integrable_on (cbox a b \<inter> {x. x\<bullet>k \<ge> c})" (is ?t2)
proof -
  guess y using assms(1) unfolding integrable_on_def .. note y=this
  define b' where "b' = (\<Sum>i\<in>Basis. (if i = k then min (b\<bullet>k) c else b\<bullet>i)*\<^sub>R i)"
  define a' where "a' = (\<Sum>i\<in>Basis. (if i = k then max (a\<bullet>k) c else a\<bullet>i)*\<^sub>R i)"
  show ?t1 ?t2
    unfolding interval_split[OF k] integrable_cauchy
    unfolding interval_split[symmetric,OF k]
  proof (rule_tac[!] allI impI)+
    fix e :: real
    assume "e > 0"
    then have "e/2>0"
      by auto
    from has_integral_separate_sides[OF y this k,of c] guess d . note d=this[rule_format]
    let ?P = "\<lambda>A. \<exists>d. gauge d \<and> (\<forall>p1 p2. p1 tagged_division_of (cbox a b) \<inter> A \<and> d fine p1 \<and>
      p2 tagged_division_of (cbox a b) \<inter> A \<and> d fine p2 \<longrightarrow>
      norm ((\<Sum>(x, k)\<in>p1. content k *\<^sub>R f x) - (\<Sum>(x, k)\<in>p2. content k *\<^sub>R f x)) < e)"
    show "?P {x. x \<bullet> k \<le> c}"
    proof (rule_tac x=d in exI, clarsimp simp add: d)
      fix p1 p2
      assume as: "p1 tagged_division_of (cbox a b) \<inter> {x. x \<bullet> k \<le> c}" "d fine p1"
                 "p2 tagged_division_of (cbox a b) \<inter> {x. x \<bullet> k \<le> c}" "d fine p2"
      show "norm ((\<Sum>(x, k)\<in>p1. content k *\<^sub>R f x) - (\<Sum>(x, k)\<in>p2. content k *\<^sub>R f x)) < e"
      proof (rule fine_division_exists[OF d(1), of a' b] )
        fix p
        assume "p tagged_division_of cbox a' b" "d fine p"
        then show ?thesis
          using as norm_triangle_half_l[OF d(2)[of p1 p] d(2)[of p2 p]]
          unfolding interval_split[OF k] b'_def[symmetric] a'_def[symmetric]
          by (auto simp add: algebra_simps)
      qed
    qed
    show "?P {x. x \<bullet> k \<ge> c}"
    proof (rule_tac x=d in exI, clarsimp simp add: d)
      fix p1 p2
      assume as: "p1 tagged_division_of (cbox a b) \<inter> {x. x \<bullet> k \<ge> c}" "d fine p1"
                 "p2 tagged_division_of (cbox a b) \<inter> {x. x \<bullet> k \<ge> c}" "d fine p2"
      show "norm ((\<Sum>(x, k)\<in>p1. content k *\<^sub>R f x) - (\<Sum>(x, k)\<in>p2. content k *\<^sub>R f x)) < e"
      proof (rule fine_division_exists[OF d(1), of a b'] )
        fix p
        assume "p tagged_division_of cbox a b'" "d fine p"
        then show ?thesis
          using as norm_triangle_half_l[OF d(2)[of p p1] d(2)[of p p2]]
          unfolding interval_split[OF k] b'_def[symmetric] a'_def[symmetric]
          by (auto simp add: algebra_simps)
      qed
    qed
  qed
qed

lemma operative_integral:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::banach"
  shows "comm_monoid.operative (lift_option op +) (Some 0)
    (\<lambda>i. if f integrable_on i then Some (integral i f) else None)"
proof -
  interpret comm_monoid "lift_option plus" "Some (0::'b)"
    by (rule comm_monoid_lift_option)
      (rule add.comm_monoid_axioms)
  show ?thesis
  proof (unfold operative_def, safe)
    fix a b c
    fix k :: 'a
    assume k: "k \<in> Basis"
    show "(if f integrable_on cbox a b then Some (integral (cbox a b) f) else None) =
          lift_option op + (if f integrable_on cbox a b \<inter> {x. x \<bullet> k \<le> c} then Some (integral (cbox a b \<inter> {x. x \<bullet> k \<le> c}) f) else None)
          (if f integrable_on cbox a b \<inter> {x. c \<le> x \<bullet> k} then Some (integral (cbox a b \<inter> {x. c \<le> x \<bullet> k}) f) else None)"
    proof (cases "f integrable_on cbox a b")
      case True
      with k show ?thesis
        apply (simp add: integrable_split)
        apply (rule integral_unique [OF has_integral_split[OF _ _ k]])
        apply (auto intro: integrable_integral)
        done
    next
    case False
      have "\<not> (f integrable_on cbox a b \<inter> {x. x \<bullet> k \<le> c}) \<or> \<not> ( f integrable_on cbox a b \<inter> {x. c \<le> x \<bullet> k})"
      proof (rule ccontr)
        assume "\<not> ?thesis"
        then have "f integrable_on cbox a b"
          unfolding integrable_on_def
          apply (rule_tac x="integral (cbox a b \<inter> {x. x \<bullet> k \<le> c}) f + integral (cbox a b \<inter> {x. x \<bullet> k \<ge> c}) f" in exI)
          apply (rule has_integral_split[OF _ _ k])
          apply (auto intro: integrable_integral)
          done
        then show False
          using False by auto
      qed
      then show ?thesis
        using False by auto
    qed
  next
    fix a b :: 'a
    assume "content (cbox a b) = 0"
    then show "(if f integrable_on cbox a b then Some (integral (cbox a b) f) else None) = Some 0"
      using has_integral_null_eq
      by (auto simp: integrable_on_null)
  qed
qed

subsection \<open>Finally, the integral of a constant\<close>

lemma has_integral_const [intro]:
  fixes a b :: "'a::euclidean_space"
  shows "((\<lambda>x. c) has_integral (content (cbox a b) *\<^sub>R c)) (cbox a b)"
  apply (auto intro!: exI [where x="\<lambda>x. ball x 1"] simp: split_def has_integral)
  apply (subst scaleR_left.setsum[symmetric, unfolded o_def])
  apply (subst additive_content_tagged_division[unfolded split_def])
  apply auto
  done

lemma has_integral_const_real [intro]:
  fixes a b :: real
  shows "((\<lambda>x. c) has_integral (content {a .. b} *\<^sub>R c)) {a .. b}"
  by (metis box_real(2) has_integral_const)

lemma integral_const [simp]:
  fixes a b :: "'a::euclidean_space"
  shows "integral (cbox a b) (\<lambda>x. c) = content (cbox a b) *\<^sub>R c"
  by (rule integral_unique) (rule has_integral_const)

lemma integral_const_real [simp]:
  fixes a b :: real
  shows "integral {a .. b} (\<lambda>x. c) = content {a .. b} *\<^sub>R c"
  by (metis box_real(2) integral_const)


subsection \<open>Bounds on the norm of Riemann sums and the integral itself.\<close>

lemma dsum_bound:
  assumes "p division_of (cbox a b)"
    and "norm c \<le> e"
  shows "norm (setsum (\<lambda>l. content l *\<^sub>R c) p) \<le> e * content(cbox a b)"
proof -
  have sumeq: "(\<Sum>i\<in>p. \<bar>content i\<bar>) = setsum content p"
    apply (rule setsum.cong)
    using assms
    apply simp
    apply (metis abs_of_nonneg assms(1) content_pos_le division_ofD(4))
    done
  have e: "0 \<le> e"
    using assms(2) norm_ge_zero order_trans by blast
  have "norm (setsum (\<lambda>l. content l *\<^sub>R c) p) \<le> (\<Sum>i\<in>p. norm (content i *\<^sub>R c))"
    using norm_setsum by blast
  also have "...  \<le> e * (\<Sum>i\<in>p. \<bar>content i\<bar>)"
    by (simp add: setsum_distrib_left[symmetric] mult.commute assms(2) mult_right_mono setsum_nonneg)
  also have "... \<le> e * content (cbox a b)"
    apply (rule mult_left_mono [OF _ e])
    apply (simp add: sumeq)
    using additive_content_division assms(1) eq_iff apply blast
    done
  finally show ?thesis .
qed

lemma rsum_bound:
  assumes p: "p tagged_division_of (cbox a b)"
      and "\<forall>x\<in>cbox a b. norm (f x) \<le> e"
    shows "norm (setsum (\<lambda>(x,k). content k *\<^sub>R f x) p) \<le> e * content (cbox a b)"
proof (cases "cbox a b = {}")
  case True show ?thesis
    using p unfolding True tagged_division_of_trivial by auto
next
  case False
  then have e: "e \<ge> 0"
    by (meson ex_in_conv assms(2) norm_ge_zero order_trans)
  have setsum_le: "setsum (content \<circ> snd) p \<le> content (cbox a b)"
    unfolding additive_content_tagged_division[OF p, symmetric] split_def
    by (auto intro: eq_refl)
  have con: "\<And>xk. xk \<in> p \<Longrightarrow> 0 \<le> content (snd xk)"
    using tagged_division_ofD(4) [OF p] content_pos_le
    by force
  have norm: "\<And>xk. xk \<in> p \<Longrightarrow> norm (f (fst xk)) \<le> e"
    unfolding fst_conv using tagged_division_ofD(2,3)[OF p] assms
    by (metis prod.collapse subset_eq)
  have "norm (setsum (\<lambda>(x,k). content k *\<^sub>R f x) p) \<le> (\<Sum>i\<in>p. norm (case i of (x, k) \<Rightarrow> content k *\<^sub>R f x))"
    by (rule norm_setsum)
  also have "...  \<le> e * content (cbox a b)"
    unfolding split_def norm_scaleR
    apply (rule order_trans[OF setsum_mono])
    apply (rule mult_left_mono[OF _ abs_ge_zero, of _ e])
    apply (metis norm)
    unfolding setsum_distrib_right[symmetric]
    using con setsum_le
    apply (auto simp: mult.commute intro: mult_left_mono [OF _ e])
    done
  finally show ?thesis .
qed

lemma rsum_diff_bound:
  assumes "p tagged_division_of (cbox a b)"
    and "\<forall>x\<in>cbox a b. norm (f x - g x) \<le> e"
  shows "norm (setsum (\<lambda>(x,k). content k *\<^sub>R f x) p - setsum (\<lambda>(x,k). content k *\<^sub>R g x) p) \<le>
         e * content (cbox a b)"
  apply (rule order_trans[OF _ rsum_bound[OF assms]])
  apply (simp add: split_def scaleR_diff_right setsum_subtractf eq_refl)
  done

lemma has_integral_bound:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::real_normed_vector"
  assumes "0 \<le> B"
      and "(f has_integral i) (cbox a b)"
      and "\<forall>x\<in>cbox a b. norm (f x) \<le> B"
    shows "norm i \<le> B * content (cbox a b)"
proof (rule ccontr)
  assume "\<not> ?thesis"
  then have *: "norm i - B * content (cbox a b) > 0"
    by auto
  from assms(2)[unfolded has_integral,rule_format,OF *]
  guess d by (elim exE conjE) note d=this[rule_format]
  from fine_division_exists[OF this(1), of a b] guess p . note p=this
  have *: "\<And>s B. norm s \<le> B \<Longrightarrow> \<not> norm (s - i) < norm i - B"
    unfolding not_less
    by (metis norm_triangle_sub[of i] add.commute le_less_trans less_diff_eq linorder_not_le norm_minus_commute)
  show False
    using d(2)[OF conjI[OF p]] *[OF rsum_bound[OF p(1) assms(3)]] by auto
qed

corollary has_integral_bound_real:
  fixes f :: "real \<Rightarrow> 'b::real_normed_vector"
  assumes "0 \<le> B"
      and "(f has_integral i) {a .. b}"
      and "\<forall>x\<in>{a .. b}. norm (f x) \<le> B"
    shows "norm i \<le> B * content {a .. b}"
  by (metis assms box_real(2) has_integral_bound)

corollary integrable_bound:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::real_normed_vector"
  assumes "0 \<le> B"
      and "f integrable_on (cbox a b)"
      and "\<And>x. x\<in>cbox a b \<Longrightarrow> norm (f x) \<le> B"
    shows "norm (integral (cbox a b) f) \<le> B * content (cbox a b)"
by (metis integrable_integral has_integral_bound assms)


subsection \<open>Similar theorems about relationship among components.\<close>

lemma rsum_component_le:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  assumes "p tagged_division_of (cbox a b)"
      and "\<forall>x\<in>cbox a b. (f x)\<bullet>i \<le> (g x)\<bullet>i"
    shows "(setsum (\<lambda>(x,k). content k *\<^sub>R f x) p)\<bullet>i \<le> (setsum (\<lambda>(x,k). content k *\<^sub>R g x) p)\<bullet>i"
unfolding inner_setsum_left
proof (rule setsum_mono, clarify)
  fix a b
  assume ab: "(a, b) \<in> p"
  note tagged = tagged_division_ofD(2-4)[OF assms(1) ab]
  from this(3) guess u v by (elim exE) note b=this
  show "(content b *\<^sub>R f a) \<bullet> i \<le> (content b *\<^sub>R g a) \<bullet> i"
    unfolding b inner_simps real_scaleR_def
    apply (rule mult_left_mono)
    using assms(2) tagged
    by (auto simp add: content_pos_le)
qed

lemma has_integral_component_le:
  fixes f g :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  assumes k: "k \<in> Basis"
  assumes "(f has_integral i) s" "(g has_integral j) s"
    and "\<forall>x\<in>s. (f x)\<bullet>k \<le> (g x)\<bullet>k"
  shows "i\<bullet>k \<le> j\<bullet>k"
proof -
  have lem: "i\<bullet>k \<le> j\<bullet>k"
    if f_i: "(f has_integral i) (cbox a b)"
    and g_j: "(g has_integral j) (cbox a b)"
    and le: "\<forall>x\<in>cbox a b. (f x)\<bullet>k \<le> (g x)\<bullet>k"
    for a b i and j :: 'b and f g :: "'a \<Rightarrow> 'b"
  proof (rule ccontr)
    assume "\<not> ?thesis"
    then have *: "0 < (i\<bullet>k - j\<bullet>k) / 3"
      by auto
    guess d1 using f_i[unfolded has_integral,rule_format,OF *] by (elim exE conjE) note d1=this[rule_format]
    guess d2 using g_j[unfolded has_integral,rule_format,OF *] by (elim exE conjE) note d2=this[rule_format]
    obtain p where p: "p tagged_division_of cbox a b" "d1 fine p" "d2 fine p"
       using fine_division_exists[OF gauge_inter[OF d1(1) d2(1)], of a b] unfolding fine_inter
       by metis
    note le_less_trans[OF Basis_le_norm[OF k]]
    then have "\<bar>((\<Sum>(x, k)\<in>p. content k *\<^sub>R f x) - i) \<bullet> k\<bar> < (i \<bullet> k - j \<bullet> k) / 3"
              "\<bar>((\<Sum>(x, k)\<in>p. content k *\<^sub>R g x) - j) \<bullet> k\<bar> < (i \<bullet> k - j \<bullet> k) / 3"
      using  k norm_bound_Basis_lt d1 d2 p
      by blast+
    then show False
      unfolding inner_simps
      using rsum_component_le[OF p(1) le]
      by (simp add: abs_real_def split: if_split_asm)
  qed
  show ?thesis
  proof (cases "\<exists>a b. s = cbox a b")
    case True
    with lem assms show ?thesis
      by auto
  next
    case False
    show ?thesis
    proof (rule ccontr)
      assume "\<not> i\<bullet>k \<le> j\<bullet>k"
      then have ij: "(i\<bullet>k - j\<bullet>k) / 3 > 0"
        by auto
      note has_integral_altD[OF _ False this]
      from this[OF assms(2)] this[OF assms(3)] guess B1 B2 . note B=this[rule_format]
      have "bounded (ball 0 B1 \<union> ball (0::'a) B2)"
        unfolding bounded_Un by(rule conjI bounded_ball)+
      from bounded_subset_cbox[OF this] guess a b by (elim exE)
      note ab = conjunctD2[OF this[unfolded Un_subset_iff]]
      guess w1 using B(2)[OF ab(1)] .. note w1=conjunctD2[OF this]
      guess w2 using B(4)[OF ab(2)] .. note w2=conjunctD2[OF this]
      have *: "\<And>w1 w2 j i::real .\<bar>w1 - i\<bar> < (i - j) / 3 \<Longrightarrow> \<bar>w2 - j\<bar> < (i - j) / 3 \<Longrightarrow> w1 \<le> w2 \<Longrightarrow> False"
        by (simp add: abs_real_def split: if_split_asm)
      note le_less_trans[OF Basis_le_norm[OF k]]
      note this[OF w1(2)] this[OF w2(2)]
      moreover
      have "w1\<bullet>k \<le> w2\<bullet>k"
        by (rule lem[OF w1(1) w2(1)]) (simp add: assms(4))
      ultimately show False
        unfolding inner_simps by(rule *)
    qed
  qed
qed

lemma integral_component_le:
  fixes g f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  assumes "k \<in> Basis"
    and "f integrable_on s" "g integrable_on s"
    and "\<forall>x\<in>s. (f x)\<bullet>k \<le> (g x)\<bullet>k"
  shows "(integral s f)\<bullet>k \<le> (integral s g)\<bullet>k"
  apply (rule has_integral_component_le)
  using integrable_integral assms
  apply auto
  done

lemma has_integral_component_nonneg:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  assumes "k \<in> Basis"
    and "(f has_integral i) s"
    and "\<forall>x\<in>s. 0 \<le> (f x)\<bullet>k"
  shows "0 \<le> i\<bullet>k"
  using has_integral_component_le[OF assms(1) has_integral_0 assms(2)]
  using assms(3-)
  by auto

lemma integral_component_nonneg:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  assumes "k \<in> Basis"
    and  "\<forall>x\<in>s. 0 \<le> (f x)\<bullet>k"
  shows "0 \<le> (integral s f)\<bullet>k"
proof (cases "f integrable_on s")
  case True show ?thesis
    apply (rule has_integral_component_nonneg)
    using assms True
    apply auto
    done
next
  case False then show ?thesis by (simp add: not_integrable_integral)
qed

lemma has_integral_component_neg:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  assumes "k \<in> Basis"
    and "(f has_integral i) s"
    and "\<forall>x\<in>s. (f x)\<bullet>k \<le> 0"
  shows "i\<bullet>k \<le> 0"
  using has_integral_component_le[OF assms(1,2) has_integral_0] assms(2-)
  by auto

lemma has_integral_component_lbound:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  assumes "(f has_integral i) (cbox a b)"
    and "\<forall>x\<in>cbox a b. B \<le> f(x)\<bullet>k"
    and "k \<in> Basis"
  shows "B * content (cbox a b) \<le> i\<bullet>k"
  using has_integral_component_le[OF assms(3) has_integral_const assms(1),of "(\<Sum>i\<in>Basis. B *\<^sub>R i)::'b"] assms(2-)
  by (auto simp add: field_simps)

lemma has_integral_component_ubound:
  fixes f::"'a::euclidean_space => 'b::euclidean_space"
  assumes "(f has_integral i) (cbox a b)"
    and "\<forall>x\<in>cbox a b. f x\<bullet>k \<le> B"
    and "k \<in> Basis"
  shows "i\<bullet>k \<le> B * content (cbox a b)"
  using has_integral_component_le[OF assms(3,1) has_integral_const, of "\<Sum>i\<in>Basis. B *\<^sub>R i"] assms(2-)
  by (auto simp add: field_simps)

lemma integral_component_lbound:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  assumes "f integrable_on cbox a b"
    and "\<forall>x\<in>cbox a b. B \<le> f(x)\<bullet>k"
    and "k \<in> Basis"
  shows "B * content (cbox a b) \<le> (integral(cbox a b) f)\<bullet>k"
  apply (rule has_integral_component_lbound)
  using assms
  unfolding has_integral_integral
  apply auto
  done

lemma integral_component_lbound_real:
  assumes "f integrable_on {a ::real .. b}"
    and "\<forall>x\<in>{a .. b}. B \<le> f(x)\<bullet>k"
    and "k \<in> Basis"
  shows "B * content {a .. b} \<le> (integral {a .. b} f)\<bullet>k"
  using assms
  by (metis box_real(2) integral_component_lbound)

lemma integral_component_ubound:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  assumes "f integrable_on cbox a b"
    and "\<forall>x\<in>cbox a b. f x\<bullet>k \<le> B"
    and "k \<in> Basis"
  shows "(integral (cbox a b) f)\<bullet>k \<le> B * content (cbox a b)"
  apply (rule has_integral_component_ubound)
  using assms
  unfolding has_integral_integral
  apply auto
  done

lemma integral_component_ubound_real:
  fixes f :: "real \<Rightarrow> 'a::euclidean_space"
  assumes "f integrable_on {a .. b}"
    and "\<forall>x\<in>{a .. b}. f x\<bullet>k \<le> B"
    and "k \<in> Basis"
  shows "(integral {a .. b} f)\<bullet>k \<le> B * content {a .. b}"
  using assms
  by (metis box_real(2) integral_component_ubound)

subsection \<open>Uniform limit of integrable functions is integrable.\<close>

lemma real_arch_invD:
  "0 < (e::real) \<Longrightarrow> (\<exists>n::nat. n \<noteq> 0 \<and> 0 < inverse (real n) \<and> inverse (real n) < e)"
  by (subst(asm) real_arch_inverse)

lemma integrable_uniform_limit:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::banach"
  assumes "\<forall>e>0. \<exists>g. (\<forall>x\<in>cbox a b. norm (f x - g x) \<le> e) \<and> g integrable_on cbox a b"
  shows "f integrable_on cbox a b"
proof (cases "content (cbox a b) > 0")
  case False then show ?thesis
      using has_integral_null
      by (simp add: content_lt_nz integrable_on_def)
next
  case True
  have *: "\<And>P. \<forall>e>(0::real). P e \<Longrightarrow> \<forall>n::nat. P (inverse (real n + 1))"
    by auto
  from choice[OF *[OF assms]] guess g .. note g=conjunctD2[OF this[rule_format],rule_format]
  from choice[OF allI[OF g(2)[unfolded integrable_on_def], of "\<lambda>x. x"]]
  obtain i where i: "\<And>x. (g x has_integral i x) (cbox a b)"
      by auto
  have "Cauchy i"
    unfolding Cauchy_def
  proof clarify
    fix e :: real
    assume "e>0"
    then have "e / 4 / content (cbox a b) > 0"
      using True by (auto simp add: field_simps)
    then obtain M :: nat
         where M: "M \<noteq> 0" "0 < inverse (real_of_nat M)" "inverse (of_nat M) < e / 4 / content (cbox a b)"
      by (subst (asm) real_arch_inverse) auto
    show "\<exists>M. \<forall>m\<ge>M. \<forall>n\<ge>M. dist (i m) (i n) < e"
    proof (rule exI [where x=M], clarify)
      fix m n
      assume m: "M \<le> m" and n: "M \<le> n"
      have "e/4>0" using \<open>e>0\<close> by auto
      note * = i[unfolded has_integral,rule_format,OF this]
      from *[of m] guess gm by (elim conjE exE) note gm=this[rule_format]
      from *[of n] guess gn by (elim conjE exE) note gn=this[rule_format]
      from fine_division_exists[OF gauge_inter[OF gm(1) gn(1)], of a b]
      obtain p where p: "p tagged_division_of cbox a b" "(\<lambda>x. gm x \<inter> gn x) fine p"
        by auto
      { fix s1 s2 i1 and i2::'b
        assume no: "norm(s2 - s1) \<le> e/2" "norm (s1 - i1) < e/4" "norm (s2 - i2) < e/4"
        have "norm (i1 - i2) \<le> norm (i1 - s1) + norm (s1 - s2) + norm (s2 - i2)"
          using norm_triangle_ineq[of "i1 - s1" "s1 - i2"]
          using norm_triangle_ineq[of "s1 - s2" "s2 - i2"]
          by (auto simp add: algebra_simps)
        also have "\<dots> < e"
          using no
          unfolding norm_minus_commute
          by (auto simp add: algebra_simps)
        finally have "norm (i1 - i2) < e" .
      } note triangle3 = this
      have finep: "gm fine p" "gn fine p"
        using fine_inter p  by auto
      { fix x
        assume x: "x \<in> cbox a b"
        have "norm (f x - g n x) + norm (f x - g m x) \<le> inverse (real n + 1) + inverse (real m + 1)"
          using g(1)[OF x, of n] g(1)[OF x, of m] by auto
        also have "\<dots> \<le> inverse (real M) + inverse (real M)"
          apply (rule add_mono)
          using M(2) m n by auto
        also have "\<dots> = 2 / real M"
          unfolding divide_inverse by auto
        finally have "norm (g n x - g m x) \<le> 2 / real M"
          using norm_triangle_le[of "g n x - f x" "f x - g m x" "2 / real M"]
          by (auto simp add: algebra_simps simp add: norm_minus_commute)
      } note norm_le = this
      have le_e2: "norm ((\<Sum>(x, k)\<in>p. content k *\<^sub>R g n x) - (\<Sum>(x, k)\<in>p. content k *\<^sub>R g m x)) \<le> e / 2"
        apply (rule order_trans [OF rsum_diff_bound[OF p(1), where e="2 / real M"]])
        apply (blast intro: norm_le)
        using M True
        by (auto simp add: field_simps)
      then show "dist (i m) (i n) < e"
        unfolding dist_norm
        using gm gn p finep
        by (auto intro!: triangle3)
    qed
  qed
  then obtain s where s: "i \<longlonglongrightarrow> s"
    using convergent_eq_cauchy[symmetric] by blast
  show ?thesis
    unfolding integrable_on_def has_integral
  proof (rule_tac x=s in exI, clarify)
    fix e::real
    assume e: "0 < e"
    then have *: "e/3 > 0" by auto
    then obtain N1 where N1: "\<forall>n\<ge>N1. norm (i n - s) < e / 3"
      using LIMSEQ_D [OF s] by metis
    from e True have "e / 3 / content (cbox a b) > 0"
      by (auto simp add: field_simps)
    from real_arch_invD[OF this] guess N2 by (elim exE conjE) note N2=this
    from i[of "N1 + N2",unfolded has_integral,rule_format,OF *] guess g' .. note g'=conjunctD2[OF this,rule_format]
    { fix sf sg i
      assume no: "norm (sf - sg) \<le> e / 3"
                 "norm(i - s) < e / 3"
                 "norm (sg - i) < e / 3"
      have "norm (sf - s) \<le> norm (sf - sg) + norm (sg - i) + norm (i - s)"
        using norm_triangle_ineq[of "sf - sg" "sg - s"]
        using norm_triangle_ineq[of "sg -  i" " i - s"]
        by (auto simp add: algebra_simps)
      also have "\<dots> < e"
        using no
        unfolding norm_minus_commute
        by (auto simp add: algebra_simps)
      finally have "norm (sf - s) < e" .
    } note lem = this
    { fix p
      assume p: "p tagged_division_of (cbox a b) \<and> g' fine p"
      then have norm_less: "norm ((\<Sum>(x, k)\<in>p. content k *\<^sub>R g (N1 + N2) x) - i (N1 + N2)) < e / 3"
        using g' by blast
      have "content (cbox a b) < e / 3 * (of_nat N2)"
        using N2 unfolding inverse_eq_divide using True by (auto simp add: field_simps)
      moreover have "e / 3 * of_nat N2 \<le> e / 3 * (of_nat (N1 + N2) + 1)"
        using \<open>e>0\<close> by auto
      ultimately have "content (cbox a b) < e / 3 * (of_nat (N1 + N2) + 1)"
        by linarith
      then have le_e3: "inverse (real (N1 + N2) + 1) * content (cbox a b) \<le> e / 3"
        unfolding inverse_eq_divide
        by (auto simp add: field_simps)
      have ne3: "norm (i (N1 + N2) - s) < e / 3"
        using N1 by auto
      have "norm ((\<Sum>(x, k)\<in>p. content k *\<^sub>R f x) - s) < e"
        apply (rule lem[OF order_trans [OF _ le_e3] ne3 norm_less])
        apply (rule rsum_diff_bound[OF p[THEN conjunct1]])
        apply (blast intro: g)
        done }
    then show "\<exists>d. gauge d \<and>
             (\<forall>p. p tagged_division_of cbox a b \<and> d fine p \<longrightarrow> norm ((\<Sum>(x, k)\<in>p. content k *\<^sub>R f x) - s) < e)"
      by (blast intro: g')
  qed
qed

lemmas integrable_uniform_limit_real = integrable_uniform_limit [where 'a=real, simplified]


subsection \<open>Negligible sets.\<close>

definition "negligible (s:: 'a::euclidean_space set) \<longleftrightarrow>
  (\<forall>a b. ((indicator s :: 'a\<Rightarrow>real) has_integral 0) (cbox a b))"


subsection \<open>Negligibility of hyperplane.\<close>

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
      apply (simp add: abs_diff_le_iff field_simps Collect_conj_eq setcompr_eq_image[symmetric])
      apply (rule equalityI)
      apply blast
      apply clarsimp
      apply (rule_tac x="l \<inter> {x. c + e \<ge> x \<bullet> k}" in exI)
      apply auto
      done
    by (simp add: interval_split k interval_doublesplit)
qed

lemma content_doublesplit:
  fixes a :: "'a::euclidean_space"
  assumes "0 < e"
    and k: "k \<in> Basis"
  obtains d where "0 < d" and "content (cbox a b \<inter> {x. \<bar>x\<bullet>k - c\<bar> \<le> d}) < e"
proof cases
  assume *: "a \<bullet> k \<le> c \<and> c \<le> b \<bullet> k \<and> (\<forall>j\<in>Basis. a \<bullet> j \<le> b \<bullet> j)"
  define a' where "a' d = (\<Sum>j\<in>Basis. (if j = k then max (a\<bullet>j) (c - d) else a\<bullet>j) *\<^sub>R j)" for d
  define b' where "b' d = (\<Sum>j\<in>Basis. (if j = k then min (b\<bullet>j) (c + d) else b\<bullet>j) *\<^sub>R j)" for d

  have "((\<lambda>d. \<Prod>j\<in>Basis. (b' d - a' d) \<bullet> j) \<longlongrightarrow> (\<Prod>j\<in>Basis. (b' 0 - a' 0) \<bullet> j)) (at_right 0)"
    by (auto simp: b'_def a'_def intro!: tendsto_min tendsto_max tendsto_eq_intros)
  also have "(\<Prod>j\<in>Basis. (b' 0 - a' 0) \<bullet> j) = 0"
    using k *
    by (intro setprod_zero bexI[OF _ k])
       (auto simp: b'_def a'_def inner_diff inner_setsum_left inner_not_same_Basis intro!: setsum.cong)
  also have "((\<lambda>d. \<Prod>j\<in>Basis. (b' d - a' d) \<bullet> j) \<longlongrightarrow> 0) (at_right 0) =
    ((\<lambda>d. content (cbox a b \<inter> {x. \<bar>x\<bullet>k - c\<bar> \<le> d})) \<longlongrightarrow> 0) (at_right 0)"
  proof (intro tendsto_cong eventually_at_rightI)
    fix d :: real assume d: "d \<in> {0<..<1}"
    have "cbox a b \<inter> {x. \<bar>x\<bullet>k - c\<bar> \<le> d} = cbox (a' d) (b' d)" for d
      using * d k by (auto simp add: cbox_def set_eq_iff Int_def ball_conj_distrib abs_diff_le_iff a'_def b'_def)
    moreover have "j \<in> Basis \<Longrightarrow> a' d \<bullet> j \<le> b' d \<bullet> j" for j
      using * d k by (auto simp: a'_def b'_def)
    ultimately show "(\<Prod>j\<in>Basis. (b' d - a' d) \<bullet> j) = content (cbox a b \<inter> {x. \<bar>x\<bullet>k - c\<bar> \<le> d})"
      by simp
  qed simp
  finally have "((\<lambda>d. content (cbox a b \<inter> {x. \<bar>x \<bullet> k - c\<bar> \<le> d})) \<longlongrightarrow> 0) (at_right 0)" .
  from order_tendstoD(2)[OF this \<open>0<e\<close>]
  obtain d' where "0 < d'" and d': "\<And>y. y > 0 \<Longrightarrow> y < d' \<Longrightarrow> content (cbox a b \<inter> {x. \<bar>x \<bullet> k - c\<bar> \<le> y}) < e"
    by (subst (asm) eventually_at_right[of _ 1]) auto
  show ?thesis
    by (rule that[of "d'/2"], insert \<open>0<d'\<close> d'[of "d'/2"], auto)
next
  assume *: "\<not> (a \<bullet> k \<le> c \<and> c \<le> b \<bullet> k \<and> (\<forall>j\<in>Basis. a \<bullet> j \<le> b \<bullet> j))"
  then have "(\<exists>j\<in>Basis. b \<bullet> j < a \<bullet> j) \<or> (c < a \<bullet> k \<or> b \<bullet> k < c)"
    by (auto simp: not_le)
  show thesis
  proof cases
    assume "\<exists>j\<in>Basis. b \<bullet> j < a \<bullet> j"
    then have [simp]: "cbox a b = {}"
      using box_ne_empty(1)[of a b] by auto
    show ?thesis
      by (rule that[of 1]) (simp_all add: \<open>0<e\<close>)
  next
    assume "\<not> (\<exists>j\<in>Basis. b \<bullet> j < a \<bullet> j)"
    with * have "c < a \<bullet> k \<or> b \<bullet> k < c"
      by auto
    then show thesis
    proof
      assume c: "c < a \<bullet> k"
      moreover have "x \<in> cbox a b \<Longrightarrow> c \<le> x \<bullet> k" for x
        using k c by (auto simp: cbox_def)
      ultimately have "cbox a b \<inter> {x. \<bar>x \<bullet> k - c\<bar> \<le> (a \<bullet> k - c) / 2} = {}"
        using k by (auto simp: cbox_def)
      with \<open>0<e\<close> c that[of "(a \<bullet> k - c) / 2"] show ?thesis
        by auto
    next
      assume c: "b \<bullet> k < c"
      moreover have "x \<in> cbox a b \<Longrightarrow> x \<bullet> k \<le> c" for x
        using k c by (auto simp: cbox_def)
      ultimately have "cbox a b \<inter> {x. \<bar>x \<bullet> k - c\<bar> \<le> (c - b \<bullet> k) / 2} = {}"
        using k by (auto simp: cbox_def)
      with \<open>0<e\<close> c that[of "(c - b \<bullet> k) / 2"] show ?thesis
        by auto
    qed
  qed
qed


lemma negligible_standard_hyperplane[intro]:
  fixes k :: "'a::euclidean_space"
  assumes k: "k \<in> Basis"
  shows "negligible {x. x\<bullet>k = c}"
  unfolding negligible_def has_integral
proof (clarify, goal_cases)
  case (1 a b e)
  from this and k obtain d where d: "0 < d" "content (cbox a b \<inter> {x. \<bar>x \<bullet> k - c\<bar> \<le> d}) < e"
    by (rule content_doublesplit)
  let ?i = "indicator {x::'a. x\<bullet>k = c} :: 'a\<Rightarrow>real"
  show ?case
    apply (rule_tac x="\<lambda>x. ball x d" in exI)
    apply rule
    apply (rule gauge_ball)
    apply (rule d)
  proof (rule, rule)
    fix p
    assume p: "p tagged_division_of (cbox a b) \<and> (\<lambda>x. ball x d) fine p"
    have *: "(\<Sum>(x, ka)\<in>p. content ka *\<^sub>R ?i x) =
      (\<Sum>(x, ka)\<in>p. content (ka \<inter> {x. \<bar>x\<bullet>k - c\<bar> \<le> d}) *\<^sub>R ?i x)"
      apply (rule setsum.cong)
      apply (rule refl)
      unfolding split_paired_all real_scaleR_def mult_cancel_right split_conv
      apply cases
      apply (rule disjI1)
      apply assumption
      apply (rule disjI2)
    proof -
      fix x l
      assume as: "(x, l) \<in> p" "?i x \<noteq> 0"
      then have xk: "x\<bullet>k = c"
        unfolding indicator_def
        apply -
        apply (rule ccontr)
        apply auto
        done
      show "content l = content (l \<inter> {x. \<bar>x \<bullet> k - c\<bar> \<le> d})"
        apply (rule arg_cong[where f=content])
        apply (rule set_eqI)
        apply rule
        apply rule
        unfolding mem_Collect_eq
      proof -
        fix y
        assume y: "y \<in> l"
        note p[THEN conjunct2,unfolded fine_def,rule_format,OF as(1),unfolded split_conv]
        note this[unfolded subset_eq mem_ball dist_norm,rule_format,OF y]
        note le_less_trans[OF Basis_le_norm[OF k] this]
        then show "\<bar>y \<bullet> k - c\<bar> \<le> d"
          unfolding inner_simps xk by auto
      qed auto
    qed
    note p'= tagged_division_ofD[OF p[THEN conjunct1]] and p''=division_of_tagged_division[OF p[THEN conjunct1]]
    show "norm ((\<Sum>(x, ka)\<in>p. content ka *\<^sub>R ?i x) - 0) < e"
      unfolding diff_0_right *
      unfolding real_scaleR_def real_norm_def
      apply (subst abs_of_nonneg)
      apply (rule setsum_nonneg)
      apply rule
      unfolding split_paired_all split_conv
      apply (rule mult_nonneg_nonneg)
      apply (drule p'(4))
      apply (erule exE)+
      apply(rule_tac b=b in back_subst)
      prefer 2
      apply (subst(asm) eq_commute)
      apply assumption
      apply (subst interval_doublesplit[OF k])
      apply (rule content_pos_le)
      apply (rule indicator_pos_le)
    proof -
      have "(\<Sum>(x, ka)\<in>p. content (ka \<inter> {x. \<bar>x \<bullet> k - c\<bar> \<le> d}) * ?i x) \<le>
        (\<Sum>(x, ka)\<in>p. content (ka \<inter> {x. \<bar>x \<bullet> k - c\<bar> \<le> d}))"
        apply (rule setsum_mono)
        unfolding split_paired_all split_conv
        apply (rule mult_right_le_one_le)
        apply (drule p'(4))
        apply (auto simp add:interval_doublesplit[OF k])
        done
      also have "\<dots> < e"
      proof (subst setsum.over_tagged_division_lemma[OF p[THEN conjunct1]], goal_cases)
        case prems: (1 u v)
        have "content (cbox u v \<inter> {x. \<bar>x \<bullet> k - c\<bar> \<le> d}) \<le> content (cbox u v)"
          unfolding interval_doublesplit[OF k]
          apply (rule content_subset)
          unfolding interval_doublesplit[symmetric,OF k]
          apply auto
          done
        then show ?case
          unfolding prems interval_doublesplit[OF k]
          by (blast intro: antisym)
      next
        have "(\<Sum>l\<in>snd ` p. content (l \<inter> {x. \<bar>x \<bullet> k - c\<bar> \<le> d})) =
          setsum content ((\<lambda>l. l \<inter> {x. \<bar>x \<bullet> k - c\<bar> \<le> d})`{l\<in>snd ` p. l \<inter> {x. \<bar>x \<bullet> k - c\<bar> \<le> d} \<noteq> {}})"
        proof (subst (2) setsum.reindex_nontrivial)
          fix x y assume "x \<in> {l \<in> snd ` p. l \<inter> {x. \<bar>x \<bullet> k - c\<bar> \<le> d} \<noteq> {}}" "y \<in> {l \<in> snd ` p. l \<inter> {x. \<bar>x \<bullet> k - c\<bar> \<le> d} \<noteq> {}}"
            "x \<noteq> y" and eq: "x \<inter> {x. \<bar>x \<bullet> k - c\<bar> \<le> d} = y \<inter> {x. \<bar>x \<bullet> k - c\<bar> \<le> d}"
          then obtain x' y' where "(x', x) \<in> p" "x \<inter> {x. \<bar>x \<bullet> k - c\<bar> \<le> d} \<noteq> {}" "(y', y) \<in> p" "y \<inter> {x. \<bar>x \<bullet> k - c\<bar> \<le> d} \<noteq> {}"
            by (auto)
          from p'(5)[OF \<open>(x', x) \<in> p\<close> \<open>(y', y) \<in> p\<close>] \<open>x \<noteq> y\<close> have "interior (x \<inter> y) = {}"
            by auto
          moreover have "interior ((x \<inter> {x. \<bar>x \<bullet> k - c\<bar> \<le> d}) \<inter> (y \<inter> {x. \<bar>x \<bullet> k - c\<bar> \<le> d})) \<subseteq> interior (x \<inter> y)"
            by (auto intro: interior_mono)
          ultimately have "interior (x \<inter> {x. \<bar>x \<bullet> k - c\<bar> \<le> d}) = {}"
            by (auto simp: eq)
          then show "content (x \<inter> {x. \<bar>x \<bullet> k - c\<bar> \<le> d}) = 0"
            using p'(4)[OF \<open>(x', x) \<in> p\<close>] by (auto simp: interval_doublesplit[OF k] content_eq_0_interior simp del: interior_Int)
        qed (insert p'(1), auto intro!: setsum.mono_neutral_right)
        also have "\<dots> \<le> norm (\<Sum>l\<in>(\<lambda>l. l \<inter> {x. \<bar>x \<bullet> k - c\<bar> \<le> d})`{l\<in>snd ` p. l \<inter> {x. \<bar>x \<bullet> k - c\<bar> \<le> d} \<noteq> {}}. content l *\<^sub>R 1::real)"
          by simp
        also have "\<dots> \<le> 1 * content (cbox a b \<inter> {x. \<bar>x \<bullet> k - c\<bar> \<le> d})"
          using division_doublesplit[OF p'' k, unfolded interval_doublesplit[OF k]]
          unfolding interval_doublesplit[OF k] by (intro dsum_bound) auto
        also have "\<dots> < e"
          using d(2) by simp
        finally show "(\<Sum>ka\<in>snd ` p. content (ka \<inter> {x. \<bar>x \<bullet> k - c\<bar> \<le> d})) < e" .
      qed
      finally show "(\<Sum>(x, ka)\<in>p. content (ka \<inter> {x. \<bar>x \<bullet> k - c\<bar> \<le> d}) * ?i x) < e" .
    qed
  qed
qed


subsection \<open>A technical lemma about "refinement" of division.\<close>

lemma tagged_division_finer:
  fixes p :: "('a::euclidean_space \<times> ('a::euclidean_space set)) set"
  assumes "p tagged_division_of (cbox a b)"
    and "gauge d"
  obtains q where "q tagged_division_of (cbox a b)"
    and "d fine q"
    and "\<forall>(x,k) \<in> p. k \<subseteq> d(x) \<longrightarrow> (x,k) \<in> q"
proof -
  let ?P = "\<lambda>p. p tagged_partial_division_of (cbox a b) \<longrightarrow> gauge d \<longrightarrow>
    (\<exists>q. q tagged_division_of (\<Union>{k. \<exists>x. (x,k) \<in> p}) \<and> d fine q \<and>
      (\<forall>(x,k) \<in> p. k \<subseteq> d(x) \<longrightarrow> (x,k) \<in> q))"
  {
    have *: "finite p" "p tagged_partial_division_of (cbox a b)"
      using assms(1)
      unfolding tagged_division_of_def
      by auto
    presume "\<And>p. finite p \<Longrightarrow> ?P p"
    from this[rule_format,OF * assms(2)] guess q .. note q=this
    then show ?thesis
      apply -
      apply (rule that[of q])
      unfolding tagged_division_ofD[OF assms(1)]
      apply auto
      done
  }
  fix p :: "('a::euclidean_space \<times> ('a::euclidean_space set)) set"
  assume as: "finite p"
  show "?P p"
    apply rule
    apply rule
    using as
  proof (induct p)
    case empty
    show ?case
      apply (rule_tac x="{}" in exI)
      unfolding fine_def
      apply auto
      done
  next
    case (insert xk p)
    guess x k using surj_pair[of xk] by (elim exE) note xk=this
    note tagged_partial_division_subset[OF insert(4) subset_insertI]
    from insert(3)[OF this insert(5)] guess q1 .. note q1 = conjunctD3[OF this]
    have *: "\<Union>{l. \<exists>y. (y,l) \<in> insert xk p} = k \<union> \<Union>{l. \<exists>y. (y,l) \<in> p}"
      unfolding xk by auto
    note p = tagged_partial_division_ofD[OF insert(4)]
    from p(4)[unfolded xk, OF insertI1] guess u v by (elim exE) note uv=this

    have "finite {k. \<exists>x. (x, k) \<in> p}"
      apply (rule finite_subset[of _ "snd ` p"])
      using p
      apply safe
      apply (metis image_iff snd_conv)
      apply auto
      done
    then have int: "interior (cbox u v) \<inter> interior (\<Union>{k. \<exists>x. (x, k) \<in> p}) = {}"
      apply (rule inter_interior_unions_intervals)
      apply (rule open_interior)
      apply (rule_tac[!] ballI)
      unfolding mem_Collect_eq
      apply (erule_tac[!] exE)
      apply (drule p(4)[OF insertI2])
      apply assumption
      apply (rule p(5))
      unfolding uv xk
      apply (rule insertI1)
      apply (rule insertI2)
      apply assumption
      using insert(2)
      unfolding uv xk
      apply auto
      done
    show ?case
    proof (cases "cbox u v \<subseteq> d x")
      case True
      then show ?thesis
        apply (rule_tac x="{(x,cbox u v)} \<union> q1" in exI)
        apply rule
        unfolding * uv
        apply (rule tagged_division_union)
        apply (rule tagged_division_of_self)
        apply (rule p[unfolded xk uv] insertI1)+
        apply (rule q1)
        apply (rule int)
        apply rule
        apply (rule fine_union)
        apply (subst fine_def)
        defer
        apply (rule q1)
        unfolding Ball_def split_paired_All split_conv
        apply rule
        apply rule
        apply rule
        apply rule
        apply (erule insertE)
        apply (simp add: uv xk)
        apply (rule UnI2)
        apply (drule q1(3)[rule_format])
        unfolding xk uv
        apply auto
        done
    next
      case False
      from fine_division_exists[OF assms(2), of u v] guess q2 . note q2=this
      show ?thesis
        apply (rule_tac x="q2 \<union> q1" in exI)
        apply rule
        unfolding * uv
        apply (rule tagged_division_union q2 q1 int fine_union)+
        unfolding Ball_def split_paired_All split_conv
        apply rule
        apply (rule fine_union)
        apply (rule q1 q2)+
        apply rule
        apply rule
        apply rule
        apply rule
        apply (erule insertE)
        apply (rule UnI2)
        apply (simp add: False uv xk)
        apply (drule q1(3)[rule_format])
        using False
        unfolding xk uv
        apply auto
        done
    qed
  qed
qed


subsection \<open>Hence the main theorem about negligible sets.\<close>

lemma finite_product_dependent:
  assumes "finite s"
    and "\<And>x. x \<in> s \<Longrightarrow> finite (t x)"
  shows "finite {(i, j) |i j. i \<in> s \<and> j \<in> t i}"
  using assms
proof induct
  case (insert x s)
  have *: "{(i, j) |i j. i \<in> insert x s \<and> j \<in> t i} =
    (\<lambda>y. (x,y)) ` (t x) \<union> {(i, j) |i j. i \<in> s \<and> j \<in> t i}" by auto
  show ?case
    unfolding *
    apply (rule finite_UnI)
    using insert
    apply auto
    done
qed auto

lemma sum_sum_product:
  assumes "finite s"
    and "\<forall>i\<in>s. finite (t i)"
  shows "setsum (\<lambda>i. setsum (x i) (t i)::real) s =
    setsum (\<lambda>(i,j). x i j) {(i,j) | i j. i \<in> s \<and> j \<in> t i}"
  using assms
proof induct
  case (insert a s)
  have *: "{(i, j) |i j. i \<in> insert a s \<and> j \<in> t i} =
    (\<lambda>y. (a,y)) ` (t a) \<union> {(i, j) |i j. i \<in> s \<and> j \<in> t i}" by auto
  show ?case
    unfolding *
    apply (subst setsum.union_disjoint)
    unfolding setsum.insert[OF insert(1-2)]
    prefer 4
    apply (subst insert(3))
    unfolding add_right_cancel
  proof -
    show "setsum (x a) (t a) = (\<Sum>(xa, y)\<in> Pair a ` t a. x xa y)"
      apply (subst setsum.reindex)
      unfolding inj_on_def
      apply auto
      done
    show "finite {(i, j) |i j. i \<in> s \<and> j \<in> t i}"
      apply (rule finite_product_dependent)
      using insert
      apply auto
      done
  qed (insert insert, auto)
qed auto

lemma has_integral_negligible:
  fixes f :: "'b::euclidean_space \<Rightarrow> 'a::real_normed_vector"
  assumes "negligible s"
    and "\<forall>x\<in>(t - s). f x = 0"
  shows "(f has_integral 0) t"
proof -
  presume P: "\<And>f::'b::euclidean_space \<Rightarrow> 'a.
    \<And>a b. \<forall>x. x \<notin> s \<longrightarrow> f x = 0 \<Longrightarrow> (f has_integral 0) (cbox a b)"
  let ?f = "(\<lambda>x. if x \<in> t then f x else 0)"
  show ?thesis
    apply (rule_tac f="?f" in has_integral_eq)
    unfolding if_P
    apply (rule refl)
    apply (subst has_integral_alt)
    apply cases
    apply (subst if_P, assumption)
    unfolding if_not_P
  proof -
    assume "\<exists>a b. t = cbox a b"
    then guess a b apply - by (erule exE)+ note t = this
    show "(?f has_integral 0) t"
      unfolding t
      apply (rule P)
      using assms(2)
      unfolding t
      apply auto
      done
  next
    show "\<forall>e>0. \<exists>B>0. \<forall>a b. ball 0 B \<subseteq> cbox a b \<longrightarrow>
      (\<exists>z. ((\<lambda>x. if x \<in> t then ?f x else 0) has_integral z) (cbox a b) \<and> norm (z - 0) < e)"
      apply safe
      apply (rule_tac x=1 in exI)
      apply rule
      apply (rule zero_less_one)
      apply safe
      apply (rule_tac x=0 in exI)
      apply rule
      apply (rule P)
      using assms(2)
      apply auto
      done
  qed
next
  fix f :: "'b \<Rightarrow> 'a"
  fix a b :: 'b
  assume assm: "\<forall>x. x \<notin> s \<longrightarrow> f x = 0"
  show "(f has_integral 0) (cbox a b)"
    unfolding has_integral
  proof (safe, goal_cases)
    case prems: (1 e)
    then have "\<And>n. e / 2 / ((real n+1) * (2 ^ n)) > 0"
      apply -
      apply (rule divide_pos_pos)
      defer
      apply (rule mult_pos_pos)
      apply (auto simp add:field_simps)
      done
    note assms(1)[unfolded negligible_def has_integral,rule_format,OF this,of a b]
    note allI[OF this,of "\<lambda>x. x"]
    from choice[OF this] guess d .. note d=conjunctD2[OF this[rule_format]]
    show ?case
      apply (rule_tac x="\<lambda>x. d (nat \<lfloor>norm (f x)\<rfloor>) x" in exI)
    proof safe
      show "gauge (\<lambda>x. d (nat \<lfloor>norm (f x)\<rfloor>) x)"
        using d(1) unfolding gauge_def by auto
      fix p
      assume as: "p tagged_division_of (cbox a b)" "(\<lambda>x. d (nat \<lfloor>norm (f x)\<rfloor>) x) fine p"
      let ?goal = "norm ((\<Sum>(x, k)\<in>p. content k *\<^sub>R f x) - 0) < e"
      {
        presume "p \<noteq> {} \<Longrightarrow> ?goal"
        then show ?goal
          apply (cases "p = {}")
          using prems
          apply auto
          done
      }
      assume as': "p \<noteq> {}"
      from real_arch_simple[of "Max((\<lambda>(x,k). norm(f x)) ` p)"] guess N ..
      then have N: "\<forall>x\<in>(\<lambda>(x, k). norm (f x)) ` p. x \<le> real N"
        by (meson Max_ge as(1) dual_order.trans finite_imageI tagged_division_of_finite)
      have "\<forall>i. \<exists>q. q tagged_division_of (cbox a b) \<and> (d i) fine q \<and> (\<forall>(x, k)\<in>p. k \<subseteq> (d i) x \<longrightarrow> (x, k) \<in> q)"
        by (auto intro: tagged_division_finer[OF as(1) d(1)])
      from choice[OF this] guess q .. note q=conjunctD3[OF this[rule_format]]
      have *: "\<And>i. (\<Sum>(x, k)\<in>q i. content k *\<^sub>R indicator s x) \<ge> (0::real)"
        apply (rule setsum_nonneg)
        apply safe
        unfolding real_scaleR_def
        apply (drule tagged_division_ofD(4)[OF q(1)])
        apply (auto intro: mult_nonneg_nonneg)
        done
      have **: "finite s \<Longrightarrow> finite t \<Longrightarrow> (\<forall>(x,y) \<in> t. (0::real) \<le> g(x,y)) \<Longrightarrow>
        (\<forall>y\<in>s. \<exists>x. (x,y) \<in> t \<and> f(y) \<le> g(x,y)) \<Longrightarrow> setsum f s \<le> setsum g t" for f g s t
        apply (rule setsum_le_included[of s t g snd f])
        prefer 4
        apply safe
        apply (erule_tac x=x in ballE)
        apply (erule exE)
        apply (rule_tac x="(xa,x)" in bexI)
        apply auto
        done
      have "norm ((\<Sum>(x, k)\<in>p. content k *\<^sub>R f x) - 0) \<le> setsum (\<lambda>i. (real i + 1) *
        norm (setsum (\<lambda>(x,k). content k *\<^sub>R indicator s x :: real) (q i))) {..N+1}"
        unfolding real_norm_def setsum_distrib_left abs_of_nonneg[OF *] diff_0_right
        apply (rule order_trans)
        apply (rule norm_setsum)
        apply (subst sum_sum_product)
        prefer 3
      proof (rule **, safe)
        show "finite {(i, j) |i j. i \<in> {..N + 1} \<and> j \<in> q i}"
          apply (rule finite_product_dependent)
          using q
          apply auto
          done
        fix i a b
        assume as'': "(a, b) \<in> q i"
        show "0 \<le> (real i + 1) * (content b *\<^sub>R indicator s a)"
          unfolding real_scaleR_def
          using tagged_division_ofD(4)[OF q(1) as'']
          by (auto intro!: mult_nonneg_nonneg)
      next
        fix i :: nat
        show "finite (q i)"
          using q by auto
      next
        fix x k
        assume xk: "(x, k) \<in> p"
        define n where "n = nat \<lfloor>norm (f x)\<rfloor>"
        have *: "norm (f x) \<in> (\<lambda>(x, k). norm (f x)) ` p"
          using xk by auto
        have nfx: "real n \<le> norm (f x)" "norm (f x) \<le> real n + 1"
          unfolding n_def by auto
        then have "n \<in> {0..N + 1}"
          using N[rule_format,OF *] by auto
        moreover
        note as(2)[unfolded fine_def,rule_format,OF xk,unfolded split_conv]
        note q(3)[rule_format,OF xk,unfolded split_conv,rule_format,OF this]
        note this[unfolded n_def[symmetric]]
        moreover
        have "norm (content k *\<^sub>R f x) \<le> (real n + 1) * (content k * indicator s x)"
        proof (cases "x \<in> s")
          case False
          then show ?thesis
            using assm by auto
        next
          case True
          have *: "content k \<ge> 0"
            using tagged_division_ofD(4)[OF as(1) xk] by auto
          moreover
          have "content k * norm (f x) \<le> content k * (real n + 1)"
            apply (rule mult_mono)
            using nfx *
            apply auto
            done
          ultimately
          show ?thesis
            unfolding abs_mult
            using nfx True
            by (auto simp add: field_simps)
        qed
        ultimately show "\<exists>y. (y, x, k) \<in> {(i, j) |i j. i \<in> {..N + 1} \<and> j \<in> q i} \<and> norm (content k *\<^sub>R f x) \<le>
          (real y + 1) * (content k *\<^sub>R indicator s x)"
          apply (rule_tac x=n in exI)
          apply safe
          apply (rule_tac x=n in exI)
          apply (rule_tac x="(x,k)" in exI)
          apply safe
          apply auto
          done
      qed (insert as, auto)
      also have "\<dots> \<le> setsum (\<lambda>i. e / 2 / 2 ^ i) {..N+1}"
      proof (rule setsum_mono, goal_cases)
        case (1 i)
        then show ?case
          apply (subst mult.commute, subst pos_le_divide_eq[symmetric])
          using d(2)[rule_format, of "q i" i]
          using q[rule_format]
          apply (auto simp add: field_simps)
          done
      qed
      also have "\<dots> < e * inverse 2 * 2"
        unfolding divide_inverse setsum_distrib_left[symmetric]
        apply (rule mult_strict_left_mono)
        unfolding power_inverse [symmetric] lessThan_Suc_atMost[symmetric]
        apply (subst geometric_sum)
        using prems
        apply auto
        done
      finally show "?goal" by auto
    qed
  qed
qed

lemma has_integral_spike:
  fixes f :: "'b::euclidean_space \<Rightarrow> 'a::real_normed_vector"
  assumes "negligible s"
    and "(\<forall>x\<in>(t - s). g x = f x)"
    and "(f has_integral y) t"
  shows "(g has_integral y) t"
proof -
  {
    fix a b :: 'b
    fix f g :: "'b \<Rightarrow> 'a"
    fix y :: 'a
    assume as: "\<forall>x \<in> cbox a b - s. g x = f x" "(f has_integral y) (cbox a b)"
    have "((\<lambda>x. f x + (g x - f x)) has_integral (y + 0)) (cbox a b)"
      apply (rule has_integral_add[OF as(2)])
      apply (rule has_integral_negligible[OF assms(1)])
      using as
      apply auto
      done
    then have "(g has_integral y) (cbox a b)"
      by auto
  } note * = this
  show ?thesis
    apply (subst has_integral_alt)
    using assms(2-)
    apply -
    apply (rule cond_cases)
    apply safe
    apply (rule *)
    apply assumption+
    apply (subst(asm) has_integral_alt)
    unfolding if_not_P
    apply (erule_tac x=e in allE)
    apply safe
    apply (rule_tac x=B in exI)
    apply safe
    apply (erule_tac x=a in allE)
    apply (erule_tac x=b in allE)
    apply safe
    apply (rule_tac x=z in exI)
    apply safe
    apply (rule *[where fa2="\<lambda>x. if x\<in>t then f x else 0"])
    apply auto
    done
qed

lemma has_integral_spike_eq:
  assumes "negligible s"
    and "\<forall>x\<in>(t - s). g x = f x"
  shows "((f has_integral y) t \<longleftrightarrow> (g has_integral y) t)"
  apply rule
  apply (rule_tac[!] has_integral_spike[OF assms(1)])
  using assms(2)
  apply auto
  done

lemma integrable_spike:
  assumes "negligible s"
    and "\<forall>x\<in>(t - s). g x = f x"
    and "f integrable_on t"
  shows "g integrable_on  t"
  using assms
  unfolding integrable_on_def
  apply -
  apply (erule exE)
  apply rule
  apply (rule has_integral_spike)
  apply fastforce+
  done

lemma integral_spike:
  assumes "negligible s"
    and "\<forall>x\<in>(t - s). g x = f x"
  shows "integral t f = integral t g"
  using has_integral_spike_eq[OF assms] by (simp add: integral_def integrable_on_def)


subsection \<open>Some other trivialities about negligible sets.\<close>

lemma negligible_subset[intro]:
  assumes "negligible s"
    and "t \<subseteq> s"
  shows "negligible t"
  unfolding negligible_def
proof (safe, goal_cases)
  case (1 a b)
  show ?case
    using assms(1)[unfolded negligible_def,rule_format,of a b]
    apply -
    apply (rule has_integral_spike[OF assms(1)])
    defer
    apply assumption
    using assms(2)
    unfolding indicator_def
    apply auto
    done
qed

lemma negligible_diff[intro?]:
  assumes "negligible s"
  shows "negligible (s - t)"
  using assms by auto

lemma negligible_Int:
  assumes "negligible s \<or> negligible t"
  shows "negligible (s \<inter> t)"
  using assms by auto

lemma negligible_Un:
  assumes "negligible s"
    and "negligible t"
  shows "negligible (s \<union> t)"
  unfolding negligible_def
proof (safe, goal_cases)
  case (1 a b)
  note assm = assms[unfolded negligible_def,rule_format,of a b]
  then show ?case
    apply (subst has_integral_spike_eq[OF assms(2)])
    defer
    apply assumption
    unfolding indicator_def
    apply auto
    done
qed

lemma negligible_Un_eq[simp]: "negligible (s \<union> t) \<longleftrightarrow> negligible s \<and> negligible t"
  using negligible_Un by auto

lemma negligible_sing[intro]: "negligible {a::'a::euclidean_space}"
  using negligible_standard_hyperplane[OF SOME_Basis, of "a \<bullet> (SOME i. i \<in> Basis)"] by auto

lemma negligible_insert[simp]: "negligible (insert a s) \<longleftrightarrow> negligible s"
  apply (subst insert_is_Un)
  unfolding negligible_Un_eq
  apply auto
  done

lemma negligible_empty[iff]: "negligible {}"
  by auto

lemma negligible_finite[intro]:
  assumes "finite s"
  shows "negligible s"
  using assms by (induct s) auto

lemma negligible_Union[intro]:
  assumes "finite s"
    and "\<forall>t\<in>s. negligible t"
  shows "negligible(\<Union>s)"
  using assms by induct auto

lemma negligible:
  "negligible s \<longleftrightarrow> (\<forall>t::('a::euclidean_space) set. ((indicator s::'a\<Rightarrow>real) has_integral 0) t)"
  apply safe
  defer
  apply (subst negligible_def)
proof -
  fix t :: "'a set"
  assume as: "negligible s"
  have *: "(\<lambda>x. if x \<in> s \<inter> t then 1 else 0) = (\<lambda>x. if x\<in>t then if x\<in>s then 1 else 0 else 0)"
    by auto
  show "((indicator s::'a\<Rightarrow>real) has_integral 0) t"
    apply (subst has_integral_alt)
    apply cases
    apply (subst if_P,assumption)
    unfolding if_not_P
    apply safe
    apply (rule as[unfolded negligible_def,rule_format])
    apply (rule_tac x=1 in exI)
    apply safe
    apply (rule zero_less_one)
    apply (rule_tac x=0 in exI)
    using negligible_subset[OF as,of "s \<inter> t"]
    unfolding negligible_def indicator_def [abs_def]
    unfolding *
    apply auto
    done
qed auto


subsection \<open>Finite case of the spike theorem is quite commonly needed.\<close>

lemma has_integral_spike_finite:
  assumes "finite s"
    and "\<forall>x\<in>t-s. g x = f x"
    and "(f has_integral y) t"
  shows "(g has_integral y) t"
  apply (rule has_integral_spike)
  using assms
  apply auto
  done

lemma has_integral_spike_finite_eq:
  assumes "finite s"
    and "\<forall>x\<in>t-s. g x = f x"
  shows "((f has_integral y) t \<longleftrightarrow> (g has_integral y) t)"
  apply rule
  apply (rule_tac[!] has_integral_spike_finite)
  using assms
  apply auto
  done

lemma integrable_spike_finite:
  assumes "finite s"
    and "\<forall>x\<in>t-s. g x = f x"
    and "f integrable_on t"
  shows "g integrable_on  t"
  using assms
  unfolding integrable_on_def
  apply safe
  apply (rule_tac x=y in exI)
  apply (rule has_integral_spike_finite)
  apply auto
  done


subsection \<open>In particular, the boundary of an interval is negligible.\<close>

lemma negligible_frontier_interval: "negligible(cbox (a::'a::euclidean_space) b - box a b)"
proof -
  let ?A = "\<Union>((\<lambda>k. {x. x\<bullet>k = a\<bullet>k} \<union> {x::'a. x\<bullet>k = b\<bullet>k}) ` Basis)"
  have "cbox a b - box a b \<subseteq> ?A"
    apply rule unfolding Diff_iff mem_box
    apply simp
    apply(erule conjE bexE)+
    apply(rule_tac x=i in bexI)
    apply auto
    done
  then show ?thesis
    apply -
    apply (rule negligible_subset[of ?A])
    apply (rule negligible_Union[OF finite_imageI])
    apply auto
    done
qed

lemma has_integral_spike_interior:
  assumes "\<forall>x\<in>box a b. g x = f x"
    and "(f has_integral y) (cbox a b)"
  shows "(g has_integral y) (cbox a b)"
  apply (rule has_integral_spike[OF negligible_frontier_interval _ assms(2)])
  using assms(1)
  apply auto
  done

lemma has_integral_spike_interior_eq:
  assumes "\<forall>x\<in>box a b. g x = f x"
  shows "(f has_integral y) (cbox a b) \<longleftrightarrow> (g has_integral y) (cbox a b)"
  apply rule
  apply (rule_tac[!] has_integral_spike_interior)
  using assms
  apply auto
  done

lemma integrable_spike_interior:
  assumes "\<forall>x\<in>box a b. g x = f x"
    and "f integrable_on cbox a b"
  shows "g integrable_on cbox a b"
  using assms
  unfolding integrable_on_def
  using has_integral_spike_interior[OF assms(1)]
  by auto


subsection \<open>Integrability of continuous functions.\<close>

lemma operative_approximable:
  fixes f :: "'b::euclidean_space \<Rightarrow> 'a::banach"
  assumes "0 \<le> e"
  shows "comm_monoid.operative op \<and> True (\<lambda>i. \<exists>g. (\<forall>x\<in>i. norm (f x - g (x::'b)) \<le> e) \<and> g integrable_on i)"
  unfolding comm_monoid.operative_def[OF comm_monoid_and]
proof safe
  fix a b :: 'b
  show "\<exists>g. (\<forall>x\<in>cbox a b. norm (f x - g x) \<le> e) \<and> g integrable_on cbox a b"
    if "content (cbox a b) = 0"
    apply (rule_tac x=f in exI)
    using assms that
    apply (auto intro!: integrable_on_null)
    done
  {
    fix c g
    fix k :: 'b
    assume as: "\<forall>x\<in>cbox a b. norm (f x - g x) \<le> e" "g integrable_on cbox a b"
    assume k: "k \<in> Basis"
    show "\<exists>g. (\<forall>x\<in>cbox a b \<inter> {x. x \<bullet> k \<le> c}. norm (f x - g x) \<le> e) \<and> g integrable_on cbox a b \<inter> {x. x \<bullet> k \<le> c}"
      "\<exists>g. (\<forall>x\<in>cbox a b \<inter> {x. c \<le> x \<bullet> k}. norm (f x - g x) \<le> e) \<and> g integrable_on cbox a b \<inter> {x. c \<le> x \<bullet> k}"
      apply (rule_tac[!] x=g in exI)
      using as(1) integrable_split[OF as(2) k]
      apply auto
      done
  }
  fix c k g1 g2
  assume as: "\<forall>x\<in>cbox a b \<inter> {x. x \<bullet> k \<le> c}. norm (f x - g1 x) \<le> e" "g1 integrable_on cbox a b \<inter> {x. x \<bullet> k \<le> c}"
    "\<forall>x\<in>cbox a b \<inter> {x. c \<le> x \<bullet> k}. norm (f x - g2 x) \<le> e" "g2 integrable_on cbox a b \<inter> {x. c \<le> x \<bullet> k}"
  assume k: "k \<in> Basis"
  let ?g = "\<lambda>x. if x\<bullet>k = c then f x else if x\<bullet>k \<le> c then g1 x else g2 x"
  show "\<exists>g. (\<forall>x\<in>cbox a b. norm (f x - g x) \<le> e) \<and> g integrable_on cbox a b"
    apply (rule_tac x="?g" in exI)
    apply safe
  proof goal_cases
    case (1 x)
    then show ?case
      apply -
      apply (cases "x\<bullet>k=c")
      apply (case_tac "x\<bullet>k < c")
      using as assms
      apply auto
      done
  next
    case 2
    presume "?g integrable_on cbox a b \<inter> {x. x \<bullet> k \<le> c}"
      and "?g integrable_on cbox a b \<inter> {x. x \<bullet> k \<ge> c}"
    then guess h1 h2 unfolding integrable_on_def by auto
    from has_integral_split[OF this k] show ?case
      unfolding integrable_on_def by auto
  next
    show "?g integrable_on cbox a b \<inter> {x. x \<bullet> k \<le> c}" "?g integrable_on cbox a b \<inter> {x. x \<bullet> k \<ge> c}"
      apply(rule_tac[!] integrable_spike[OF negligible_standard_hyperplane[of k c]])
      using k as(2,4)
      apply auto
      done
  qed
qed

lemma comm_monoid_set_F_and: "comm_monoid_set.F op \<and> True f s \<longleftrightarrow> (finite s \<longrightarrow> (\<forall>x\<in>s. f x))"
proof -
  interpret bool: comm_monoid_set "op \<and>" True
    proof qed auto
  show ?thesis
    by (induction s rule: infinite_finite_induct) auto
qed

lemma approximable_on_division:
  fixes f :: "'b::euclidean_space \<Rightarrow> 'a::banach"
  assumes "0 \<le> e"
    and "d division_of (cbox a b)"
    and "\<forall>i\<in>d. \<exists>g. (\<forall>x\<in>i. norm (f x - g x) \<le> e) \<and> g integrable_on i"
  obtains g where "\<forall>x\<in>cbox a b. norm (f x - g x) \<le> e" "g integrable_on cbox a b"
proof -
  note * = comm_monoid_set.operative_division[OF comm_monoid_set_and operative_approximable[OF assms(1)] assms(2)]
  from assms(3) this[unfolded comm_monoid_set_F_and, of f] division_of_finite[OF assms(2)]
  guess g by auto
  then show thesis
    apply -
    apply (rule that[of g])
    apply auto
    done
qed

lemma integrable_continuous:
  fixes f :: "'b::euclidean_space \<Rightarrow> 'a::banach"
  assumes "continuous_on (cbox a b) f"
  shows "f integrable_on cbox a b"
proof (rule integrable_uniform_limit, safe)
  fix e :: real
  assume e: "e > 0"
  from compact_uniformly_continuous[OF assms compact_cbox,unfolded uniformly_continuous_on_def,rule_format,OF e] guess d ..
  note d=conjunctD2[OF this,rule_format]
  from fine_division_exists[OF gauge_ball[OF d(1)], of a b] guess p . note p=this
  note p' = tagged_division_ofD[OF p(1)]
  have *: "\<forall>i\<in>snd ` p. \<exists>g. (\<forall>x\<in>i. norm (f x - g x) \<le> e) \<and> g integrable_on i"
  proof (safe, unfold snd_conv)
    fix x l
    assume as: "(x, l) \<in> p"
    from p'(4)[OF this] guess a b by (elim exE) note l=this
    show "\<exists>g. (\<forall>x\<in>l. norm (f x - g x) \<le> e) \<and> g integrable_on l"
      apply (rule_tac x="\<lambda>y. f x" in exI)
    proof safe
      show "(\<lambda>y. f x) integrable_on l"
        unfolding integrable_on_def l
        apply rule
        apply (rule has_integral_const)
        done
      fix y
      assume y: "y \<in> l"
      note fineD[OF p(2) as,unfolded subset_eq,rule_format,OF this]
      note d(2)[OF _ _ this[unfolded mem_ball]]
      then show "norm (f y - f x) \<le> e"
        using y p'(2-3)[OF as] unfolding dist_norm l norm_minus_commute by fastforce
    qed
  qed
  from e have "e \<ge> 0"
    by auto
  from approximable_on_division[OF this division_of_tagged_division[OF p(1)] *] guess g .
  then show "\<exists>g. (\<forall>x\<in>cbox a b. norm (f x - g x) \<le> e) \<and> g integrable_on cbox a b"
    by auto
qed

lemma integrable_continuous_real:
  fixes f :: "real \<Rightarrow> 'a::banach"
  assumes "continuous_on {a .. b} f"
  shows "f integrable_on {a .. b}"
  by (metis assms box_real(2) integrable_continuous)

subsection \<open>Specialization of additivity to one dimension.\<close>

subsection \<open>Special case of additivity we need for the FTC.\<close>

lemma additive_tagged_division_1:
  fixes f :: "real \<Rightarrow> 'a::real_normed_vector"
  assumes "a \<le> b"
    and "p tagged_division_of {a..b}"
  shows "setsum (\<lambda>(x,k). f(Sup k) - f(Inf k)) p = f b - f a"
proof -
  let ?f = "(\<lambda>k::(real) set. if k = {} then 0 else f(interval_upperbound k) - f(interval_lowerbound k))"
  have ***: "\<forall>i\<in>Basis. a \<bullet> i \<le> b \<bullet> i"
    using assms by auto
  have *: "add.operative ?f"
    unfolding add.operative_1_lt box_eq_empty
    by auto
  have **: "cbox a b \<noteq> {}"
    using assms(1) by auto
  note setsum.operative_tagged_division[OF * assms(2)[simplified box_real[symmetric]]]
  note * = this[unfolded if_not_P[OF **] interval_bounds[OF ***],symmetric]
  show ?thesis
    unfolding *
    apply (rule setsum.cong)
    unfolding split_paired_all split_conv
    using assms(2)
    apply auto
    done
qed


subsection \<open>A useful lemma allowing us to factor out the content size.\<close>

lemma has_integral_factor_content:
  "(f has_integral i) (cbox a b) \<longleftrightarrow>
    (\<forall>e>0. \<exists>d. gauge d \<and> (\<forall>p. p tagged_division_of (cbox a b) \<and> d fine p \<longrightarrow>
      norm (setsum (\<lambda>(x,k). content k *\<^sub>R f x) p - i) \<le> e * content (cbox a b)))"
proof (cases "content (cbox a b) = 0")
  case True
  show ?thesis
    unfolding has_integral_null_eq[OF True]
    apply safe
    apply (rule, rule, rule gauge_trivial, safe)
    unfolding setsum_content_null[OF True] True
    defer
    apply (erule_tac x=1 in allE)
    apply safe
    defer
    apply (rule fine_division_exists[of _ a b])
    apply assumption
    apply (erule_tac x=p in allE)
    unfolding setsum_content_null[OF True]
    apply auto
    done
next
  case False
  note F = this[unfolded content_lt_nz[symmetric]]
  let ?P = "\<lambda>e opp. \<exists>d. gauge d \<and>
    (\<forall>p. p tagged_division_of (cbox a b) \<and> d fine p \<longrightarrow> opp (norm ((\<Sum>(x, k)\<in>p. content k *\<^sub>R f x) - i)) e)"
  show ?thesis
    apply (subst has_integral)
  proof safe
    fix e :: real
    assume e: "e > 0"
    {
      assume "\<forall>e>0. ?P e op <"
      then show "?P (e * content (cbox a b)) op \<le>"
        apply (erule_tac x="e * content (cbox a b)" in allE)
        apply (erule impE)
        defer
        apply (erule exE,rule_tac x=d in exI)
        using F e
        apply (auto simp add:field_simps)
        done
    }
    {
      assume "\<forall>e>0. ?P (e * content (cbox a b)) op \<le>"
      then show "?P e op <"
        apply (erule_tac x="e / 2 / content (cbox a b)" in allE)
        apply (erule impE)
        defer
        apply (erule exE,rule_tac x=d in exI)
        using F e
        apply (auto simp add: field_simps)
        done
    }
  qed
qed

lemma has_integral_factor_content_real:
  "(f has_integral i) {a .. b::real} \<longleftrightarrow>
    (\<forall>e>0. \<exists>d. gauge d \<and> (\<forall>p. p tagged_division_of {a .. b}  \<and> d fine p \<longrightarrow>
      norm (setsum (\<lambda>(x,k). content k *\<^sub>R f x) p - i) \<le> e * content {a .. b} ))"
  unfolding box_real[symmetric]
  by (rule has_integral_factor_content)


subsection \<open>Fundamental theorem of calculus.\<close>

lemma interval_bounds_real:
  fixes q b :: real
  assumes "a \<le> b"
  shows "Sup {a..b} = b"
    and "Inf {a..b} = a"
  using assms by auto

lemma fundamental_theorem_of_calculus:
  fixes f :: "real \<Rightarrow> 'a::banach"
  assumes "a \<le> b"
    and "\<forall>x\<in>{a .. b}. (f has_vector_derivative f' x) (at x within {a .. b})"
  shows "(f' has_integral (f b - f a)) {a .. b}"
  unfolding has_integral_factor_content box_real[symmetric]
proof safe
  fix e :: real
  assume e: "e > 0"
  note assm = assms(2)[unfolded has_vector_derivative_def has_derivative_within_alt]
  have *: "\<And>P Q. \<forall>x\<in>{a .. b}. P x \<and> (\<forall>e>0. \<exists>d>0. Q x e d) \<Longrightarrow> \<forall>x. \<exists>(d::real)>0. x\<in>{a .. b} \<longrightarrow> Q x e d"
    using e by blast
  note this[OF assm,unfolded gauge_existence_lemma]
  from choice[OF this,unfolded Ball_def[symmetric]] guess d ..
  note d=conjunctD2[OF this[rule_format],rule_format]
  show "\<exists>d. gauge d \<and> (\<forall>p. p tagged_division_of (cbox a b) \<and> d fine p \<longrightarrow>
    norm ((\<Sum>(x, k)\<in>p. content k *\<^sub>R f' x) - (f b - f a)) \<le> e * content (cbox a b))"
    apply (rule_tac x="\<lambda>x. ball x (d x)" in exI)
    apply safe
    apply (rule gauge_ball_dependent)
    apply rule
    apply (rule d(1))
  proof -
    fix p
    assume as: "p tagged_division_of cbox a b" "(\<lambda>x. ball x (d x)) fine p"
    show "norm ((\<Sum>(x, k)\<in>p. content k *\<^sub>R f' x) - (f b - f a)) \<le> e * content (cbox a b)"
      unfolding content_real[OF assms(1), simplified box_real[symmetric]] additive_tagged_division_1[OF assms(1) as(1)[simplified box_real],of f,symmetric]
      unfolding additive_tagged_division_1[OF assms(1) as(1)[simplified box_real],of "\<lambda>x. x",symmetric]
      unfolding setsum_distrib_left
      defer
      unfolding setsum_subtractf[symmetric]
    proof (rule setsum_norm_le,safe)
      fix x k
      assume "(x, k) \<in> p"
      note xk = tagged_division_ofD(2-4)[OF as(1) this]
      from this(3) guess u v by (elim exE) note k=this
      have *: "u \<le> v"
        using xk unfolding k by auto
      have ball: "\<forall>xa\<in>k. xa \<in> ball x (d x)"
        using as(2)[unfolded fine_def,rule_format,OF \<open>(x,k)\<in>p\<close>,unfolded split_conv subset_eq] .
      have "norm ((v - u) *\<^sub>R f' x - (f v - f u)) \<le>
        norm (f u - f x - (u - x) *\<^sub>R f' x) + norm (f v - f x - (v - x) *\<^sub>R f' x)"
        apply (rule order_trans[OF _ norm_triangle_ineq4])
        apply (rule eq_refl)
        apply (rule arg_cong[where f=norm])
        unfolding scaleR_diff_left
        apply (auto simp add:algebra_simps)
        done
      also have "\<dots> \<le> e * norm (u - x) + e * norm (v - x)"
        apply (rule add_mono)
        apply (rule d(2)[of "x" "u",unfolded o_def])
        prefer 4
        apply (rule d(2)[of "x" "v",unfolded o_def])
        using ball[rule_format,of u] ball[rule_format,of v]
        using xk(1-2)
        unfolding k subset_eq
        apply (auto simp add:dist_real_def)
        done
      also have "\<dots> \<le> e * (Sup k - Inf k)"
        unfolding k interval_bounds_real[OF *]
        using xk(1)
        unfolding k
        by (auto simp add: dist_real_def field_simps)
      finally show "norm (content k *\<^sub>R f' x - (f (Sup k) - f (Inf k))) \<le>
        e * (Sup k - Inf k)"
        unfolding box_real k interval_bounds_real[OF *] content_real[OF *]
          interval_upperbound_real interval_lowerbound_real
          .
    qed
  qed
qed

lemma ident_has_integral:
  fixes a::real
  assumes "a \<le> b"
  shows "((\<lambda>x. x) has_integral (b\<^sup>2 - a\<^sup>2) / 2) {a..b}"
proof -
  have "((\<lambda>x. x) has_integral inverse 2 * b\<^sup>2 - inverse 2 * a\<^sup>2) {a..b}"
    apply (rule fundamental_theorem_of_calculus [OF assms], clarify)
    unfolding power2_eq_square
    by (rule derivative_eq_intros | simp)+
  then show ?thesis
    by (simp add: field_simps)
qed

lemma integral_ident [simp]:
  fixes a::real
  assumes "a \<le> b"
  shows "integral {a..b} (\<lambda>x. x) = (if a \<le> b then (b\<^sup>2 - a\<^sup>2) / 2 else 0)"
using ident_has_integral integral_unique by fastforce

lemma ident_integrable_on:
  fixes a::real
  shows "(\<lambda>x. x) integrable_on {a..b}"
by (metis atLeastatMost_empty_iff integrable_on_def has_integral_empty ident_has_integral)


subsection \<open>Taylor series expansion\<close>

lemma (in bounded_bilinear) setsum_prod_derivatives_has_vector_derivative:
  assumes "p>0"
  and f0: "Df 0 = f"
  and Df: "\<And>m t. m < p \<Longrightarrow> a \<le> t \<Longrightarrow> t \<le> b \<Longrightarrow>
    (Df m has_vector_derivative Df (Suc m) t) (at t within {a .. b})"
  and g0: "Dg 0 = g"
  and Dg: "\<And>m t. m < p \<Longrightarrow> a \<le> t \<Longrightarrow> t \<le> b \<Longrightarrow>
    (Dg m has_vector_derivative Dg (Suc m) t) (at t within {a .. b})"
  and ivl: "a \<le> t" "t \<le> b"
  shows "((\<lambda>t. \<Sum>i<p. (-1)^i *\<^sub>R prod (Df i t) (Dg (p - Suc i) t))
    has_vector_derivative
      prod (f t) (Dg p t) - (-1)^p *\<^sub>R prod (Df p t) (g t))
    (at t within {a .. b})"
  using assms
proof cases
  assume p: "p \<noteq> 1"
  define p' where "p' = p - 2"
  from assms p have p': "{..<p} = {..Suc p'}" "p = Suc (Suc p')"
    by (auto simp: p'_def)
  have *: "\<And>i. i \<le> p' \<Longrightarrow> Suc (Suc p' - i) = (Suc (Suc p') - i)"
    by auto
  let ?f = "\<lambda>i. (-1) ^ i *\<^sub>R (prod (Df i t) (Dg ((p - i)) t))"
  have "(\<Sum>i<p. (-1) ^ i *\<^sub>R (prod (Df i t) (Dg (Suc (p - Suc i)) t) +
    prod (Df (Suc i) t) (Dg (p - Suc i) t))) =
    (\<Sum>i\<le>(Suc p'). ?f i - ?f (Suc i))"
    by (auto simp: algebra_simps p'(2) numeral_2_eq_2 * lessThan_Suc_atMost)
  also note setsum_telescope
  finally
  have "(\<Sum>i<p. (-1) ^ i *\<^sub>R (prod (Df i t) (Dg (Suc (p - Suc i)) t) +
    prod (Df (Suc i) t) (Dg (p - Suc i) t)))
    = prod (f t) (Dg p t) - (- 1) ^ p *\<^sub>R prod (Df p t) (g t)"
    unfolding p'[symmetric]
    by (simp add: assms)
  thus ?thesis
    using assms
    by (auto intro!: derivative_eq_intros has_vector_derivative)
qed (auto intro!: derivative_eq_intros has_vector_derivative)

lemma
  fixes f::"real\<Rightarrow>'a::banach"
  assumes "p>0"
  and f0: "Df 0 = f"
  and Df: "\<And>m t. m < p \<Longrightarrow> a \<le> t \<Longrightarrow> t \<le> b \<Longrightarrow>
    (Df m has_vector_derivative Df (Suc m) t) (at t within {a .. b})"
  and ivl: "a \<le> b"
  defines "i \<equiv> \<lambda>x. ((b - x) ^ (p - 1) / fact (p - 1)) *\<^sub>R Df p x"
  shows taylor_has_integral:
    "(i has_integral f b - (\<Sum>i<p. ((b - a) ^ i / fact i) *\<^sub>R Df i a)) {a..b}"
  and taylor_integral:
    "f b = (\<Sum>i<p. ((b - a) ^ i / fact i) *\<^sub>R Df i a) + integral {a..b} i"
  and taylor_integrable:
    "i integrable_on {a .. b}"
proof goal_cases
  case 1
  interpret bounded_bilinear "scaleR::real\<Rightarrow>'a\<Rightarrow>'a"
    by (rule bounded_bilinear_scaleR)
  define g where "g s = (b - s)^(p - 1)/fact (p - 1)" for s
  define Dg where [abs_def]:
    "Dg n s = (if n < p then (-1)^n * (b - s)^(p - 1 - n) / fact (p - 1 - n) else 0)" for n s
  have g0: "Dg 0 = g"
    using \<open>p > 0\<close>
    by (auto simp add: Dg_def divide_simps g_def split: if_split_asm)
  {
    fix m
    assume "p > Suc m"
    hence "p - Suc m = Suc (p - Suc (Suc m))"
      by auto
    hence "real (p - Suc m) * fact (p - Suc (Suc m)) = fact (p - Suc m)"
      by auto
  } note fact_eq = this
  have Dg: "\<And>m t. m < p \<Longrightarrow> a \<le> t \<Longrightarrow> t \<le> b \<Longrightarrow>
    (Dg m has_vector_derivative Dg (Suc m) t) (at t within {a .. b})"
    unfolding Dg_def
    by (auto intro!: derivative_eq_intros simp: has_vector_derivative_def fact_eq divide_simps)
  let ?sum = "\<lambda>t. \<Sum>i<p. (- 1) ^ i *\<^sub>R Dg i t *\<^sub>R Df (p - Suc i) t"
  from setsum_prod_derivatives_has_vector_derivative[of _ Dg _ _ _ Df,
      OF \<open>p > 0\<close> g0 Dg f0 Df]
  have deriv: "\<And>t. a \<le> t \<Longrightarrow> t \<le> b \<Longrightarrow>
    (?sum has_vector_derivative
      g t *\<^sub>R Df p t - (- 1) ^ p *\<^sub>R Dg p t *\<^sub>R f t) (at t within {a..b})"
    by auto
  from fundamental_theorem_of_calculus[rule_format, OF \<open>a \<le> b\<close> deriv]
  have "(i has_integral ?sum b - ?sum a) {a .. b}"
    using atLeastatMost_empty'[simp del]
    by (simp add: i_def g_def Dg_def)
  also
  have one: "(- 1) ^ p' * (- 1) ^ p' = (1::real)"
    and "{..<p} \<inter> {i. p = Suc i} = {p - 1}"
    for p'
    using \<open>p > 0\<close>
    by (auto simp: power_mult_distrib[symmetric])
  then have "?sum b = f b"
    using Suc_pred'[OF \<open>p > 0\<close>]
    by (simp add: diff_eq_eq Dg_def power_0_left le_Suc_eq if_distrib
        cond_application_beta setsum.If_cases f0)
  also
  have "{..<p} = (\<lambda>x. p - x - 1) ` {..<p}"
  proof safe
    fix x
    assume "x < p"
    thus "x \<in> (\<lambda>x. p - x - 1) ` {..<p}"
      by (auto intro!: image_eqI[where x = "p - x - 1"])
  qed simp
  from _ this
  have "?sum a = (\<Sum>i<p. ((b - a) ^ i / fact i) *\<^sub>R Df i a)"
    by (rule setsum.reindex_cong) (auto simp add: inj_on_def Dg_def one)
  finally show c: ?case .
  case 2 show ?case using c integral_unique by force
  case 3 show ?case using c by force
qed


subsection \<open>Attempt a systematic general set of "offset" results for components.\<close>

lemma gauge_modify:
  assumes "(\<forall>s. open s \<longrightarrow> open {x. f(x) \<in> s})" "gauge d"
  shows "gauge (\<lambda>x. {y. f y \<in> d (f x)})"
  using assms
  unfolding gauge_def
  apply safe
  defer
  apply (erule_tac x="f x" in allE)
  apply (erule_tac x="d (f x)" in allE)
  apply auto
  done


subsection \<open>Only need trivial subintervals if the interval itself is trivial.\<close>

lemma division_of_nontrivial:
  fixes s :: "'a::euclidean_space set set"
  assumes "s division_of (cbox a b)"
    and "content (cbox a b) \<noteq> 0"
  shows "{k. k \<in> s \<and> content k \<noteq> 0} division_of (cbox a b)"
  using assms(1)
  apply -
proof (induct "card s" arbitrary: s rule: nat_less_induct)
  fix s::"'a set set"
  assume assm: "s division_of (cbox a b)"
    "\<forall>m<card s. \<forall>x. m = card x \<longrightarrow>
      x division_of (cbox a b) \<longrightarrow> {k \<in> x. content k \<noteq> 0} division_of (cbox a b)"
  note s = division_ofD[OF assm(1)]
  let ?thesis = "{k \<in> s. content k \<noteq> 0} division_of (cbox a b)"
  {
    presume *: "{k \<in> s. content k \<noteq> 0} \<noteq> s \<Longrightarrow> ?thesis"
    show ?thesis
      apply cases
      defer
      apply (rule *)
      apply assumption
      using assm(1)
      apply auto
      done
  }
  assume noteq: "{k \<in> s. content k \<noteq> 0} \<noteq> s"
  then obtain k where k: "k \<in> s" "content k = 0"
    by auto
  from s(4)[OF k(1)] guess c d by (elim exE) note k=k this
  from k have "card s > 0"
    unfolding card_gt_0_iff using assm(1) by auto
  then have card: "card (s - {k}) < card s"
    using assm(1) k(1)
    apply (subst card_Diff_singleton_if)
    apply auto
    done
  have *: "closed (\<Union>(s - {k}))"
    apply (rule closed_Union)
    defer
    apply rule
    apply (drule DiffD1,drule s(4))
    using assm(1)
    apply auto
    done
  have "k \<subseteq> \<Union>(s - {k})"
    apply safe
    apply (rule *[unfolded closed_limpt,rule_format])
    unfolding islimpt_approachable
  proof safe
    fix x
    fix e :: real
    assume as: "x \<in> k" "e > 0"
    from k(2)[unfolded k content_eq_0] guess i ..
    then have i:"c\<bullet>i = d\<bullet>i" "i\<in>Basis"
      using s(3)[OF k(1),unfolded k] unfolding box_ne_empty by auto
    then have xi: "x\<bullet>i = d\<bullet>i"
      using as unfolding k mem_box by (metis antisym)
    define y where "y = (\<Sum>j\<in>Basis. (if j = i then if c\<bullet>i \<le> (a\<bullet>i + b\<bullet>i) / 2 then c\<bullet>i +
      min e (b\<bullet>i - c\<bullet>i) / 2 else c\<bullet>i - min e (c\<bullet>i - a\<bullet>i) / 2 else x\<bullet>j) *\<^sub>R j)"
    show "\<exists>x'\<in>\<Union>(s - {k}). x' \<noteq> x \<and> dist x' x < e"
      apply (rule_tac x=y in bexI)
    proof
      have "d \<in> cbox c d"
        using s(3)[OF k(1)]
        unfolding k box_eq_empty mem_box
        by (fastforce simp add: not_less)
      then have "d \<in> cbox a b"
        using s(2)[OF k(1)]
        unfolding k
        by auto
      note di = this[unfolded mem_box,THEN bspec[where x=i]]
      then have xyi: "y\<bullet>i \<noteq> x\<bullet>i"
        unfolding y_def i xi
        using as(2) assms(2)[unfolded content_eq_0] i(2)
        by (auto elim!: ballE[of _ _ i])
      then show "y \<noteq> x"
        unfolding euclidean_eq_iff[where 'a='a] using i by auto
      have *: "Basis = insert i (Basis - {i})"
        using i by auto
      have "norm (y - x) < e + setsum (\<lambda>i. 0) Basis"
        apply (rule le_less_trans[OF norm_le_l1])
        apply (subst *)
        apply (subst setsum.insert)
        prefer 3
        apply (rule add_less_le_mono)
      proof -
        show "\<bar>(y - x) \<bullet> i\<bar> < e"
          using di as(2) y_def i xi by (auto simp: inner_simps)
        show "(\<Sum>i\<in>Basis - {i}. \<bar>(y - x) \<bullet> i\<bar>) \<le> (\<Sum>i\<in>Basis. 0)"
          unfolding y_def by (auto simp: inner_simps)
      qed auto
      then show "dist y x < e"
        unfolding dist_norm by auto
      have "y \<notin> k"
        unfolding k mem_box
        apply rule
        apply (erule_tac x=i in ballE)
        using xyi k i xi
        apply auto
        done
      moreover
      have "y \<in> \<Union>s"
        using set_rev_mp[OF as(1) s(2)[OF k(1)]] as(2) di i
        unfolding s mem_box y_def
        by (auto simp: field_simps elim!: ballE[of _ _ i])
      ultimately
      show "y \<in> \<Union>(s - {k})" by auto
    qed
  qed
  then have "\<Union>(s - {k}) = cbox a b"
    unfolding s(6)[symmetric] by auto
  then have  "{ka \<in> s - {k}. content ka \<noteq> 0} division_of (cbox a b)"
    apply -
    apply (rule assm(2)[rule_format,OF card refl])
    apply (rule division_ofI)
    defer
    apply (rule_tac[1-4] s)
    using assm(1)
    apply auto
    done
  moreover
  have "{ka \<in> s - {k}. content ka \<noteq> 0} = {k \<in> s. content k \<noteq> 0}"
    using k by auto
  ultimately show ?thesis by auto
qed


subsection \<open>Integrability on subintervals.\<close>

lemma operative_integrable:
  fixes f :: "'b::euclidean_space \<Rightarrow> 'a::banach"
  shows "comm_monoid.operative op \<and> True (\<lambda>i. f integrable_on i)"
  unfolding comm_monoid.operative_def[OF comm_monoid_and]
  apply safe
  apply (subst integrable_on_def)
  unfolding has_integral_null_eq
  apply (rule, rule refl)
  apply (rule, assumption, assumption)+
  unfolding integrable_on_def
  by (auto intro!: has_integral_split)

lemma integrable_subinterval:
  fixes f :: "'b::euclidean_space \<Rightarrow> 'a::banach"
  assumes "f integrable_on cbox a b"
    and "cbox c d \<subseteq> cbox a b"
  shows "f integrable_on cbox c d"
  apply (cases "cbox c d = {}")
  defer
  apply (rule partial_division_extend_1[OF assms(2)],assumption)
  using comm_monoid_set.operative_division[OF comm_monoid_set_and operative_integrable,symmetric,of _ _ _ f] assms(1)
  apply (auto simp: comm_monoid_set_F_and)
  done

lemma integrable_subinterval_real:
  fixes f :: "real \<Rightarrow> 'a::banach"
  assumes "f integrable_on {a .. b}"
    and "{c .. d} \<subseteq> {a .. b}"
  shows "f integrable_on {c .. d}"
  by (metis assms(1) assms(2) box_real(2) integrable_subinterval)


subsection \<open>Combining adjacent intervals in 1 dimension.\<close>

lemma has_integral_combine:
  fixes a b c :: real
  assumes "a \<le> c"
    and "c \<le> b"
    and "(f has_integral i) {a .. c}"
    and "(f has_integral (j::'a::banach)) {c .. b}"
  shows "(f has_integral (i + j)) {a .. b}"
proof -
  interpret comm_monoid "lift_option plus" "Some (0::'a)"
    by (rule comm_monoid_lift_option)
      (rule add.comm_monoid_axioms)
  note operative_integral [of f, unfolded operative_1_le]
  note conjunctD2 [OF this, rule_format]
  note * = this(2) [OF conjI [OF assms(1-2)],
    unfolded if_P [OF assms(3)]]
  then have "f integrable_on cbox a b"
    apply -
    apply (rule ccontr)
    apply (subst(asm) if_P)
    defer
    apply (subst(asm) if_P)
    using assms(3-)
    apply auto
    done
  with *
  show ?thesis
    apply -
    apply (subst(asm) if_P)
    defer
    apply (subst(asm) if_P)
    defer
    apply (subst(asm) if_P)
    using assms(3-)
    apply (auto simp add: integrable_on_def integral_unique)
    done
qed

lemma integral_combine:
  fixes f :: "real \<Rightarrow> 'a::banach"
  assumes "a \<le> c"
    and "c \<le> b"
    and "f integrable_on {a .. b}"
  shows "integral {a .. c} f + integral {c .. b} f = integral {a .. b} f"
  apply (rule integral_unique[symmetric])
  apply (rule has_integral_combine[OF assms(1-2)])
  apply (metis assms(2) assms(3) atLeastatMost_subset_iff box_real(2) content_pos_le content_real_eq_0 integrable_integral integrable_subinterval le_add_same_cancel2 monoid_add_class.add.left_neutral)
  by (metis assms(1) assms(3) atLeastatMost_subset_iff box_real(2) content_pos_le content_real_eq_0 integrable_integral integrable_subinterval le_add_same_cancel1 monoid_add_class.add.right_neutral)

lemma integrable_combine:
  fixes f :: "real \<Rightarrow> 'a::banach"
  assumes "a \<le> c"
    and "c \<le> b"
    and "f integrable_on {a .. c}"
    and "f integrable_on {c .. b}"
  shows "f integrable_on {a .. b}"
  using assms
  unfolding integrable_on_def
  by (fastforce intro!:has_integral_combine)


subsection \<open>Reduce integrability to "local" integrability.\<close>

lemma integrable_on_little_subintervals:
  fixes f :: "'b::euclidean_space \<Rightarrow> 'a::banach"
  assumes "\<forall>x\<in>cbox a b. \<exists>d>0. \<forall>u v. x \<in> cbox u v \<and> cbox u v \<subseteq> ball x d \<and> cbox u v \<subseteq> cbox a b \<longrightarrow>
    f integrable_on cbox u v"
  shows "f integrable_on cbox a b"
proof -
  have "\<forall>x. \<exists>d. x\<in>cbox a b \<longrightarrow> d>0 \<and> (\<forall>u v. x \<in> cbox u v \<and> cbox u v \<subseteq> ball x d \<and> cbox u v \<subseteq> cbox a b \<longrightarrow>
    f integrable_on cbox u v)"
    using assms by auto
  note this[unfolded gauge_existence_lemma]
  from choice[OF this] guess d .. note d=this[rule_format]
  guess p
    apply (rule fine_division_exists[OF gauge_ball_dependent,of d a b])
    using d
    by auto
  note p=this(1-2)
  note division_of_tagged_division[OF this(1)]
  note * = comm_monoid_set.operative_division[OF comm_monoid_set_and operative_integrable, OF this, symmetric, of f]
  show ?thesis
    unfolding * comm_monoid_set_F_and
    apply safe
    unfolding snd_conv
  proof -
    fix x k
    assume "(x, k) \<in> p"
    note tagged_division_ofD(2-4)[OF p(1) this] fineD[OF p(2) this]
    then show "f integrable_on k"
      apply safe
      apply (rule d[THEN conjunct2,rule_format,of x])
      apply (auto intro: order.trans)
      done
  qed
qed


subsection \<open>Second FTC or existence of antiderivative.\<close>

lemma integrable_const[intro]: "(\<lambda>x. c) integrable_on cbox a b"
  unfolding integrable_on_def
  apply rule
  apply (rule has_integral_const)
  done

lemma integral_has_vector_derivative_continuous_at:
  fixes f :: "real \<Rightarrow> 'a::banach"
  assumes f: "f integrable_on {a..b}"
      and x: "x \<in> {a..b}"
      and fx: "continuous (at x within {a..b}) f"
  shows "((\<lambda>u. integral {a..u} f) has_vector_derivative f x) (at x within {a..b})"
proof -
  let ?I = "\<lambda>a b. integral {a..b} f"
  { fix e::real
    assume "e > 0"
    obtain d where "d>0" and d: "\<And>x'. \<lbrakk>x' \<in> {a..b}; \<bar>x' - x\<bar> < d\<rbrakk> \<Longrightarrow> norm(f x' - f x) \<le> e"
      using \<open>e>0\<close> fx by (auto simp: continuous_within_eps_delta dist_norm less_imp_le)
    have "norm (integral {a..y} f - integral {a..x} f - (y - x) *\<^sub>R f x) \<le> e * \<bar>y - x\<bar>"
           if y: "y \<in> {a..b}" and yx: "\<bar>y - x\<bar> < d" for y
    proof (cases "y < x")
      case False
      have "f integrable_on {a..y}"
        using f y by (simp add: integrable_subinterval_real)
      then have Idiff: "?I a y - ?I a x = ?I x y"
        using False x by (simp add: algebra_simps integral_combine)
      have fux_int: "((\<lambda>u. f u - f x) has_integral integral {x..y} f - (y - x) *\<^sub>R f x) {x..y}"
        apply (rule has_integral_sub)
        using x y apply (force intro: integrable_integral [OF integrable_subinterval_real [OF f]])
        using has_integral_const_real [of "f x" x y] False
        apply (simp add: )
        done
      show ?thesis
        using False
        apply (simp add: abs_eq_content del: content_real_if measure_lborel_Icc)
        apply (rule has_integral_bound_real[where f="(\<lambda>u. f u - f x)"])
        using yx False d x y \<open>e>0\<close> apply (auto simp add: Idiff fux_int)
        done
    next
      case True
      have "f integrable_on {a..x}"
        using f x by (simp add: integrable_subinterval_real)
      then have Idiff: "?I a x - ?I a y = ?I y x"
        using True x y by (simp add: algebra_simps integral_combine)
      have fux_int: "((\<lambda>u. f u - f x) has_integral integral {y..x} f - (x - y) *\<^sub>R f x) {y..x}"
        apply (rule has_integral_sub)
        using x y apply (force intro: integrable_integral [OF integrable_subinterval_real [OF f]])
        using has_integral_const_real [of "f x" y x] True
        apply (simp add: )
        done
      have "norm (integral {a..x} f - integral {a..y} f - (x - y) *\<^sub>R f x) \<le> e * \<bar>y - x\<bar>"
        using True
        apply (simp add: abs_eq_content del: content_real_if measure_lborel_Icc)
        apply (rule has_integral_bound_real[where f="(\<lambda>u. f u - f x)"])
        using yx True d x y \<open>e>0\<close> apply (auto simp add: Idiff fux_int)
        done
      then show ?thesis
        by (simp add: algebra_simps norm_minus_commute)
    qed
    then have "\<exists>d>0. \<forall>y\<in>{a..b}. \<bar>y - x\<bar> < d \<longrightarrow> norm (integral {a..y} f - integral {a..x} f - (y - x) *\<^sub>R f x) \<le> e * \<bar>y - x\<bar>"
      using \<open>d>0\<close> by blast
  }
  then show ?thesis
    by (simp add: has_vector_derivative_def has_derivative_within_alt bounded_linear_scaleR_left)
qed

lemma integral_has_vector_derivative:
  fixes f :: "real \<Rightarrow> 'a::banach"
  assumes "continuous_on {a .. b} f"
    and "x \<in> {a .. b}"
  shows "((\<lambda>u. integral {a .. u} f) has_vector_derivative f(x)) (at x within {a .. b})"
apply (rule integral_has_vector_derivative_continuous_at [OF integrable_continuous_real])
using assms
apply (auto simp: continuous_on_eq_continuous_within)
done

lemma antiderivative_continuous:
  fixes q b :: real
  assumes "continuous_on {a .. b} f"
  obtains g where "\<forall>x\<in>{a .. b}. (g has_vector_derivative (f x::_::banach)) (at x within {a .. b})"
  apply (rule that)
  apply rule
  using integral_has_vector_derivative[OF assms]
  apply auto
  done


subsection \<open>Combined fundamental theorem of calculus.\<close>

lemma antiderivative_integral_continuous:
  fixes f :: "real \<Rightarrow> 'a::banach"
  assumes "continuous_on {a .. b} f"
  obtains g where "\<forall>u\<in>{a .. b}. \<forall>v \<in> {a .. b}. u \<le> v \<longrightarrow> (f has_integral (g v - g u)) {u .. v}"
proof -
  from antiderivative_continuous[OF assms] guess g . note g=this
  show ?thesis
    apply (rule that[of g])
    apply safe
  proof goal_cases
    case prems: (1 u v)
    have "\<forall>x\<in>cbox u v. (g has_vector_derivative f x) (at x within cbox u v)"
      apply rule
      apply (rule has_vector_derivative_within_subset)
      apply (rule g[rule_format])
      using prems(1,2)
      apply auto
      done
    then show ?case
      using fundamental_theorem_of_calculus[OF prems(3), of g f] by auto
  qed
qed


subsection \<open>General "twiddling" for interval-to-interval function image.\<close>

lemma has_integral_twiddle:
  assumes "0 < r"
    and "\<forall>x. h(g x) = x"
    and "\<forall>x. g(h x) = x"
    and contg: "\<And>x. continuous (at x) g"
    and "\<forall>u v. \<exists>w z. g ` cbox u v = cbox w z"
    and "\<forall>u v. \<exists>w z. h ` cbox u v = cbox w z"
    and "\<forall>u v. content(g ` cbox u v) = r * content (cbox u v)"
    and "(f has_integral i) (cbox a b)"
  shows "((\<lambda>x. f(g x)) has_integral (1 / r) *\<^sub>R i) (h ` cbox a b)"
proof -
  show ?thesis when *: "cbox a b \<noteq> {} \<Longrightarrow> ?thesis"
    apply cases
    defer
    apply (rule *)
    apply assumption
  proof goal_cases
    case prems: 1
    then show ?thesis
      unfolding prems assms(8)[unfolded prems has_integral_empty_eq] by auto
  qed
  assume "cbox a b \<noteq> {}"
  from assms(6)[rule_format,of a b] guess w z by (elim exE) note wz=this
  have inj: "inj g" "inj h"
    unfolding inj_on_def
    apply safe
    apply(rule_tac[!] ccontr)
    using assms(2)
    apply(erule_tac x=x in allE)
    using assms(2)
    apply(erule_tac x=y in allE)
    defer
    using assms(3)
    apply (erule_tac x=x in allE)
    using assms(3)
    apply(erule_tac x=y in allE)
    apply auto
    done
  show ?thesis
    unfolding has_integral_def has_integral_compact_interval_def
    apply (subst if_P)
    apply rule
    apply rule
    apply (rule wz)
  proof safe
    fix e :: real
    assume e: "e > 0"
    with assms(1) have "e * r > 0" by simp
    from assms(8)[unfolded has_integral,rule_format,OF this] guess d by (elim exE conjE) note d=this[rule_format]
    define d' where "d' x = {y. g y \<in> d (g x)}" for x
    have d': "\<And>x. d' x = {y. g y \<in> (d (g x))}"
      unfolding d'_def ..
    show "\<exists>d. gauge d \<and> (\<forall>p. p tagged_division_of h ` cbox a b \<and> d fine p \<longrightarrow> norm ((\<Sum>(x, k)\<in>p. content k *\<^sub>R f (g x)) - (1 / r) *\<^sub>R i) < e)"
    proof (rule_tac x=d' in exI, safe)
      show "gauge d'"
        using d(1)
        unfolding gauge_def d'
        using continuous_open_preimage_univ[OF _ contg]
        by auto
      fix p
      assume as: "p tagged_division_of h ` cbox a b" "d' fine p"
      note p = tagged_division_ofD[OF as(1)]
      have "(\<lambda>(x, k). (g x, g ` k)) ` p tagged_division_of (cbox a b) \<and> d fine (\<lambda>(x, k). (g x, g ` k)) ` p"
        unfolding tagged_division_of
      proof safe
        show "finite ((\<lambda>(x, k). (g x, g ` k)) ` p)"
          using as by auto
        show "d fine (\<lambda>(x, k). (g x, g ` k)) ` p"
          using as(2) unfolding fine_def d' by auto
        fix x k
        assume xk[intro]: "(x, k) \<in> p"
        show "g x \<in> g ` k"
          using p(2)[OF xk] by auto
        show "\<exists>u v. g ` k = cbox u v"
          using p(4)[OF xk] using assms(5-6) by auto
        {
          fix y
          assume "y \<in> k"
          then show "g y \<in> cbox a b" "g y \<in> cbox a b"
            using p(3)[OF xk,unfolded subset_eq,rule_format,of "h (g y)"]
            using assms(2)[rule_format,of y]
            unfolding inj_image_mem_iff[OF inj(2)]
            by auto
        }
        fix x' k'
        assume xk': "(x', k') \<in> p"
        fix z
        assume z: "z \<in> interior (g ` k)" "z \<in> interior (g ` k')"
        have same: "(x, k) = (x', k')"
          apply -
          apply (rule ccontr)
          apply (drule p(5)[OF xk xk'])
        proof -
          assume as: "interior k \<inter> interior k' = {}"
          have "z \<in> g ` (interior k \<inter> interior k')"
            using interior_image_subset[OF \<open>inj g\<close> contg] z
            unfolding image_Int[OF inj(1)] by blast
          then show False
            using as by blast
        qed
        then show "g x = g x'"
          by auto
        {
          fix z
          assume "z \<in> k"
          then show "g z \<in> g ` k'"
            using same by auto
        }
        {
          fix z
          assume "z \<in> k'"
          then show "g z \<in> g ` k"
            using same by auto
        }
      next
        fix x
        assume "x \<in> cbox a b"
        then have "h x \<in>  \<Union>{k. \<exists>x. (x, k) \<in> p}"
          using p(6) by auto
        then guess X unfolding Union_iff .. note X=this
        from this(1) guess y unfolding mem_Collect_eq ..
        then show "x \<in> \<Union>{k. \<exists>x. (x, k) \<in> (\<lambda>(x, k). (g x, g ` k)) ` p}"
          apply -
          apply (rule_tac X="g ` X" in UnionI)
          defer
          apply (rule_tac x="h x" in image_eqI)
          using X(2) assms(3)[rule_format,of x]
          apply auto
          done
      qed
        note ** = d(2)[OF this]
        have *: "inj_on (\<lambda>(x, k). (g x, g ` k)) p"
          using inj(1) unfolding inj_on_def by fastforce
        have "(\<Sum>(x, k)\<in>(\<lambda>(x, k). (g x, g ` k)) ` p. content k *\<^sub>R f x) - i = r *\<^sub>R (\<Sum>(x, k)\<in>p. content k *\<^sub>R f (g x)) - i" (is "?l = _")
          using assms(7)
          apply (simp only: algebra_simps add_left_cancel scaleR_right.setsum)
          apply (subst setsum.reindex_bij_betw[symmetric, where h="\<lambda>(x, k). (g x, g ` k)" and S=p])
          apply (auto intro!: * setsum.cong simp: bij_betw_def dest!: p(4))
          done
      also have "\<dots> = r *\<^sub>R ((\<Sum>(x, k)\<in>p. content k *\<^sub>R f (g x)) - (1 / r) *\<^sub>R i)" (is "_ = ?r")
        unfolding scaleR_diff_right scaleR_scaleR
        using assms(1)
        by auto
      finally have *: "?l = ?r" .
      show "norm ((\<Sum>(x, k)\<in>p. content k *\<^sub>R f (g x)) - (1 / r) *\<^sub>R i) < e"
        using **
        unfolding *
        unfolding norm_scaleR
        using assms(1)
        by (auto simp add:field_simps)
    qed
  qed
qed


subsection \<open>Special case of a basic affine transformation.\<close>

lemma AE_lborel_inner_neq:
  assumes k: "k \<in> Basis"
  shows "AE x in lborel. x \<bullet> k \<noteq> c"
proof -
  interpret finite_product_sigma_finite "\<lambda>_. lborel" Basis
    proof qed simp

  have "emeasure lborel {x\<in>space lborel. x \<bullet> k = c} = emeasure (\<Pi>\<^sub>M j::'a\<in>Basis. lborel) (\<Pi>\<^sub>E j\<in>Basis. if j = k then {c} else UNIV)"
    using k
    by (auto simp add: lborel_eq[where 'a='a] emeasure_distr intro!: arg_cong2[where f=emeasure])
       (auto simp: space_PiM PiE_iff extensional_def split: if_split_asm)
  also have "\<dots> = (\<Prod>j\<in>Basis. emeasure lborel (if j = k then {c} else UNIV))"
    by (intro measure_times) auto
  also have "\<dots> = 0"
    by (intro setprod_zero bexI[OF _ k]) auto
  finally show ?thesis
    by (subst AE_iff_measurable[OF _ refl]) auto
qed

lemma content_image_stretch_interval:
  fixes m :: "'a::euclidean_space \<Rightarrow> real"
  defines "s f x \<equiv> (\<Sum>k::'a\<in>Basis. (f k * (x\<bullet>k)) *\<^sub>R k)"
  shows "content (s m ` cbox a b) = \<bar>\<Prod>k\<in>Basis. m k\<bar> * content (cbox a b)"
proof cases
  have s[measurable]: "s f \<in> borel \<rightarrow>\<^sub>M borel" for f
    by (auto simp: s_def[abs_def])
  assume m: "\<forall>k\<in>Basis. m k \<noteq> 0"
  then have s_comp_s: "s (\<lambda>k. 1 / m k) \<circ> s m = id" "s m \<circ> s (\<lambda>k. 1 / m k) = id"
    by (auto simp: s_def[abs_def] fun_eq_iff euclidean_representation)
  then have "inv (s (\<lambda>k. 1 / m k)) = s m" "bij (s (\<lambda>k. 1 / m k))"
    by (auto intro: inv_unique_comp o_bij)
  then have eq: "s m ` cbox a b = s (\<lambda>k. 1 / m k) -` cbox a b"
    using bij_vimage_eq_inv_image[OF \<open>bij (s (\<lambda>k. 1 / m k))\<close>, of "cbox a b"] by auto
  show ?thesis
    using m unfolding eq measure_def
    by (subst lborel_affine_euclidean[where c=m and t=0])
       (simp_all add: emeasure_density measurable_sets_borel[OF s] abs_setprod nn_integral_cmult
                      s_def[symmetric] emeasure_distr vimage_comp s_comp_s enn2real_mult setprod_nonneg)
next
  assume "\<not> (\<forall>k\<in>Basis. m k \<noteq> 0)"
  then obtain k where k: "k \<in> Basis" "m k = 0" by auto
  then have [simp]: "(\<Prod>k\<in>Basis. m k) = 0"
    by (intro setprod_zero) auto
  have "emeasure lborel {x\<in>space lborel. x \<in> s m ` cbox a b} = 0"
  proof (rule emeasure_eq_0_AE)
    show "AE x in lborel. x \<notin> s m ` cbox a b"
      using AE_lborel_inner_neq[OF \<open>k\<in>Basis\<close>]
    proof eventually_elim
      show "x \<bullet> k \<noteq> 0 \<Longrightarrow> x \<notin> s m ` cbox a b " for x
        using k by (auto simp: s_def[abs_def] cbox_def)
    qed
  qed
  then show ?thesis
    by (simp add: measure_def)
qed

lemma interval_image_affinity_interval:
  "\<exists>u v. (\<lambda>x. m *\<^sub>R (x::'a::euclidean_space) + c) ` cbox a b = cbox u v"
  unfolding image_affinity_cbox
  by auto

lemma content_image_affinity_cbox:
  "content((\<lambda>x::'a::euclidean_space. m *\<^sub>R x + c) ` cbox a b) =
    \<bar>m\<bar> ^ DIM('a) * content (cbox a b)" (is "?l = ?r")
proof (cases "cbox a b = {}")
  case True then show ?thesis by simp
next
  case False
  show ?thesis
  proof (cases "m \<ge> 0")
    case True
    with \<open>cbox a b \<noteq> {}\<close> have "cbox (m *\<^sub>R a + c) (m *\<^sub>R b + c) \<noteq> {}"
      unfolding box_ne_empty
      apply (intro ballI)
      apply (erule_tac x=i in ballE)
      apply (auto simp: inner_simps mult_left_mono)
      done
    moreover from True have *: "\<And>i. (m *\<^sub>R b + c) \<bullet> i - (m *\<^sub>R a + c) \<bullet> i = m *\<^sub>R (b - a) \<bullet> i"
      by (simp add: inner_simps field_simps)
    ultimately show ?thesis
      by (simp add: image_affinity_cbox True content_cbox'
        setprod.distrib setprod_constant inner_diff_left)
  next
    case False
    with \<open>cbox a b \<noteq> {}\<close> have "cbox (m *\<^sub>R b + c) (m *\<^sub>R a + c) \<noteq> {}"
      unfolding box_ne_empty
      apply (intro ballI)
      apply (erule_tac x=i in ballE)
      apply (auto simp: inner_simps mult_left_mono)
      done
    moreover from False have *: "\<And>i. (m *\<^sub>R a + c) \<bullet> i - (m *\<^sub>R b + c) \<bullet> i = (-m) *\<^sub>R (b - a) \<bullet> i"
      by (simp add: inner_simps field_simps)
    ultimately show ?thesis using False
      by (simp add: image_affinity_cbox content_cbox'
        setprod.distrib[symmetric] setprod_constant[symmetric] inner_diff_left)
  qed
qed

lemma has_integral_affinity:
  fixes a :: "'a::euclidean_space"
  assumes "(f has_integral i) (cbox a b)"
      and "m \<noteq> 0"
  shows "((\<lambda>x. f(m *\<^sub>R x + c)) has_integral ((1 / (\<bar>m\<bar> ^ DIM('a))) *\<^sub>R i)) ((\<lambda>x. (1 / m) *\<^sub>R x + -((1 / m) *\<^sub>R c)) ` cbox a b)"
  apply (rule has_integral_twiddle)
  using assms
  apply (safe intro!: interval_image_affinity_interval content_image_affinity_cbox)
  apply (rule zero_less_power)
  unfolding scaleR_right_distrib
  apply auto
  done

lemma integrable_affinity:
  assumes "f integrable_on cbox a b"
    and "m \<noteq> 0"
  shows "(\<lambda>x. f(m *\<^sub>R x + c)) integrable_on ((\<lambda>x. (1 / m) *\<^sub>R x + -((1/m) *\<^sub>R c)) ` cbox a b)"
  using assms
  unfolding integrable_on_def
  apply safe
  apply (drule has_integral_affinity)
  apply auto
  done

lemmas has_integral_affinity01 = has_integral_affinity [of _ _ 0 "1::real", simplified]

subsection \<open>Special case of stretching coordinate axes separately.\<close>

lemma has_integral_stretch:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::real_normed_vector"
  assumes "(f has_integral i) (cbox a b)"
    and "\<forall>k\<in>Basis. m k \<noteq> 0"
  shows "((\<lambda>x. f (\<Sum>k\<in>Basis. (m k * (x\<bullet>k))*\<^sub>R k)) has_integral
         ((1/ \<bar>setprod m Basis\<bar>) *\<^sub>R i)) ((\<lambda>x. (\<Sum>k\<in>Basis. (1 / m k * (x\<bullet>k))*\<^sub>R k)) ` cbox a b)"
apply (rule has_integral_twiddle[where f=f])
unfolding zero_less_abs_iff content_image_stretch_interval
unfolding image_stretch_interval empty_as_interval euclidean_eq_iff[where 'a='a]
using assms
by auto
 

lemma integrable_stretch:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::real_normed_vector"
  assumes "f integrable_on cbox a b"
    and "\<forall>k\<in>Basis. m k \<noteq> 0"
  shows "(\<lambda>x::'a. f (\<Sum>k\<in>Basis. (m k * (x\<bullet>k))*\<^sub>R k)) integrable_on
    ((\<lambda>x. \<Sum>k\<in>Basis. (1 / m k * (x\<bullet>k))*\<^sub>R k) ` cbox a b)"
  using assms unfolding integrable_on_def
  by (force dest: has_integral_stretch)


subsection \<open>even more special cases.\<close>

lemma uminus_interval_vector[simp]:
  fixes a b :: "'a::euclidean_space"
  shows "uminus ` cbox a b = cbox (-b) (-a)"
  apply (rule set_eqI)
  apply rule
  defer
  unfolding image_iff
  apply (rule_tac x="-x" in bexI)
  apply (auto simp add:minus_le_iff le_minus_iff mem_box)
  done

lemma has_integral_reflect_lemma[intro]:
  assumes "(f has_integral i) (cbox a b)"
  shows "((\<lambda>x. f(-x)) has_integral i) (cbox (-b) (-a))"
  using has_integral_affinity[OF assms, of "-1" 0]
  by auto

lemma has_integral_reflect_lemma_real[intro]:
  assumes "(f has_integral i) {a .. b::real}"
  shows "((\<lambda>x. f(-x)) has_integral i) {-b .. -a}"
  using assms
  unfolding box_real[symmetric]
  by (rule has_integral_reflect_lemma)

lemma has_integral_reflect[simp]:
  "((\<lambda>x. f (-x)) has_integral i) (cbox (-b) (-a)) \<longleftrightarrow> (f has_integral i) (cbox a b)"
  apply rule
  apply (drule_tac[!] has_integral_reflect_lemma)
  apply auto
  done

lemma integrable_reflect[simp]: "(\<lambda>x. f(-x)) integrable_on cbox (-b) (-a) \<longleftrightarrow> f integrable_on cbox a b"
  unfolding integrable_on_def by auto

lemma integrable_reflect_real[simp]: "(\<lambda>x. f(-x)) integrable_on {-b .. -a} \<longleftrightarrow> f integrable_on {a .. b::real}"
  unfolding box_real[symmetric]
  by (rule integrable_reflect)

lemma integral_reflect[simp]: "integral (cbox (-b) (-a)) (\<lambda>x. f (-x)) = integral (cbox a b) f"
  unfolding integral_def by auto

lemma integral_reflect_real[simp]: "integral {-b .. -a} (\<lambda>x. f (-x)) = integral {a .. b::real} f"
  unfolding box_real[symmetric]
  by (rule integral_reflect)


subsection \<open>Stronger form of FCT; quite a tedious proof.\<close>

lemma bgauge_existence_lemma: "(\<forall>x\<in>s. \<exists>d::real. 0 < d \<and> q d x) \<longleftrightarrow> (\<forall>x. \<exists>d>0. x\<in>s \<longrightarrow> q d x)"
  by (meson zero_less_one)

lemma additive_tagged_division_1':
  fixes f :: "real \<Rightarrow> 'a::real_normed_vector"
  assumes "a \<le> b"
    and "p tagged_division_of {a..b}"
  shows "setsum (\<lambda>(x,k). f (Sup k) - f(Inf k)) p = f b - f a"
  using additive_tagged_division_1[OF _ assms(2), of f]
  using assms(1)
  by auto

lemma split_minus[simp]: "(\<lambda>(x, k). f x k) x - (\<lambda>(x, k). g x k) x = (\<lambda>(x, k). f x k - g x k) x"
  by (simp add: split_def)

lemma norm_triangle_le_sub: "norm x + norm y \<le> e \<Longrightarrow> norm (x - y) \<le> e"
  apply (subst(asm)(2) norm_minus_cancel[symmetric])
  apply (drule norm_triangle_le)
  apply (auto simp add: algebra_simps)
  done

lemma fundamental_theorem_of_calculus_interior:
  fixes f :: "real \<Rightarrow> 'a::real_normed_vector"
  assumes "a \<le> b"
    and "continuous_on {a .. b} f"
    and "\<forall>x\<in>{a <..< b}. (f has_vector_derivative f'(x)) (at x)"
  shows "(f' has_integral (f b - f a)) {a .. b}"
proof -
  {
    presume *: "a < b \<Longrightarrow> ?thesis"
    show ?thesis
    proof (cases "a < b")
      case True
      then show ?thesis by (rule *)
    next
      case False
      then have "a = b"
        using assms(1) by auto
      then have *: "cbox a b = {b}" "f b - f a = 0"
        by (auto simp add:  order_antisym)
      show ?thesis
        unfolding *(2)
        unfolding content_eq_0
        using * \<open>a = b\<close>
        by (auto simp: ex_in_conv)
    qed
  }
  assume ab: "a < b"
  let ?P = "\<lambda>e. \<exists>d. gauge d \<and> (\<forall>p. p tagged_division_of {a .. b} \<and> d fine p \<longrightarrow>
    norm ((\<Sum>(x, k)\<in>p. content k *\<^sub>R f' x) - (f b - f a)) \<le> e * content {a .. b})"
  { presume "\<And>e. e > 0 \<Longrightarrow> ?P e" then show ?thesis unfolding has_integral_factor_content_real by auto }
  fix e :: real
  assume e: "e > 0"
  note assms(3)[unfolded has_vector_derivative_def has_derivative_at_alt ball_conj_distrib]
  note conjunctD2[OF this]
  note bounded=this(1) and this(2)
  from this(2) have "\<forall>x\<in>box a b. \<exists>d>0. \<forall>y. norm (y - x) < d \<longrightarrow>
    norm (f y - f x - (y - x) *\<^sub>R f' x) \<le> e/2 * norm (y - x)"
    apply -
    apply safe
    apply (erule_tac x=x in ballE)
    apply (erule_tac x="e/2" in allE)
    using e
    apply auto
    done
  note this[unfolded bgauge_existence_lemma]
  from choice[OF this] guess d ..
  note conjunctD2[OF this[rule_format]]
  note d = this[rule_format]
  have "bounded (f ` cbox a b)"
    apply (rule compact_imp_bounded compact_continuous_image)+
    using compact_cbox assms
    apply auto
    done
  from this[unfolded bounded_pos] guess B .. note B = this[rule_format]

  have "\<exists>da. 0 < da \<and> (\<forall>c. a \<le> c \<and> {a .. c} \<subseteq> {a .. b} \<and> {a .. c} \<subseteq> ball a da \<longrightarrow>
    norm (content {a .. c} *\<^sub>R f' a - (f c - f a)) \<le> (e * (b - a)) / 4)"
  proof -
    have "a \<in> {a .. b}"
      using ab by auto
    note assms(2)[unfolded continuous_on_eq_continuous_within,rule_format,OF this]
    note * = this[unfolded continuous_within Lim_within,rule_format]
    have "(e * (b - a)) / 8 > 0"
      using e ab by (auto simp add: field_simps)
    from *[OF this] guess k .. note k = conjunctD2[OF this,rule_format]
    have "\<exists>l. 0 < l \<and> norm(l *\<^sub>R f' a) \<le> (e * (b - a)) / 8"
    proof (cases "f' a = 0")
      case True
      thus ?thesis using ab e by auto
    next
      case False
      then show ?thesis
        apply (rule_tac x="(e * (b - a)) / 8 / norm (f' a)" in exI)
        using ab e
        apply (auto simp add: field_simps)
        done
    qed
    then guess l .. note l = conjunctD2[OF this]
    show ?thesis
      apply (rule_tac x="min k l" in exI)
      apply safe
      unfolding min_less_iff_conj
      apply rule
      apply (rule l k)+
    proof -
      fix c
      assume as: "a \<le> c" "{a .. c} \<subseteq> {a .. b}" "{a .. c} \<subseteq> ball a (min k l)"
      note as' = this[unfolded subset_eq Ball_def mem_ball dist_real_def mem_box]
      have "norm ((c - a) *\<^sub>R f' a - (f c - f a)) \<le> norm ((c - a) *\<^sub>R f' a) + norm (f c - f a)"
        by (rule norm_triangle_ineq4)
      also have "\<dots> \<le> e * (b - a) / 8 + e * (b - a) / 8"
      proof (rule add_mono)
        have "\<bar>c - a\<bar> \<le> \<bar>l\<bar>"
          using as' by auto
        then show "norm ((c - a) *\<^sub>R f' a) \<le> e * (b - a) / 8"
          apply -
          apply (rule order_trans[OF _ l(2)])
          unfolding norm_scaleR
          apply (rule mult_right_mono)
          apply auto
          done
      next
        show "norm (f c - f a) \<le> e * (b - a) / 8"
          apply (rule less_imp_le)
          apply (cases "a = c")
          defer
          apply (rule k(2)[unfolded dist_norm])
          using as' e ab
          apply (auto simp add: field_simps)
          done
      qed
      finally show "norm (content {a .. c} *\<^sub>R f' a - (f c - f a)) \<le> e * (b - a) / 4"
        unfolding content_real[OF as(1)] by auto
    qed
  qed
  then guess da .. note da=conjunctD2[OF this,rule_format]

  have "\<exists>db>0. \<forall>c\<le>b. {c .. b} \<subseteq> {a .. b} \<and> {c .. b} \<subseteq> ball b db \<longrightarrow>
    norm (content {c .. b} *\<^sub>R f' b - (f b - f c)) \<le> (e * (b - a)) / 4"
  proof -
    have "b \<in> {a .. b}"
      using ab by auto
    note assms(2)[unfolded continuous_on_eq_continuous_within,rule_format,OF this]
    note * = this[unfolded continuous_within Lim_within,rule_format] have "(e * (b - a)) / 8 > 0"
      using e ab by (auto simp add: field_simps)
    from *[OF this] guess k .. note k = conjunctD2[OF this,rule_format]
    have "\<exists>l. 0 < l \<and> norm (l *\<^sub>R f' b) \<le> (e * (b - a)) / 8"
    proof (cases "f' b = 0")
      case True
      thus ?thesis using ab e by auto
    next
      case False
      then show ?thesis
        apply (rule_tac x="(e * (b - a)) / 8 / norm (f' b)" in exI)
        using ab e
        apply (auto simp add: field_simps)
        done
    qed
    then guess l .. note l = conjunctD2[OF this]
    show ?thesis
      apply (rule_tac x="min k l" in exI)
      apply safe
      unfolding min_less_iff_conj
      apply rule
      apply (rule l k)+
    proof -
      fix c
      assume as: "c \<le> b" "{c..b} \<subseteq> {a..b}" "{c..b} \<subseteq> ball b (min k l)"
      note as' = this[unfolded subset_eq Ball_def mem_ball dist_real_def mem_box]
      have "norm ((b - c) *\<^sub>R f' b - (f b - f c)) \<le> norm ((b - c) *\<^sub>R f' b) + norm (f b - f c)"
        by (rule norm_triangle_ineq4)
      also have "\<dots> \<le> e * (b - a) / 8 + e * (b - a) / 8"
      proof (rule add_mono)
        have "\<bar>c - b\<bar> \<le> \<bar>l\<bar>"
          using as' by auto
        then show "norm ((b - c) *\<^sub>R f' b) \<le> e * (b - a) / 8"
          apply -
          apply (rule order_trans[OF _ l(2)])
          unfolding norm_scaleR
          apply (rule mult_right_mono)
          apply auto
          done
      next
        show "norm (f b - f c) \<le> e * (b - a) / 8"
          apply (rule less_imp_le)
          apply (cases "b = c")
          defer
          apply (subst norm_minus_commute)
          apply (rule k(2)[unfolded dist_norm])
          using as' e ab
          apply (auto simp add: field_simps)
          done
      qed
      finally show "norm (content {c .. b} *\<^sub>R f' b - (f b - f c)) \<le> e * (b - a) / 4"
        unfolding content_real[OF as(1)] by auto
    qed
  qed
  then guess db .. note db=conjunctD2[OF this,rule_format]

  let ?d = "(\<lambda>x. ball x (if x=a then da else if x=b then db else d x))"
  show "?P e"
    apply (rule_tac x="?d" in exI)
  proof (safe, goal_cases)
    case 1
    show ?case
      apply (rule gauge_ball_dependent)
      using ab db(1) da(1) d(1)
      apply auto
      done
  next
    case as: (2 p)
    let ?A = "{t. fst t \<in> {a, b}}"
    note p = tagged_division_ofD[OF as(1)]
    have pA: "p = (p \<inter> ?A) \<union> (p - ?A)" "finite (p \<inter> ?A)" "finite (p - ?A)" "(p \<inter> ?A) \<inter> (p - ?A) = {}"
      using as by auto
    note * = additive_tagged_division_1'[OF assms(1) as(1), symmetric]
    have **: "\<And>n1 s1 n2 s2::real. n2 \<le> s2 / 2 \<Longrightarrow> n1 - s1 \<le> s2 / 2 \<Longrightarrow> n1 + n2 \<le> s1 + s2"
      by arith
    show ?case
      unfolding content_real[OF assms(1)] and *[of "\<lambda>x. x"] *[of f] setsum_subtractf[symmetric] split_minus
      unfolding setsum_distrib_left
      apply (subst(2) pA)
      apply (subst pA)
      unfolding setsum.union_disjoint[OF pA(2-)]
    proof (rule norm_triangle_le, rule **, goal_cases)
      case 1
      show ?case
        apply (rule order_trans)
        apply (rule setsum_norm_le)
        defer
        apply (subst setsum_divide_distrib)
        apply (rule order_refl)
        apply safe
        apply (unfold not_le o_def split_conv fst_conv)
      proof (rule ccontr)
        fix x k
        assume xk: "(x, k) \<in> p"
          "e * (Sup k -  Inf k) / 2 <
            norm (content k *\<^sub>R f' x - (f (Sup k) - f (Inf k)))"
        from p(4)[OF this(1)] guess u v by (elim exE) note k=this
        then have "u \<le> v" and uv: "{u, v} \<subseteq> cbox u v"
          using p(2)[OF xk(1)] by auto
        note result = xk(2)[unfolded k box_real interval_bounds_real[OF this(1)] content_real[OF this(1)]]

        assume as': "x \<noteq> a" "x \<noteq> b"
        then have "x \<in> box a b"
          using p(2-3)[OF xk(1)] by (auto simp: mem_box)
        note  * = d(2)[OF this]
        have "norm ((v - u) *\<^sub>R f' (x) - (f (v) - f (u))) =
          norm ((f (u) - f (x) - (u - x) *\<^sub>R f' (x)) - (f (v) - f (x) - (v - x) *\<^sub>R f' (x)))"
          apply (rule arg_cong[of _ _ norm])
          unfolding scaleR_left.diff
          apply auto
          done
        also have "\<dots> \<le> e / 2 * norm (u - x) + e / 2 * norm (v - x)"
          apply (rule norm_triangle_le_sub)
          apply (rule add_mono)
          apply (rule_tac[!] *)
          using fineD[OF as(2) xk(1)] as'
          unfolding k subset_eq
          apply -
          apply (erule_tac x=u in ballE)
          apply (erule_tac[3] x=v in ballE)
          using uv
          apply (auto simp:dist_real_def)
          done
        also have "\<dots> \<le> e / 2 * norm (v - u)"
          using p(2)[OF xk(1)]
          unfolding k
          by (auto simp add: field_simps)
        finally have "e * (v - u) / 2 < e * (v - u) / 2"
          apply -
          apply (rule less_le_trans[OF result])
          using uv
          apply auto
          done
        then show False by auto
      qed
    next
      have *: "\<And>x s1 s2::real. 0 \<le> s1 \<Longrightarrow> x \<le> (s1 + s2) / 2 \<Longrightarrow> x - s1 \<le> s2 / 2"
        by auto
      case 2
      show ?case
        apply (rule *)
        apply (rule setsum_nonneg)
        apply rule
        apply (unfold split_paired_all split_conv)
        defer
        unfolding setsum.union_disjoint[OF pA(2-),symmetric] pA(1)[symmetric]
        unfolding setsum_distrib_left[symmetric]
        apply (subst additive_tagged_division_1[OF _ as(1)])
        apply (rule assms)
      proof -
        fix x k
        assume "(x, k) \<in> p \<inter> {t. fst t \<in> {a, b}}"
        note xk=IntD1[OF this]
        from p(4)[OF this] guess u v by (elim exE) note uv=this
        with p(2)[OF xk] have "cbox u v \<noteq> {}"
          by auto
        then show "0 \<le> e * ((Sup k) - (Inf k))"
          unfolding uv using e by (auto simp add: field_simps)
      next
        have *: "\<And>s f t e. setsum f s = setsum f t \<Longrightarrow> norm (setsum f t) \<le> e \<Longrightarrow> norm (setsum f s) \<le> e"
          by auto
        show "norm (\<Sum>(x, k)\<in>p \<inter> ?A. content k *\<^sub>R f' x -
          (f ((Sup k)) - f ((Inf k)))) \<le> e * (b - a) / 2"
          apply (rule *[where t1="p \<inter> {t. fst t \<in> {a, b} \<and> content(snd t) \<noteq> 0}"])
          apply (rule setsum.mono_neutral_right[OF pA(2)])
          defer
          apply rule
          unfolding split_paired_all split_conv o_def
        proof goal_cases
          fix x k
          assume "(x, k) \<in> p \<inter> {t. fst t \<in> {a, b}} - p \<inter> {t. fst t \<in> {a, b} \<and> content (snd t) \<noteq> 0}"
          then have xk: "(x, k) \<in> p" "content k = 0"
            by auto
          from p(4)[OF xk(1)] guess u v by (elim exE) note uv=this
          have "k \<noteq> {}"
            using p(2)[OF xk(1)] by auto
          then have *: "u = v"
            using xk
            unfolding uv content_eq_0 box_eq_empty
            by auto
          then show "content k *\<^sub>R (f' (x)) - (f ((Sup k)) - f ((Inf k))) = 0"
            using xk unfolding uv by auto
        next
          have *: "p \<inter> {t. fst t \<in> {a, b} \<and> content(snd t) \<noteq> 0} =
            {t. t\<in>p \<and> fst t = a \<and> content(snd t) \<noteq> 0} \<union> {t. t\<in>p \<and> fst t = b \<and> content(snd t) \<noteq> 0}"
            by blast
          have **: "norm (setsum f s) \<le> e"
            if "\<forall>x y. x \<in> s \<and> y \<in> s \<longrightarrow> x = y"
            and "\<forall>x. x \<in> s \<longrightarrow> norm (f x) \<le> e"
            and "e > 0"
            for s f and e :: real
          proof (cases "s = {}")
            case True
            with that show ?thesis by auto
          next
            case False
            then obtain x where "x \<in> s"
              by auto
            then have *: "s = {x}"
              using that(1) by auto
            then show ?thesis
              using \<open>x \<in> s\<close> that(2) by auto
          qed
          case 2
          show ?case
            apply (subst *)
            apply (subst setsum.union_disjoint)
            prefer 4
            apply (rule order_trans[of _ "e * (b - a)/4 + e * (b - a)/4"])
            apply (rule norm_triangle_le,rule add_mono)
            apply (rule_tac[1-2] **)
          proof -
            let ?B = "\<lambda>x. {t \<in> p. fst t = x \<and> content (snd t) \<noteq> 0}"
            have pa: "\<exists>v. k = cbox a v \<and> a \<le> v" if "(a, k) \<in> p" for k
            proof -
              guess u v using p(4)[OF that] by (elim exE) note uv=this
              have *: "u \<le> v"
                using p(2)[OF that] unfolding uv by auto
              have u: "u = a"
              proof (rule ccontr)
                have "u \<in> cbox u v"
                  using p(2-3)[OF that(1)] unfolding uv by auto
                have "u \<ge> a"
                  using p(2-3)[OF that(1)] unfolding uv subset_eq by auto
                moreover assume "\<not> ?thesis"
                ultimately have "u > a" by auto
                then show False
                  using p(2)[OF that(1)] unfolding uv by (auto simp add:)
              qed
              then show ?thesis
                apply (rule_tac x=v in exI)
                unfolding uv
                using *
                apply auto
                done
            qed
            have pb: "\<exists>v. k = cbox v b \<and> b \<ge> v" if "(b, k) \<in> p" for k
            proof -
              guess u v using p(4)[OF that] by (elim exE) note uv=this
              have *: "u \<le> v"
                using p(2)[OF that] unfolding uv by auto
              have u: "v = b"
              proof (rule ccontr)
                have "u \<in> cbox u v"
                  using p(2-3)[OF that(1)] unfolding uv by auto
                have "v \<le> b"
                  using p(2-3)[OF that(1)] unfolding uv subset_eq by auto
                moreover assume "\<not> ?thesis"
                ultimately have "v < b" by auto
                then show False
                  using p(2)[OF that(1)] unfolding uv by (auto simp add:)
              qed
              then show ?thesis
                apply (rule_tac x=u in exI)
                unfolding uv
                using *
                apply auto
                done
            qed
            show "\<forall>x y. x \<in> ?B a \<and> y \<in> ?B a \<longrightarrow> x = y"
              apply (rule,rule,rule,unfold split_paired_all)
              unfolding mem_Collect_eq fst_conv snd_conv
              apply safe
            proof -
              fix x k k'
              assume k: "(a, k) \<in> p" "(a, k') \<in> p" "content k \<noteq> 0" "content k' \<noteq> 0"
              guess v using pa[OF k(1)] .. note v = conjunctD2[OF this]
              guess v' using pa[OF k(2)] .. note v' = conjunctD2[OF this] let ?v = "min v v'"
              have "box a ?v \<subseteq> k \<inter> k'"
                unfolding v v' by (auto simp add: mem_box)
              note interior_mono[OF this,unfolded interior_Int]
              moreover have "(a + ?v)/2 \<in> box a ?v"
                using k(3-)
                unfolding v v' content_eq_0 not_le
                by (auto simp add: mem_box)
              ultimately have "(a + ?v)/2 \<in> interior k \<inter> interior k'"
                unfolding interior_open[OF open_box] by auto
              then have *: "k = k'"
                apply -
                apply (rule ccontr)
                using p(5)[OF k(1-2)]
                apply auto
                done
              { assume "x \<in> k" then show "x \<in> k'" unfolding * . }
              { assume "x \<in> k'" then show "x \<in> k" unfolding * . }
            qed
            show "\<forall>x y. x \<in> ?B b \<and> y \<in> ?B b \<longrightarrow> x = y"
              apply rule
              apply rule
              apply rule
              apply (unfold split_paired_all)
              unfolding mem_Collect_eq fst_conv snd_conv
              apply safe
            proof -
              fix x k k'
              assume k: "(b, k) \<in> p" "(b, k') \<in> p" "content k \<noteq> 0" "content k' \<noteq> 0"
              guess v using pb[OF k(1)] .. note v = conjunctD2[OF this]
              guess v' using pb[OF k(2)] .. note v' = conjunctD2[OF this]
              let ?v = "max v v'"
              have "box ?v b \<subseteq> k \<inter> k'"
                unfolding v v' by (auto simp: mem_box)
                note interior_mono[OF this,unfolded interior_Int]
              moreover have " ((b + ?v)/2) \<in> box ?v b"
                using k(3-) unfolding v v' content_eq_0 not_le by (auto simp: mem_box)
              ultimately have " ((b + ?v)/2) \<in> interior k \<inter> interior k'"
                unfolding interior_open[OF open_box] by auto
              then have *: "k = k'"
                apply -
                apply (rule ccontr)
                using p(5)[OF k(1-2)]
                apply auto
                done
              { assume "x \<in> k" then show "x \<in> k'" unfolding * . }
              { assume "x \<in> k'" then show "x\<in>k" unfolding * . }
            qed

            let ?a = a and ?b = b (* a is something else while proofing the next theorem. *)
            show "\<forall>x. x \<in> ?B a \<longrightarrow> norm ((\<lambda>(x, k). content k *\<^sub>R f' x - (f (Sup k) -
              f (Inf k))) x) \<le> e * (b - a) / 4"
              apply rule
              apply rule
              unfolding mem_Collect_eq
              unfolding split_paired_all fst_conv snd_conv
            proof (safe, goal_cases)
              case prems: 1
              guess v using pa[OF prems(1)] .. note v = conjunctD2[OF this]
              have "?a \<in> {?a..v}"
                using v(2) by auto
              then have "v \<le> ?b"
                using p(3)[OF prems(1)] unfolding subset_eq v by auto
              moreover have "{?a..v} \<subseteq> ball ?a da"
                using fineD[OF as(2) prems(1)]
                apply -
                apply (subst(asm) if_P)
                apply (rule refl)
                unfolding subset_eq
                apply safe
                apply (erule_tac x=" x" in ballE)
                apply (auto simp add:subset_eq dist_real_def v)
                done
              ultimately show ?case
                unfolding v interval_bounds_real[OF v(2)] box_real
                apply -
                apply(rule da(2)[of "v"])
                using prems fineD[OF as(2) prems(1)]
                unfolding v content_eq_0
                apply auto
                done
            qed
            show "\<forall>x. x \<in> ?B b \<longrightarrow> norm ((\<lambda>(x, k). content k *\<^sub>R f' x -
              (f (Sup k) - f (Inf k))) x) \<le> e * (b - a) / 4"
              apply rule
              apply rule
              unfolding mem_Collect_eq
              unfolding split_paired_all fst_conv snd_conv
            proof (safe, goal_cases)
              case prems: 1
              guess v using pb[OF prems(1)] .. note v = conjunctD2[OF this]
              have "?b \<in> {v.. ?b}"
                using v(2) by auto
              then have "v \<ge> ?a" using p(3)[OF prems(1)]
                unfolding subset_eq v by auto
              moreover have "{v..?b} \<subseteq> ball ?b db"
                using fineD[OF as(2) prems(1)]
                apply -
                apply (subst(asm) if_P, rule refl)
                unfolding subset_eq
                apply safe
                apply (erule_tac x=" x" in ballE)
                using ab
                apply (auto simp add:subset_eq v dist_real_def)
                done
              ultimately show ?case
                unfolding v
                unfolding interval_bounds_real[OF v(2)] box_real
                apply -
                apply(rule db(2)[of "v"])
                using prems fineD[OF as(2) prems(1)]
                unfolding v content_eq_0
                apply auto
                done
            qed
          qed (insert p(1) ab e, auto simp add: field_simps)
        qed auto
      qed
    qed
  qed
qed


subsection \<open>Stronger form with finite number of exceptional points.\<close>

lemma fundamental_theorem_of_calculus_interior_strong:
  fixes f :: "real \<Rightarrow> 'a::banach"
  assumes "finite s"
    and "a \<le> b"
    and "continuous_on {a .. b} f"
    and "\<forall>x\<in>{a <..< b} - s. (f has_vector_derivative f'(x)) (at x)"
  shows "(f' has_integral (f b - f a)) {a .. b}"
  using assms
proof (induct "card s" arbitrary: s a b)
  case 0
  show ?case
    apply (rule fundamental_theorem_of_calculus_interior)
    using 0
    apply auto
    done
next
  case (Suc n)
  from this(2) guess c s'
    apply -
    apply (subst(asm) eq_commute)
    unfolding card_Suc_eq
    apply (subst(asm)(2) eq_commute)
    apply (elim exE conjE)
    done
  note cs = this[rule_format]
  show ?case
  proof (cases "c \<in> box a b")
    case False
    then show ?thesis
      apply -
      apply (rule Suc(1)[OF cs(3) _ Suc(4,5)])
      apply safe
      defer
      apply (rule Suc(6)[rule_format])
      using Suc(3)
      unfolding cs
      apply auto
      done
  next
    have *: "f b - f a = (f c - f a) + (f b - f c)"
      by auto
    case True
    then have "a \<le> c" "c \<le> b"
      by (auto simp: mem_box)
    then show ?thesis
      apply (subst *)
      apply (rule has_integral_combine)
      apply assumption+
      apply (rule_tac[!] Suc(1)[OF cs(3)])
      using Suc(3)
      unfolding cs
    proof -
      show "continuous_on {a .. c} f" "continuous_on {c .. b} f"
        apply (rule_tac[!] continuous_on_subset[OF Suc(5)])
        using True
        apply (auto simp: mem_box)
        done
      let ?P = "\<lambda>i j. \<forall>x\<in>{i <..< j} - s'. (f has_vector_derivative f' x) (at x)"
      show "?P a c" "?P c b"
        apply safe
        apply (rule_tac[!] Suc(6)[rule_format])
        using True
        unfolding cs
        apply (auto simp: mem_box)
        done
    qed auto
  qed
qed

lemma fundamental_theorem_of_calculus_strong:
  fixes f :: "real \<Rightarrow> 'a::banach"
  assumes "finite s"
    and "a \<le> b"
    and "continuous_on {a .. b} f"
    and "\<forall>x\<in>{a .. b} - s. (f has_vector_derivative f'(x)) (at x)"
  shows "(f' has_integral (f b - f a)) {a .. b}"
  apply (rule fundamental_theorem_of_calculus_interior_strong[OF assms(1-3), of f'])
  using assms(4)
  apply (auto simp: mem_box)
  done

lemma indefinite_integral_continuous_left:
  fixes f:: "real \<Rightarrow> 'a::banach"
  assumes "f integrable_on {a .. b}"
    and "a < c"
    and "c \<le> b"
    and "e > 0"
  obtains d where "d > 0"
    and "\<forall>t. c - d < t \<and> t \<le> c \<longrightarrow> norm (integral {a .. c} f - integral {a .. t} f) < e"
proof -
  have "\<exists>w>0. \<forall>t. c - w < t \<and> t < c \<longrightarrow> norm (f c) * norm(c - t) < e / 3"
  proof (cases "f c = 0")
    case False
    hence "0 < e / 3 / norm (f c)" using \<open>e>0\<close> by simp
    then show ?thesis
      apply -
      apply rule
      apply rule
      apply assumption
      apply safe
    proof -
      fix t
      assume as: "t < c" and "c - e / 3 / norm (f c) < t"
      then have "c - t < e / 3 / norm (f c)"
        by auto
      then have "norm (c - t) < e / 3 / norm (f c)"
        using as by auto
      then show "norm (f c) * norm (c - t) < e / 3"
        using False
        apply -
        apply (subst mult.commute)
        apply (subst pos_less_divide_eq[symmetric])
        apply auto
        done
    qed
  next
    case True
    show ?thesis
      apply (rule_tac x=1 in exI)
      unfolding True
      using \<open>e > 0\<close>
      apply auto
      done
  qed
  then guess w .. note w = conjunctD2[OF this,rule_format]

  have *: "e / 3 > 0"
    using assms by auto
  have "f integrable_on {a .. c}"
    apply (rule integrable_subinterval_real[OF assms(1)])
    using assms(2-3)
    apply auto
    done
  from integrable_integral[OF this,unfolded has_integral_real,rule_format,OF *] guess d1 ..
  note d1 = conjunctD2[OF this,rule_format]
  define d where [abs_def]: "d x = ball x w \<inter> d1 x" for x
  have "gauge d"
    unfolding d_def using w(1) d1 by auto
  note this[unfolded gauge_def,rule_format,of c]
  note conjunctD2[OF this]
  from this(2)[unfolded open_contains_ball,rule_format,OF this(1)] guess k ..
  note k=conjunctD2[OF this]

  let ?d = "min k (c - a) / 2"
  show ?thesis
    apply (rule that[of ?d])
    apply safe
  proof -
    show "?d > 0"
      using k(1) using assms(2) by auto
    fix t
    assume as: "c - ?d < t" "t \<le> c"
    let ?thesis = "norm (integral ({a .. c}) f - integral ({a .. t}) f) < e"
    {
      presume *: "t < c \<Longrightarrow> ?thesis"
      show ?thesis
        apply (cases "t = c")
        defer
        apply (rule *)
        apply (subst less_le)
        using \<open>e > 0\<close> as(2)
        apply auto
        done
    }
    assume "t < c"

    have "f integrable_on {a .. t}"
      apply (rule integrable_subinterval_real[OF assms(1)])
      using assms(2-3) as(2)
      apply auto
      done
    from integrable_integral[OF this,unfolded has_integral_real,rule_format,OF *] guess d2 ..
    note d2 = conjunctD2[OF this,rule_format]
    define d3 where "d3 x = (if x \<le> t then d1 x \<inter> d2 x else d1 x)" for x
    have "gauge d3"
      using d2(1) d1(1) unfolding d3_def gauge_def by auto
    from fine_division_exists_real[OF this, of a t] guess p . note p=this
    note p'=tagged_division_ofD[OF this(1)]
    have pt: "\<forall>(x,k)\<in>p. x \<le> t"
    proof (safe, goal_cases)
      case prems: 1
      from p'(2,3)[OF prems] show ?case
        by auto
    qed
    with p(2) have "d2 fine p"
      unfolding fine_def d3_def
      apply safe
      apply (erule_tac x="(a,b)" in ballE)+
      apply auto
      done
    note d2_fin = d2(2)[OF conjI[OF p(1) this]]

    have *: "{a .. c} \<inter> {x. x \<bullet> 1 \<le> t} = {a .. t}" "{a .. c} \<inter> {x. x \<bullet> 1 \<ge> t} = {t .. c}"
      using assms(2-3) as by (auto simp add: field_simps)
    have "p \<union> {(c, {t .. c})} tagged_division_of {a .. c} \<and> d1 fine p \<union> {(c, {t .. c})}"
      apply rule
      apply (rule tagged_division_union_interval_real[of _ _ _ 1 "t"])
      unfolding *
      apply (rule p)
      apply (rule tagged_division_of_self_real)
      unfolding fine_def
      apply safe
    proof -
      fix x k y
      assume "(x,k) \<in> p" and "y \<in> k"
      then show "y \<in> d1 x"
        using p(2) pt
        unfolding fine_def d3_def
        apply -
        apply (erule_tac x="(x,k)" in ballE)+
        apply auto
        done
    next
      fix x assume "x \<in> {t..c}"
      then have "dist c x < k"
        unfolding dist_real_def
        using as(1)
        by (auto simp add: field_simps)
      then show "x \<in> d1 c"
        using k(2)
        unfolding d_def
        by auto
    qed (insert as(2), auto) note d1_fin = d1(2)[OF this]

    have *: "integral {a .. c} f - integral {a .. t} f = -(((c - t) *\<^sub>R f c + (\<Sum>(x, k)\<in>p. content k *\<^sub>R f x)) -
      integral {a .. c} f) + ((\<Sum>(x, k)\<in>p. content k *\<^sub>R f x) - integral {a .. t} f) + (c - t) *\<^sub>R f c"
      "e = (e/3 + e/3) + e/3"
      by auto
    have **: "(\<Sum>(x, k)\<in>p \<union> {(c, {t .. c})}. content k *\<^sub>R f x) =
      (c - t) *\<^sub>R f c + (\<Sum>(x, k)\<in>p. content k *\<^sub>R f x)"
    proof -
      have **: "\<And>x F. F \<union> {x} = insert x F"
        by auto
      have "(c, cbox t c) \<notin> p"
      proof (safe, goal_cases)
        case prems: 1
        from p'(2-3)[OF prems] have "c \<in> cbox a t"
          by auto
        then show False using \<open>t < c\<close>
          by auto
      qed
      then show ?thesis
        unfolding ** box_real
        apply -
        apply (subst setsum.insert)
        apply (rule p')
        unfolding split_conv
        defer
        apply (subst content_real)
        using as(2)
        apply auto
        done
    qed
    have ***: "c - w < t \<and> t < c"
    proof -
      have "c - k < t"
        using \<open>k>0\<close> as(1) by (auto simp add: field_simps)
      moreover have "k \<le> w"
        apply (rule ccontr)
        using k(2)
        unfolding subset_eq
        apply (erule_tac x="c + ((k + w)/2)" in ballE)
        unfolding d_def
        using \<open>k > 0\<close> \<open>w > 0\<close>
        apply (auto simp add: field_simps not_le not_less dist_real_def)
        done
      ultimately show ?thesis using \<open>t < c\<close>
        by (auto simp add: field_simps)
    qed
    show ?thesis
      unfolding *(1)
      apply (subst *(2))
      apply (rule norm_triangle_lt add_strict_mono)+
      unfolding norm_minus_cancel
      apply (rule d1_fin[unfolded **])
      apply (rule d2_fin)
      using w(2)[OF ***]
      unfolding norm_scaleR
      apply (auto simp add: field_simps)
      done
  qed
qed

lemma indefinite_integral_continuous_right:
  fixes f :: "real \<Rightarrow> 'a::banach"
  assumes "f integrable_on {a .. b}"
    and "a \<le> c"
    and "c < b"
    and "e > 0"
  obtains d where "0 < d"
    and "\<forall>t. c \<le> t \<and> t < c + d \<longrightarrow> norm (integral {a .. c} f - integral {a .. t} f) < e"
proof -
  have *: "(\<lambda>x. f (- x)) integrable_on {-b .. -a}" "- b < - c" "- c \<le> - a"
    using assms by auto
  from indefinite_integral_continuous_left[OF * \<open>e>0\<close>] guess d . note d = this
  let ?d = "min d (b - c)"
  show ?thesis
    apply (rule that[of "?d"])
    apply safe
  proof -
    show "0 < ?d"
      using d(1) assms(3) by auto
    fix t :: real
    assume as: "c \<le> t" "t < c + ?d"
    have *: "integral {a .. c} f = integral {a .. b} f - integral {c .. b} f"
      "integral {a .. t} f = integral {a .. b} f - integral {t .. b} f"
      apply (simp_all only: algebra_simps)
      apply (rule_tac[!] integral_combine)
      using assms as
      apply auto
      done
    have "(- c) - d < (- t) \<and> - t \<le> - c"
      using as by auto note d(2)[rule_format,OF this]
    then show "norm (integral {a .. c} f - integral {a .. t} f) < e"
      unfolding *
      unfolding integral_reflect
      apply (subst norm_minus_commute)
      apply (auto simp add: algebra_simps)
      done
  qed
qed

lemma indefinite_integral_continuous:
  fixes f :: "real \<Rightarrow> 'a::banach"
  assumes "f integrable_on {a .. b}"
  shows "continuous_on {a .. b} (\<lambda>x. integral {a .. x} f)"
proof (unfold continuous_on_iff, safe)
  fix x e :: real
  assume as: "x \<in> {a .. b}" "e > 0"
  let ?thesis = "\<exists>d>0. \<forall>x'\<in>{a .. b}. dist x' x < d \<longrightarrow> dist (integral {a .. x'} f) (integral {a .. x} f) < e"
  {
    presume *: "a < b \<Longrightarrow> ?thesis"
    show ?thesis
      apply cases
      apply (rule *)
      apply assumption
    proof goal_cases
      case 1
      then have "cbox a b = {x}"
        using as(1)
        apply -
        apply (rule set_eqI)
        apply auto
        done
      then show ?case using \<open>e > 0\<close> by auto
    qed
  }
  assume "a < b"
  have "(x = a \<or> x = b) \<or> (a < x \<and> x < b)"
    using as(1) by auto
  then show ?thesis
    apply (elim disjE)
  proof -
    assume "x = a"
    have "a \<le> a" ..
    from indefinite_integral_continuous_right[OF assms(1) this \<open>a<b\<close> \<open>e>0\<close>] guess d . note d=this
    show ?thesis
      apply rule
      apply rule
      apply (rule d)
      apply safe
      apply (subst dist_commute)
      unfolding \<open>x = a\<close> dist_norm
      apply (rule d(2)[rule_format])
      apply auto
      done
  next
    assume "x = b"
    have "b \<le> b" ..
    from indefinite_integral_continuous_left[OF assms(1) \<open>a<b\<close> this \<open>e>0\<close>] guess d . note d=this
    show ?thesis
      apply rule
      apply rule
      apply (rule d)
      apply safe
      apply (subst dist_commute)
      unfolding \<open>x = b\<close> dist_norm
      apply (rule d(2)[rule_format])
      apply auto
      done
  next
    assume "a < x \<and> x < b"
    then have xl: "a < x" "x \<le> b" and xr: "a \<le> x" "x < b"
      by auto
    from indefinite_integral_continuous_left [OF assms(1) xl \<open>e>0\<close>] guess d1 . note d1=this
    from indefinite_integral_continuous_right[OF assms(1) xr \<open>e>0\<close>] guess d2 . note d2=this
    show ?thesis
      apply (rule_tac x="min d1 d2" in exI)
    proof safe
      show "0 < min d1 d2"
        using d1 d2 by auto
      fix y
      assume "y \<in> {a .. b}" and "dist y x < min d1 d2"
      then show "dist (integral {a .. y} f) (integral {a .. x} f) < e"
        apply (subst dist_commute)
        apply (cases "y < x")
        unfolding dist_norm
        apply (rule d1(2)[rule_format])
        defer
        apply (rule d2(2)[rule_format])
        unfolding not_less
        apply (auto simp add: field_simps)
        done
    qed
  qed
qed


subsection \<open>This doesn't directly involve integration, but that gives an easy proof.\<close>

lemma has_derivative_zero_unique_strong_interval:
  fixes f :: "real \<Rightarrow> 'a::banach"
  assumes "finite k"
    and "continuous_on {a .. b} f"
    and "f a = y"
    and "\<forall>x\<in>({a .. b} - k). (f has_derivative (\<lambda>h. 0)) (at x within {a .. b})" "x \<in> {a .. b}"
  shows "f x = y"
proof -
  have ab: "a \<le> b"
    using assms by auto
  have *: "a \<le> x"
    using assms(5) by auto
  have "((\<lambda>x. 0::'a) has_integral f x - f a) {a .. x}"
    apply (rule fundamental_theorem_of_calculus_interior_strong[OF assms(1) *])
    apply (rule continuous_on_subset[OF assms(2)])
    defer
    apply safe
    unfolding has_vector_derivative_def
    apply (subst has_derivative_within_open[symmetric])
    apply assumption
    apply (rule open_greaterThanLessThan)
    apply (rule has_derivative_within_subset[where s="{a .. b}"])
    using assms(4) assms(5)
    apply (auto simp: mem_box)
    done
  note this[unfolded *]
  note has_integral_unique[OF has_integral_0 this]
  then show ?thesis
    unfolding assms by auto
qed


subsection \<open>Generalize a bit to any convex set.\<close>

lemma has_derivative_zero_unique_strong_convex:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::banach"
  assumes "convex s"
    and "finite k"
    and "continuous_on s f"
    and "c \<in> s"
    and "f c = y"
    and "\<forall>x\<in>(s - k). (f has_derivative (\<lambda>h. 0)) (at x within s)"
    and "x \<in> s"
  shows "f x = y"
proof -
  {
    presume *: "x \<noteq> c \<Longrightarrow> ?thesis"
    show ?thesis
      apply cases
      apply (rule *)
      apply assumption
      unfolding assms(5)[symmetric]
      apply auto
      done
  }
  assume "x \<noteq> c"
  note conv = assms(1)[unfolded convex_alt,rule_format]
  have as1: "continuous_on {0 ..1} (f \<circ> (\<lambda>t. (1 - t) *\<^sub>R c + t *\<^sub>R x))"
    apply (rule continuous_intros)+
    apply (rule continuous_on_subset[OF assms(3)])
    apply safe
    apply (rule conv)
    using assms(4,7)
    apply auto
    done
  have *: "t = xa" if "(1 - t) *\<^sub>R c + t *\<^sub>R x = (1 - xa) *\<^sub>R c + xa *\<^sub>R x" for t xa
  proof -
    from that have "(t - xa) *\<^sub>R x = (t - xa) *\<^sub>R c"
      unfolding scaleR_simps by (auto simp add: algebra_simps)
    then show ?thesis
      using \<open>x \<noteq> c\<close> by auto
  qed
  have as2: "finite {t. ((1 - t) *\<^sub>R c + t *\<^sub>R x) \<in> k}"
    using assms(2)
    apply (rule finite_surj[where f="\<lambda>z. SOME t. (1-t) *\<^sub>R c + t *\<^sub>R x = z"])
    apply safe
    unfolding image_iff
    apply rule
    defer
    apply assumption
    apply (rule sym)
    apply (rule some_equality)
    defer
    apply (drule *)
    apply auto
    done
  have "(f \<circ> (\<lambda>t. (1 - t) *\<^sub>R c + t *\<^sub>R x)) 1 = y"
    apply (rule has_derivative_zero_unique_strong_interval[OF as2 as1, of ])
    unfolding o_def
    using assms(5)
    defer
    apply -
    apply rule
  proof -
    fix t
    assume as: "t \<in> {0 .. 1} - {t. (1 - t) *\<^sub>R c + t *\<^sub>R x \<in> k}"
    have *: "c - t *\<^sub>R c + t *\<^sub>R x \<in> s - k"
      apply safe
      apply (rule conv[unfolded scaleR_simps])
      using \<open>x \<in> s\<close> \<open>c \<in> s\<close> as
      by (auto simp add: algebra_simps)
    have "(f \<circ> (\<lambda>t. (1 - t) *\<^sub>R c + t *\<^sub>R x) has_derivative (\<lambda>x. 0) \<circ> (\<lambda>z. (0 - z *\<^sub>R c) + z *\<^sub>R x))
      (at t within {0 .. 1})"
      apply (intro derivative_eq_intros)
      apply simp_all
      apply (simp add: field_simps)
      unfolding scaleR_simps
      apply (rule has_derivative_within_subset,rule assms(6)[rule_format])
      apply (rule *)
      apply safe
      apply (rule conv[unfolded scaleR_simps])
      using \<open>x \<in> s\<close> \<open>c \<in> s\<close>
      apply auto
      done
    then show "((\<lambda>xa. f ((1 - xa) *\<^sub>R c + xa *\<^sub>R x)) has_derivative (\<lambda>h. 0)) (at t within {0 .. 1})"
      unfolding o_def .
  qed auto
  then show ?thesis
    by auto
qed


text \<open>Also to any open connected set with finite set of exceptions. Could
 generalize to locally convex set with limpt-free set of exceptions.\<close>

lemma has_derivative_zero_unique_strong_connected:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::banach"
  assumes "connected s"
    and "open s"
    and "finite k"
    and "continuous_on s f"
    and "c \<in> s"
    and "f c = y"
    and "\<forall>x\<in>(s - k). (f has_derivative (\<lambda>h. 0)) (at x within s)"
    and "x\<in>s"
  shows "f x = y"
proof -
  have "{x \<in> s. f x \<in> {y}} = {} \<or> {x \<in> s. f x \<in> {y}} = s"
    apply (rule assms(1)[unfolded connected_clopen,rule_format])
    apply rule
    defer
    apply (rule continuous_closedin_preimage[OF assms(4) closed_singleton])
    apply (rule open_openin_trans[OF assms(2)])
    unfolding open_contains_ball
  proof safe
    fix x
    assume "x \<in> s"
    from assms(2)[unfolded open_contains_ball,rule_format,OF this] guess e .. note e=conjunctD2[OF this]
    show "\<exists>e>0. ball x e \<subseteq> {xa \<in> s. f xa \<in> {f x}}"
      apply rule
      apply rule
      apply (rule e)
    proof safe
      fix y
      assume y: "y \<in> ball x e"
      then show "y \<in> s"
        using e by auto
      show "f y = f x"
        apply (rule has_derivative_zero_unique_strong_convex[OF convex_ball])
        apply (rule assms)
        apply (rule continuous_on_subset)
        apply (rule assms)
        apply (rule e)+
        apply (subst centre_in_ball)
        apply (rule e)
        apply rule
        apply safe
        apply (rule has_derivative_within_subset)
        apply (rule assms(7)[rule_format])
        using y e
        apply auto
        done
    qed
  qed
  then show ?thesis
    using \<open>x \<in> s\<close> \<open>f c = y\<close> \<open>c \<in> s\<close> by auto
qed

lemma has_derivative_zero_connected_constant:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::banach"
  assumes "connected s"
      and "open s"
      and "finite k"
      and "continuous_on s f"
      and "\<forall>x\<in>(s - k). (f has_derivative (\<lambda>h. 0)) (at x within s)"
    obtains c where "\<And>x. x \<in> s \<Longrightarrow> f(x) = c"
proof (cases "s = {}")
  case True
  then show ?thesis
by (metis empty_iff that)
next
  case False
  then obtain c where "c \<in> s"
    by (metis equals0I)
  then show ?thesis
    by (metis has_derivative_zero_unique_strong_connected assms that)
qed


subsection \<open>Integrating characteristic function of an interval\<close>

lemma has_integral_restrict_open_subinterval:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::banach"
  assumes "(f has_integral i) (cbox c d)"
    and "cbox c d \<subseteq> cbox a b"
  shows "((\<lambda>x. if x \<in> box c d then f x else 0) has_integral i) (cbox a b)"
proof -
  define g where [abs_def]: "g x = (if x \<in>box c d then f x else 0)" for x
  {
    presume *: "cbox c d \<noteq> {} \<Longrightarrow> ?thesis"
    show ?thesis
      apply cases
      apply (rule *)
      apply assumption
    proof goal_cases
      case prems: 1
      then have *: "box c d = {}"
        by (metis bot.extremum_uniqueI box_subset_cbox)
      show ?thesis
        using assms(1)
        unfolding *
        using prems
        by auto
    qed
  }
  assume "cbox c d \<noteq> {}"
  from partial_division_extend_1 [OF assms(2) this] guess p . note p=this
  interpret comm_monoid_set "lift_option plus" "Some (0 :: 'b)"
    apply (rule comm_monoid_set.intro)
    apply (rule comm_monoid_lift_option)
    apply (rule add.comm_monoid_axioms)
    done
  note operat = operative_division
    [OF operative_integral p(1), symmetric]
  let ?P = "(if g integrable_on cbox a b then Some (integral (cbox a b) g) else None) = Some i"
  {
    presume "?P"
    then have "g integrable_on cbox a b \<and> integral (cbox a b) g = i"
      apply -
      apply cases
      apply (subst(asm) if_P)
      apply assumption
      apply auto
      done
    then show ?thesis
      using integrable_integral
      unfolding g_def
      by auto
  }
  let ?F = F
  have iterate:"?F (\<lambda>i. if g integrable_on i then Some (integral i g) else None) (p - {cbox c d}) = Some 0"
  proof (intro neutral ballI)
    fix x
    assume x: "x \<in> p - {cbox c d}"
    then have "x \<in> p"
      by auto
    note div = division_ofD(2-5)[OF p(1) this]
    from div(3) guess u v by (elim exE) note uv=this
    have "interior x \<inter> interior (cbox c d) = {}"
      using div(4)[OF p(2)] x by auto
    then have "(g has_integral 0) x"
      unfolding uv
      apply -
      apply (rule has_integral_spike_interior[where f="\<lambda>x. 0"])
      unfolding g_def interior_cbox
      apply auto
      done
    then show "(if g integrable_on x then Some (integral x g) else None) = Some 0"
      by auto
  qed

  have *: "p = insert (cbox c d) (p - {cbox c d})"
    using p by auto
  interpret comm_monoid_set "lift_option plus" "Some (0 :: 'b)"
    apply (rule comm_monoid_set.intro)
    apply (rule comm_monoid_lift_option)
    apply (rule add.comm_monoid_axioms)
    done
  have **: "g integrable_on cbox c d"
    apply (rule integrable_spike_interior[where f=f])
    unfolding g_def  using assms(1)
    apply auto
    done
  moreover
  have "integral (cbox c d) g = i"
    apply (rule has_integral_unique[OF _ assms(1)])
    apply (rule has_integral_spike_interior[where f=g])
    defer
    apply (rule integrable_integral[OF **])
    unfolding g_def
    apply auto
    done
  ultimately show ?P
    unfolding operat
    using p
    apply (subst *)
    apply (subst insert)
    apply (simp_all add: division_of_finite iterate)
    done
qed

lemma has_integral_restrict_closed_subinterval:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::banach"
  assumes "(f has_integral i) (cbox c d)"
    and "cbox c d \<subseteq> cbox a b"
  shows "((\<lambda>x. if x \<in> cbox c d then f x else 0) has_integral i) (cbox a b)"
proof -
  note has_integral_restrict_open_subinterval[OF assms]
  note * = has_integral_spike[OF negligible_frontier_interval _ this]
  show ?thesis
    apply (rule *[of c d])
    using box_subset_cbox[of c d]
    apply auto
    done
qed

lemma has_integral_restrict_closed_subintervals_eq:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::banach"
  assumes "cbox c d \<subseteq> cbox a b"
  shows "((\<lambda>x. if x \<in> cbox c d then f x else 0) has_integral i) (cbox a b) \<longleftrightarrow> (f has_integral i) (cbox c d)"
  (is "?l = ?r")
proof (cases "cbox c d = {}")
  case False
  let ?g = "\<lambda>x. if x \<in> cbox c d then f x else 0"
  show ?thesis
    apply rule
    defer
    apply (rule has_integral_restrict_closed_subinterval[OF _ assms])
    apply assumption
  proof -
    assume ?l
    then have "?g integrable_on cbox c d"
      using assms has_integral_integrable integrable_subinterval by blast
    then have *: "f integrable_on cbox c d"
      apply -
      apply (rule integrable_eq)
      apply auto
      done
    then have "i = integral (cbox c d) f"
      apply -
      apply (rule has_integral_unique)
      apply (rule \<open>?l\<close>)
      apply (rule has_integral_restrict_closed_subinterval[OF _ assms])
      apply auto
      done
    then show ?r
      using * by auto
  qed
qed auto


text \<open>Hence we can apply the limit process uniformly to all integrals.\<close>

lemma has_integral':
  fixes f :: "'n::euclidean_space \<Rightarrow> 'a::banach"
  shows "(f has_integral i) s \<longleftrightarrow>
    (\<forall>e>0. \<exists>B>0. \<forall>a b. ball 0 B \<subseteq> cbox a b \<longrightarrow>
      (\<exists>z. ((\<lambda>x. if x \<in> s then f(x) else 0) has_integral z) (cbox a b) \<and> norm(z - i) < e))"
  (is "?l \<longleftrightarrow> (\<forall>e>0. ?r e)")
proof -
  {
    presume *: "\<exists>a b. s = cbox a b \<Longrightarrow> ?thesis"
    show ?thesis
      apply cases
      apply (rule *)
      apply assumption
      apply (subst has_integral_alt)
      apply auto
      done
  }
  assume "\<exists>a b. s = cbox a b"
  then guess a b by (elim exE) note s=this
  from bounded_cbox[of a b, unfolded bounded_pos] guess B ..
  note B = conjunctD2[OF this,rule_format] show ?thesis
    apply safe
  proof -
    fix e :: real
    assume ?l and "e > 0"
    show "?r e"
      apply (rule_tac x="B+1" in exI)
      apply safe
      defer
      apply (rule_tac x=i in exI)
    proof
      fix c d :: 'n
      assume as: "ball 0 (B+1) \<subseteq> cbox c d"
      then show "((\<lambda>x. if x \<in> s then f x else 0) has_integral i) (cbox c d)"
        unfolding s
        apply -
        apply (rule has_integral_restrict_closed_subinterval)
        apply (rule \<open>?l\<close>[unfolded s])
        apply safe
        apply (drule B(2)[rule_format])
        unfolding subset_eq
        apply (erule_tac x=x in ballE)
        apply (auto simp add: dist_norm)
        done
    qed (insert B \<open>e>0\<close>, auto)
  next
    assume as: "\<forall>e>0. ?r e"
    from this[rule_format,OF zero_less_one] guess C .. note C=conjunctD2[OF this,rule_format]
    define c :: 'n where "c = (\<Sum>i\<in>Basis. (- max B C) *\<^sub>R i)"
    define d :: 'n where "d = (\<Sum>i\<in>Basis. max B C *\<^sub>R i)"
    have c_d: "cbox a b \<subseteq> cbox c d"
      apply safe
      apply (drule B(2))
      unfolding mem_box
    proof
      fix x i
      show "c \<bullet> i \<le> x \<bullet> i \<and> x \<bullet> i \<le> d \<bullet> i" if "norm x \<le> B" and "i \<in> Basis"
        using that and Basis_le_norm[OF \<open>i\<in>Basis\<close>, of x]
        unfolding c_def d_def
        by (auto simp add: field_simps setsum_negf)
    qed
    have "ball 0 C \<subseteq> cbox c d"
      apply (rule subsetI)
      unfolding mem_box mem_ball dist_norm
    proof
      fix x i :: 'n
      assume x: "norm (0 - x) < C" and i: "i \<in> Basis"
      show "c \<bullet> i \<le> x \<bullet> i \<and> x \<bullet> i \<le> d \<bullet> i"
        using Basis_le_norm[OF i, of x] and x i
        unfolding c_def d_def
        by (auto simp: setsum_negf)
    qed
    from C(2)[OF this] have "\<exists>y. (f has_integral y) (cbox a b)"
      unfolding has_integral_restrict_closed_subintervals_eq[OF c_d,symmetric]
      unfolding s
      by auto
    then guess y .. note y=this

    have "y = i"
    proof (rule ccontr)
      assume "\<not> ?thesis"
      then have "0 < norm (y - i)"
        by auto
      from as[rule_format,OF this] guess C ..  note C=conjunctD2[OF this,rule_format]
      define c :: 'n where "c = (\<Sum>i\<in>Basis. (- max B C) *\<^sub>R i)"
      define d :: 'n where "d = (\<Sum>i\<in>Basis. max B C *\<^sub>R i)"
      have c_d: "cbox a b \<subseteq> cbox c d"
        apply safe
        apply (drule B(2))
        unfolding mem_box
      proof
        fix x i :: 'n
        assume "norm x \<le> B" and "i \<in> Basis"
        then show "c \<bullet> i \<le> x \<bullet> i \<and> x \<bullet> i \<le> d \<bullet> i"
          using Basis_le_norm[of i x]
          unfolding c_def d_def
          by (auto simp add: field_simps setsum_negf)
      qed
      have "ball 0 C \<subseteq> cbox c d"
        apply (rule subsetI)
        unfolding mem_box mem_ball dist_norm
      proof
        fix x i :: 'n
        assume "norm (0 - x) < C" and "i \<in> Basis"
        then show "c \<bullet> i \<le> x \<bullet> i \<and> x \<bullet> i \<le> d \<bullet> i"
          using Basis_le_norm[of i x]
          unfolding c_def d_def
          by (auto simp: setsum_negf)
      qed
      note C(2)[OF this] then guess z .. note z = conjunctD2[OF this, unfolded s]
      note this[unfolded has_integral_restrict_closed_subintervals_eq[OF c_d]]
      then have "z = y" and "norm (z - i) < norm (y - i)"
        apply -
        apply (rule has_integral_unique[OF _ y(1)])
        apply assumption
        apply assumption
        done
      then show False
        by auto
    qed
    then show ?l
      using y
      unfolding s
      by auto
  qed
qed

lemma has_integral_le:
  fixes f :: "'n::euclidean_space \<Rightarrow> real"
  assumes "(f has_integral i) s"
    and "(g has_integral j) s"
    and "\<forall>x\<in>s. f x \<le> g x"
  shows "i \<le> j"
  using has_integral_component_le[OF _ assms(1-2), of 1]
  using assms(3)
  by auto

lemma integral_le:
  fixes f :: "'n::euclidean_space \<Rightarrow> real"
  assumes "f integrable_on s"
    and "g integrable_on s"
    and "\<forall>x\<in>s. f x \<le> g x"
  shows "integral s f \<le> integral s g"
  by (rule has_integral_le[OF assms(1,2)[unfolded has_integral_integral] assms(3)])

lemma has_integral_nonneg:
  fixes f :: "'n::euclidean_space \<Rightarrow> real"
  assumes "(f has_integral i) s"
    and "\<forall>x\<in>s. 0 \<le> f x"
  shows "0 \<le> i"
  using has_integral_component_nonneg[of 1 f i s]
  unfolding o_def
  using assms
  by auto

lemma integral_nonneg:
  fixes f :: "'n::euclidean_space \<Rightarrow> real"
  assumes "f integrable_on s"
    and "\<forall>x\<in>s. 0 \<le> f x"
  shows "0 \<le> integral s f"
  by (rule has_integral_nonneg[OF assms(1)[unfolded has_integral_integral] assms(2)])


text \<open>Hence a general restriction property.\<close>

lemma has_integral_restrict[simp]:
  assumes "s \<subseteq> t"
  shows "((\<lambda>x. if x \<in> s then f x else (0::'a::banach)) has_integral i) t \<longleftrightarrow> (f has_integral i) s"
proof -
  have *: "\<And>x. (if x \<in> t then if x \<in> s then f x else 0 else 0) =  (if x\<in>s then f x else 0)"
    using assms by auto
  show ?thesis
    apply (subst(2) has_integral')
    apply (subst has_integral')
    unfolding *
    apply rule
    done
qed

lemma has_integral_restrict_univ:
  fixes f :: "'n::euclidean_space \<Rightarrow> 'a::banach"
  shows "((\<lambda>x. if x \<in> s then f x else 0) has_integral i) UNIV \<longleftrightarrow> (f has_integral i) s"
  by auto

lemma has_integral_on_superset:
  fixes f :: "'n::euclidean_space \<Rightarrow> 'a::banach"
  assumes "\<forall>x. x \<notin> s \<longrightarrow> f x = 0"
    and "s \<subseteq> t"
    and "(f has_integral i) s"
  shows "(f has_integral i) t"
proof -
  have "(\<lambda>x. if x \<in> s then f x else 0) = (\<lambda>x. if x \<in> t then f x else 0)"
    apply rule
    using assms(1-2)
    apply auto
    done
  then show ?thesis
    using assms(3)
    apply (subst has_integral_restrict_univ[symmetric])
    apply (subst(asm) has_integral_restrict_univ[symmetric])
    apply auto
    done
qed

lemma integrable_on_superset:
  fixes f :: "'n::euclidean_space \<Rightarrow> 'a::banach"
  assumes "\<forall>x. x \<notin> s \<longrightarrow> f x = 0"
    and "s \<subseteq> t"
    and "f integrable_on s"
  shows "f integrable_on t"
  using assms
  unfolding integrable_on_def
  by (auto intro:has_integral_on_superset)

lemma integral_restrict_univ[intro]:
  fixes f :: "'n::euclidean_space \<Rightarrow> 'a::banach"
  shows "f integrable_on s \<Longrightarrow> integral UNIV (\<lambda>x. if x \<in> s then f x else 0) = integral s f"
  apply (rule integral_unique)
  unfolding has_integral_restrict_univ
  apply auto
  done

lemma integrable_restrict_univ:
  fixes f :: "'n::euclidean_space \<Rightarrow> 'a::banach"
  shows "(\<lambda>x. if x \<in> s then f x else 0) integrable_on UNIV \<longleftrightarrow> f integrable_on s"
  unfolding integrable_on_def
  by auto

lemma negligible_on_intervals: "negligible s \<longleftrightarrow> (\<forall>a b. negligible(s \<inter> cbox a b))" (is "?l \<longleftrightarrow> ?r")
proof
  assume ?r
  show ?l
    unfolding negligible_def
  proof safe
    fix a b
    show "(indicator s has_integral 0) (cbox a b)"
      apply (rule has_integral_negligible[OF \<open>?r\<close>[rule_format,of a b]])
      unfolding indicator_def
      apply auto
      done
  qed
qed auto

lemma negligible_translation:
  assumes "negligible S"
    shows "negligible (op + c ` S)"
proof -
  have inj: "inj (op + c)"
    by simp
  show ?thesis
  using assms
  proof (clarsimp simp: negligible_def)
    fix a b
    assume "\<forall>x y. (indicator S has_integral 0) (cbox x y)"
    then have *: "(indicator S has_integral 0) (cbox (a-c) (b-c))"
      by (meson Diff_iff assms has_integral_negligible indicator_simps(2))
    have eq: "indicator (op + c ` S) = (\<lambda>x. indicator S (x - c))"
      by (force simp add: indicator_def)
    show "(indicator (op + c ` S) has_integral 0) (cbox a b)"
      using has_integral_affinity [OF *, of 1 "-c"]
            cbox_translation [of "c" "-c+a" "-c+b"]
      by (simp add: eq add.commute)
  qed
qed

lemma negligible_translation_rev:
  assumes "negligible (op + c ` S)"
    shows "negligible S"
by (metis negligible_translation [OF assms, of "-c"] translation_galois)

lemma has_integral_spike_set_eq:
  fixes f :: "'n::euclidean_space \<Rightarrow> 'a::banach"
  assumes "negligible ((s - t) \<union> (t - s))"
  shows "(f has_integral y) s \<longleftrightarrow> (f has_integral y) t"
  unfolding has_integral_restrict_univ[symmetric,of f]
  apply (rule has_integral_spike_eq[OF assms])
  by (auto split: if_split_asm)

lemma has_integral_spike_set[dest]:
  fixes f :: "'n::euclidean_space \<Rightarrow> 'a::banach"
  assumes "negligible ((s - t) \<union> (t - s))"
    and "(f has_integral y) s"
  shows "(f has_integral y) t"
  using assms has_integral_spike_set_eq
  by auto

lemma integrable_spike_set[dest]:
  fixes f :: "'n::euclidean_space \<Rightarrow> 'a::banach"
  assumes "negligible ((s - t) \<union> (t - s))"
    and "f integrable_on s"
  shows "f integrable_on t"
  using assms(2)
  unfolding integrable_on_def
  unfolding has_integral_spike_set_eq[OF assms(1)] .

lemma integrable_spike_set_eq:
  fixes f :: "'n::euclidean_space \<Rightarrow> 'a::banach"
  assumes "negligible ((s - t) \<union> (t - s))"
  shows "f integrable_on s \<longleftrightarrow> f integrable_on t"
  apply rule
  apply (rule_tac[!] integrable_spike_set)
  using assms
  apply auto
  done

(*lemma integral_spike_set:
 "\<forall>f:real^M->real^N g s t.
        negligible(s DIFF t \<union> t DIFF s)
        \<longrightarrow> integral s f = integral t f"
qed  REPEAT STRIP_TAC THEN REWRITE_TAC[integral] THEN
  AP_TERM_TAC THEN ABS_TAC THEN MATCH_MP_TAC HAS_INTEGRAL_SPIKE_SET_EQ THEN
  ASM_MESON_TAC[]);;

lemma has_integral_interior:
 "\<forall>f:real^M->real^N y s.
        negligible(frontier s)
        \<longrightarrow> ((f has_integral y) (interior s) \<longleftrightarrow> (f has_integral y) s)"
qed  REPEAT STRIP_TAC THEN MATCH_MP_TAC HAS_INTEGRAL_SPIKE_SET_EQ THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
    NEGLIGIBLE_SUBSET)) THEN
  REWRITE_TAC[frontier] THEN
  MP_TAC(ISPEC `s:real^M->bool` INTERIOR_SUBSET) THEN
  MP_TAC(ISPEC `s:real^M->bool` CLOSURE_SUBSET) THEN
  SET_TAC[]);;

lemma has_integral_closure:
 "\<forall>f:real^M->real^N y s.
        negligible(frontier s)
        \<longrightarrow> ((f has_integral y) (closure s) \<longleftrightarrow> (f has_integral y) s)"
qed  REPEAT STRIP_TAC THEN MATCH_MP_TAC HAS_INTEGRAL_SPIKE_SET_EQ THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
    NEGLIGIBLE_SUBSET)) THEN
  REWRITE_TAC[frontier] THEN
  MP_TAC(ISPEC `s:real^M->bool` INTERIOR_SUBSET) THEN
  MP_TAC(ISPEC `s:real^M->bool` CLOSURE_SUBSET) THEN
  SET_TAC[]);;*)


subsection \<open>More lemmas that are useful later\<close>

lemma has_integral_subset_component_le:
  fixes f :: "'n::euclidean_space \<Rightarrow> 'm::euclidean_space"
  assumes k: "k \<in> Basis"
    and as: "s \<subseteq> t" "(f has_integral i) s" "(f has_integral j) t" "\<forall>x\<in>t. 0 \<le> f(x)\<bullet>k"
  shows "i\<bullet>k \<le> j\<bullet>k"
proof -
  note has_integral_restrict_univ[symmetric, of f]
  note as(2-3)[unfolded this] note * = has_integral_component_le[OF k this]
  show ?thesis
    apply (rule *)
    using as(1,4)
    apply auto
    done
qed

lemma has_integral_subset_le:
  fixes f :: "'n::euclidean_space \<Rightarrow> real"
  assumes "s \<subseteq> t"
    and "(f has_integral i) s"
    and "(f has_integral j) t"
    and "\<forall>x\<in>t. 0 \<le> f x"
  shows "i \<le> j"
  using has_integral_subset_component_le[OF _ assms(1), of 1 f i j]
  using assms
  by auto

lemma integral_subset_component_le:
  fixes f :: "'n::euclidean_space \<Rightarrow> 'm::euclidean_space"
  assumes "k \<in> Basis"
    and "s \<subseteq> t"
    and "f integrable_on s"
    and "f integrable_on t"
    and "\<forall>x \<in> t. 0 \<le> f x \<bullet> k"
  shows "(integral s f)\<bullet>k \<le> (integral t f)\<bullet>k"
  apply (rule has_integral_subset_component_le)
  using assms
  apply auto
  done

lemma integral_subset_le:
  fixes f :: "'n::euclidean_space \<Rightarrow> real"
  assumes "s \<subseteq> t"
    and "f integrable_on s"
    and "f integrable_on t"
    and "\<forall>x \<in> t. 0 \<le> f x"
  shows "integral s f \<le> integral t f"
  apply (rule has_integral_subset_le)
  using assms
  apply auto
  done

lemma has_integral_alt':
  fixes f :: "'n::euclidean_space \<Rightarrow> 'a::banach"
  shows "(f has_integral i) s \<longleftrightarrow> (\<forall>a b. (\<lambda>x. if x \<in> s then f x else 0) integrable_on cbox a b) \<and>
    (\<forall>e>0. \<exists>B>0. \<forall>a b. ball 0 B \<subseteq> cbox a b \<longrightarrow>
      norm (integral (cbox a b) (\<lambda>x. if x \<in> s then f x else 0) - i) < e)"
  (is "?l = ?r")
proof
  assume ?r
  show ?l
    apply (subst has_integral')
    apply safe
  proof goal_cases
    case (1 e)
    from \<open>?r\<close>[THEN conjunct2,rule_format,OF this] guess B .. note B=conjunctD2[OF this]
    show ?case
      apply rule
      apply rule
      apply (rule B)
      apply safe
      apply (rule_tac x="integral (cbox a b) (\<lambda>x. if x \<in> s then f x else 0)" in exI)
      apply (drule B(2)[rule_format])
      using integrable_integral[OF \<open>?r\<close>[THEN conjunct1,rule_format]]
      apply auto
      done
  qed
next
  assume ?l note as = this[unfolded has_integral'[of f],rule_format]
  let ?f = "\<lambda>x. if x \<in> s then f x else 0"
  show ?r
  proof safe
    fix a b :: 'n
    from as[OF zero_less_one] guess B .. note B=conjunctD2[OF this,rule_format]
    let ?a = "\<Sum>i\<in>Basis. min (a\<bullet>i) (-B) *\<^sub>R i::'n"
    let ?b = "\<Sum>i\<in>Basis. max (b\<bullet>i) B *\<^sub>R i::'n"
    show "?f integrable_on cbox a b"
    proof (rule integrable_subinterval[of _ ?a ?b])
      have "ball 0 B \<subseteq> cbox ?a ?b"
        apply (rule subsetI)
        unfolding mem_ball mem_box dist_norm
      proof (rule, goal_cases)
        case (1 x i)
        then show ?case using Basis_le_norm[of i x]
          by (auto simp add:field_simps)
      qed
      from B(2)[OF this] guess z .. note conjunct1[OF this]
      then show "?f integrable_on cbox ?a ?b"
        unfolding integrable_on_def by auto
      show "cbox a b \<subseteq> cbox ?a ?b"
        apply safe
        unfolding mem_box
        apply rule
        apply (erule_tac x=i in ballE)
        apply auto
        done
    qed

    fix e :: real
    assume "e > 0"
    from as[OF this] guess B .. note B=conjunctD2[OF this,rule_format]
    show "\<exists>B>0. \<forall>a b. ball 0 B \<subseteq> cbox a b \<longrightarrow>
      norm (integral (cbox a b) (\<lambda>x. if x \<in> s then f x else 0) - i) < e"
      apply rule
      apply rule
      apply (rule B)
      apply safe
    proof goal_cases
      case 1
      from B(2)[OF this] guess z .. note z=conjunctD2[OF this]
      from integral_unique[OF this(1)] show ?case
        using z(2) by auto
    qed
  qed
qed


subsection \<open>Continuity of the integral (for a 1-dimensional interval).\<close>

lemma integrable_alt:
  fixes f :: "'n::euclidean_space \<Rightarrow> 'a::banach"
  shows "f integrable_on s \<longleftrightarrow>
    (\<forall>a b. (\<lambda>x. if x \<in> s then f x else 0) integrable_on cbox a b) \<and>
    (\<forall>e>0. \<exists>B>0. \<forall>a b c d. ball 0 B \<subseteq> cbox a b \<and> ball 0 B \<subseteq> cbox c d \<longrightarrow>
    norm (integral (cbox a b) (\<lambda>x. if x \<in> s then f x else 0) -
      integral (cbox c d)  (\<lambda>x. if x \<in> s then f x else 0)) < e)"
  (is "?l = ?r")
proof
  assume ?l
  then guess y unfolding integrable_on_def .. note this[unfolded has_integral_alt'[of f]]
  note y=conjunctD2[OF this,rule_format]
  show ?r
    apply safe
    apply (rule y)
  proof goal_cases
    case (1 e)
    then have "e/2 > 0"
      by auto
    from y(2)[OF this] guess B .. note B=conjunctD2[OF this,rule_format]
    show ?case
      apply rule
      apply rule
      apply (rule B)
      apply safe
    proof goal_cases
      case prems: (1 a b c d)
      show ?case
        apply (rule norm_triangle_half_l)
        using B(2)[OF prems(1)] B(2)[OF prems(2)]
        apply auto
        done
    qed
  qed
next
  assume ?r
  note as = conjunctD2[OF this,rule_format]
  let ?cube = "\<lambda>n. cbox (\<Sum>i\<in>Basis. - real n *\<^sub>R i::'n) (\<Sum>i\<in>Basis. real n *\<^sub>R i)"
  have "Cauchy (\<lambda>n. integral (?cube n) (\<lambda>x. if x \<in> s then f x else 0))"
  proof (unfold Cauchy_def, safe, goal_cases)
    case (1 e)
    from as(2)[OF this] guess B .. note B = conjunctD2[OF this,rule_format]
    from real_arch_simple[of B] guess N .. note N = this
    {
      fix n
      assume n: "n \<ge> N"
      have "ball 0 B \<subseteq> ?cube n"
        apply (rule subsetI)
        unfolding mem_ball mem_box dist_norm
      proof (rule, goal_cases)
        case (1 x i)
        then show ?case
          using Basis_le_norm[of i x] \<open>i\<in>Basis\<close>
          using n N
          by (auto simp add: field_simps setsum_negf)
      qed
    }
    then show ?case
      apply -
      apply (rule_tac x=N in exI)
      apply safe
      unfolding dist_norm
      apply (rule B(2))
      apply auto
      done
  qed
  from this[unfolded convergent_eq_cauchy[symmetric]] guess i ..
  note i = this[THEN LIMSEQ_D]

  show ?l unfolding integrable_on_def has_integral_alt'[of f]
    apply (rule_tac x=i in exI)
    apply safe
    apply (rule as(1)[unfolded integrable_on_def])
  proof goal_cases
    case (1 e)
    then have *: "e/2 > 0" by auto
    from i[OF this] guess N .. note N =this[rule_format]
    from as(2)[OF *] guess B .. note B=conjunctD2[OF this,rule_format]
    let ?B = "max (real N) B"
    show ?case
      apply (rule_tac x="?B" in exI)
    proof safe
      show "0 < ?B"
        using B(1) by auto
      fix a b :: 'n
      assume ab: "ball 0 ?B \<subseteq> cbox a b"
      from real_arch_simple[of ?B] guess n .. note n=this
      show "norm (integral (cbox a b) (\<lambda>x. if x \<in> s then f x else 0) - i) < e"
        apply (rule norm_triangle_half_l)
        apply (rule B(2))
        defer
        apply (subst norm_minus_commute)
        apply (rule N[of n])
      proof safe
        show "N \<le> n"
          using n by auto
        fix x :: 'n
        assume x: "x \<in> ball 0 B"
        then have "x \<in> ball 0 ?B"
          by auto
        then show "x \<in> cbox a b"
          using ab by blast
        show "x \<in> ?cube n"
          using x
          unfolding mem_box mem_ball dist_norm
          apply -
        proof (rule, goal_cases)
          case (1 i)
          then show ?case
            using Basis_le_norm[of i x] \<open>i \<in> Basis\<close>
            using n
            by (auto simp add: field_simps setsum_negf)
        qed
      qed
    qed
  qed
qed

lemma integrable_altD:
  fixes f :: "'n::euclidean_space \<Rightarrow> 'a::banach"
  assumes "f integrable_on s"
  shows "\<And>a b. (\<lambda>x. if x \<in> s then f x else 0) integrable_on cbox a b"
    and "\<And>e. e > 0 \<Longrightarrow> \<exists>B>0. \<forall>a b c d. ball 0 B \<subseteq> cbox a b \<and> ball 0 B \<subseteq> cbox c d \<longrightarrow>
      norm (integral (cbox a b) (\<lambda>x. if x \<in> s then f x else 0) - integral (cbox c d)  (\<lambda>x. if x \<in> s then f x else 0)) < e"
  using assms[unfolded integrable_alt[of f]] by auto

lemma integrable_on_subcbox:
  fixes f :: "'n::euclidean_space \<Rightarrow> 'a::banach"
  assumes "f integrable_on s"
    and "cbox a b \<subseteq> s"
  shows "f integrable_on cbox a b"
  apply (rule integrable_eq)
  defer
  apply (rule integrable_altD(1)[OF assms(1)])
  using assms(2)
  apply auto
  done


subsection \<open>A straddling criterion for integrability\<close>

lemma integrable_straddle_interval:
  fixes f :: "'n::euclidean_space \<Rightarrow> real"
  assumes "\<forall>e>0. \<exists>g  h i j. (g has_integral i) (cbox a b) \<and> (h has_integral j) (cbox a b) \<and>
    norm (i - j) < e \<and> (\<forall>x\<in>cbox a b. (g x) \<le> f x \<and> f x \<le> h x)"
  shows "f integrable_on cbox a b"
proof (subst integrable_cauchy, safe, goal_cases)
  case (1 e)
  then have e: "e/3 > 0"
    by auto
  note assms[rule_format,OF this]
  then guess g h i j by (elim exE conjE) note obt = this
  from obt(1)[unfolded has_integral[of g], rule_format, OF e] guess d1 .. note d1=conjunctD2[OF this,rule_format]
  from obt(2)[unfolded has_integral[of h], rule_format, OF e] guess d2 .. note d2=conjunctD2[OF this,rule_format]
  show ?case
    apply (rule_tac x="\<lambda>x. d1 x \<inter> d2 x" in exI)
    apply (rule conjI gauge_inter d1 d2)+
    unfolding fine_inter
  proof (safe, goal_cases)
    have **: "\<And>i j g1 g2 h1 h2 f1 f2. g1 - h2 \<le> f1 - f2 \<Longrightarrow> f1 - f2 \<le> h1 - g2 \<Longrightarrow>
      \<bar>i - j\<bar> < e / 3 \<Longrightarrow> \<bar>g2 - i\<bar> < e / 3 \<Longrightarrow> \<bar>g1 - i\<bar> < e / 3 \<Longrightarrow>
      \<bar>h2 - j\<bar> < e / 3 \<Longrightarrow> \<bar>h1 - j\<bar> < e / 3 \<Longrightarrow> \<bar>f1 - f2\<bar> < e"
    using \<open>e > 0\<close> by arith
    case prems: (1 p1 p2)
    note tagged_division_ofD(2-4) note * = this[OF prems(1)] this[OF prems(4)]

    have "(\<Sum>(x, k)\<in>p1. content k *\<^sub>R f x) - (\<Sum>(x, k)\<in>p1. content k *\<^sub>R g x) \<ge> 0"
      and "0 \<le> (\<Sum>(x, k)\<in>p2. content k *\<^sub>R h x) - (\<Sum>(x, k)\<in>p2. content k *\<^sub>R f x)"
      and "(\<Sum>(x, k)\<in>p2. content k *\<^sub>R f x) - (\<Sum>(x, k)\<in>p2. content k *\<^sub>R g x) \<ge> 0"
      and "0 \<le> (\<Sum>(x, k)\<in>p1. content k *\<^sub>R h x) - (\<Sum>(x, k)\<in>p1. content k *\<^sub>R f x)"
      unfolding setsum_subtractf[symmetric]
      apply -
      apply (rule_tac[!] setsum_nonneg)
      apply safe
      unfolding real_scaleR_def right_diff_distrib[symmetric]
      apply (rule_tac[!] mult_nonneg_nonneg)
    proof -
      fix a b
      assume ab: "(a, b) \<in> p1"
      show "0 \<le> content b"
        using *(3)[OF ab]
        apply safe
        apply (rule content_pos_le)
        done
      then show "0 \<le> content b" .
      show "0 \<le> f a - g a" "0 \<le> h a - f a"
        using *(1-2)[OF ab]
        using obt(4)[rule_format,of a]
        by auto
    next
      fix a b
      assume ab: "(a, b) \<in> p2"
      show "0 \<le> content b"
        using *(6)[OF ab]
        apply safe
        apply (rule content_pos_le)
        done
      then show "0 \<le> content b" .
      show "0 \<le> f a - g a" and "0 \<le> h a - f a"
        using *(4-5)[OF ab] using obt(4)[rule_format,of a] by auto
    qed
    then show ?case
      apply -
      unfolding real_norm_def
      apply (rule **)
      defer
      defer
      unfolding real_norm_def[symmetric]
      apply (rule obt(3))
      apply (rule d1(2)[OF conjI[OF prems(4,5)]])
      apply (rule d1(2)[OF conjI[OF prems(1,2)]])
      apply (rule d2(2)[OF conjI[OF prems(4,6)]])
      apply (rule d2(2)[OF conjI[OF prems(1,3)]])
      apply auto
      done
  qed
qed

lemma integrable_straddle:
  fixes f :: "'n::euclidean_space \<Rightarrow> real"
  assumes "\<forall>e>0. \<exists>g h i j. (g has_integral i) s \<and> (h has_integral j) s \<and>
    norm (i - j) < e \<and> (\<forall>x\<in>s. g x \<le> f x \<and> f x \<le> h x)"
  shows "f integrable_on s"
proof -
  have "\<And>a b. (\<lambda>x. if x \<in> s then f x else 0) integrable_on cbox a b"
  proof (rule integrable_straddle_interval, safe, goal_cases)
    case (1 a b e)
    then have *: "e/4 > 0"
      by auto
    from assms[rule_format,OF this] guess g h i j by (elim exE conjE) note obt=this
    note obt(1)[unfolded has_integral_alt'[of g]]
    note conjunctD2[OF this, rule_format]
    note g = this(1) and this(2)[OF *]
    from this(2) guess B1 .. note B1 = conjunctD2[OF this,rule_format]
    note obt(2)[unfolded has_integral_alt'[of h]]
    note conjunctD2[OF this, rule_format]
    note h = this(1) and this(2)[OF *]
    from this(2) guess B2 .. note B2 = conjunctD2[OF this,rule_format]
    define c :: 'n where "c = (\<Sum>i\<in>Basis. min (a\<bullet>i) (- (max B1 B2)) *\<^sub>R i)"
    define d :: 'n where "d = (\<Sum>i\<in>Basis. max (b\<bullet>i) (max B1 B2) *\<^sub>R i)"
    have *: "ball 0 B1 \<subseteq> cbox c d" "ball 0 B2 \<subseteq> cbox c d"
      apply safe
      unfolding mem_ball mem_box dist_norm
      apply (rule_tac[!] ballI)
    proof goal_cases
      case (1 x i)
      then show ?case using Basis_le_norm[of i x]
        unfolding c_def d_def by auto
    next
      case (2 x i)
      then show ?case using Basis_le_norm[of i x]
        unfolding c_def d_def by auto
    qed
    have **: "\<And>ch cg ag ah::real. norm (ah - ag) \<le> norm (ch - cg) \<Longrightarrow> norm (cg - i) < e / 4 \<Longrightarrow>
      norm (ch - j) < e / 4 \<Longrightarrow> norm (ag - ah) < e"
      using obt(3)
      unfolding real_norm_def
      by arith
    show ?case
      apply (rule_tac x="\<lambda>x. if x \<in> s then g x else 0" in exI)
      apply (rule_tac x="\<lambda>x. if x \<in> s then h x else 0" in exI)
      apply (rule_tac x="integral (cbox a b) (\<lambda>x. if x \<in> s then g x else 0)" in exI)
      apply (rule_tac x="integral (cbox a b) (\<lambda>x. if x \<in> s then h x else 0)" in exI)
      apply safe
      apply (rule_tac[1-2] integrable_integral,rule g)
      apply (rule h)
      apply (rule **[OF _ B1(2)[OF *(1)] B2(2)[OF *(2)]])
    proof -
      have *: "\<And>x f g. (if x \<in> s then f x else 0) - (if x \<in> s then g x else 0) =
        (if x \<in> s then f x - g x else (0::real))"
        by auto
      note ** = abs_of_nonneg[OF integral_nonneg[OF integrable_diff, OF h g]]
      show "norm (integral (cbox a b) (\<lambda>x. if x \<in> s then h x else 0) -
          integral (cbox a b) (\<lambda>x. if x \<in> s then g x else 0)) \<le>
        norm (integral (cbox c d) (\<lambda>x. if x \<in> s then h x else 0) -
          integral (cbox c d) (\<lambda>x. if x \<in> s then g x else 0))"
        unfolding integral_diff[OF h g,symmetric] real_norm_def
        apply (subst **)
        defer
        apply (subst **)
        defer
        apply (rule has_integral_subset_le)
        defer
        apply (rule integrable_integral integrable_diff h g)+
      proof safe
        fix x
        assume "x \<in> cbox a b"
        then show "x \<in> cbox c d"
          unfolding mem_box c_def d_def
          apply -
          apply rule
          apply (erule_tac x=i in ballE)
          apply auto
          done
      qed (insert obt(4), auto)
    qed (insert obt(4), auto)
  qed
  note interv = this

  show ?thesis
    unfolding integrable_alt[of f]
    apply safe
    apply (rule interv)
  proof goal_cases
    case (1 e)
    then have *: "e/3 > 0"
      by auto
    from assms[rule_format,OF this] guess g h i j by (elim exE conjE) note obt=this
    note obt(1)[unfolded has_integral_alt'[of g]]
    note conjunctD2[OF this, rule_format]
    note g = this(1) and this(2)[OF *]
    from this(2) guess B1 .. note B1 = conjunctD2[OF this,rule_format]
    note obt(2)[unfolded has_integral_alt'[of h]]
    note conjunctD2[OF this, rule_format]
    note h = this(1) and this(2)[OF *]
    from this(2) guess B2 .. note B2 = conjunctD2[OF this,rule_format]
    show ?case
      apply (rule_tac x="max B1 B2" in exI)
      apply safe
      apply (rule max.strict_coboundedI1)
      apply (rule B1)
    proof -
      fix a b c d :: 'n
      assume as: "ball 0 (max B1 B2) \<subseteq> cbox a b" "ball 0 (max B1 B2) \<subseteq> cbox c d"
      have **: "ball 0 B1 \<subseteq> ball (0::'n) (max B1 B2)" "ball 0 B2 \<subseteq> ball (0::'n) (max B1 B2)"
        by auto
      have *: "\<And>ga gc ha hc fa fc::real.
        \<bar>ga - i\<bar> < e / 3 \<and> \<bar>gc - i\<bar> < e / 3 \<and> \<bar>ha - j\<bar> < e / 3 \<and>
        \<bar>hc - j\<bar> < e / 3 \<and> \<bar>i - j\<bar> < e / 3 \<and> ga \<le> fa \<and> fa \<le> ha \<and> gc \<le> fc \<and> fc \<le> hc \<Longrightarrow>
        \<bar>fa - fc\<bar> < e"
        by (simp add: abs_real_def split: if_split_asm)
      show "norm (integral (cbox a b) (\<lambda>x. if x \<in> s then f x else 0) - integral (cbox c d)
        (\<lambda>x. if x \<in> s then f x else 0)) < e"
        unfolding real_norm_def
        apply (rule *)
        apply safe
        unfolding real_norm_def[symmetric]
        apply (rule B1(2))
        apply (rule order_trans)
        apply (rule **)
        apply (rule as(1))
        apply (rule B1(2))
        apply (rule order_trans)
        apply (rule **)
        apply (rule as(2))
        apply (rule B2(2))
        apply (rule order_trans)
        apply (rule **)
        apply (rule as(1))
        apply (rule B2(2))
        apply (rule order_trans)
        apply (rule **)
        apply (rule as(2))
        apply (rule obt)
        apply (rule_tac[!] integral_le)
        using obt
        apply (auto intro!: h g interv)
        done
    qed
  qed
qed


subsection \<open>Adding integrals over several sets\<close>

lemma has_integral_union:
  fixes f :: "'n::euclidean_space \<Rightarrow> 'a::banach"
  assumes "(f has_integral i) s"
    and "(f has_integral j) t"
    and "negligible (s \<inter> t)"
  shows "(f has_integral (i + j)) (s \<union> t)"
proof -
  note * = has_integral_restrict_univ[symmetric, of f]
  show ?thesis
    unfolding *
    apply (rule has_integral_spike[OF assms(3)])
    defer
    apply (rule has_integral_add[OF assms(1-2)[unfolded *]])
    apply auto
    done
qed

lemma integrable_union:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b :: banach"
  assumes "negligible (A \<inter> B)" "f integrable_on A" "f integrable_on B"
  shows   "f integrable_on (A \<union> B)"
proof -
  from assms obtain y z where "(f has_integral y) A" "(f has_integral z) B"
     by (auto simp: integrable_on_def)
  from has_integral_union[OF this assms(1)] show ?thesis by (auto simp: integrable_on_def)
qed

lemma integrable_union':
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b :: banach"
  assumes "f integrable_on A" "f integrable_on B" "negligible (A \<inter> B)" "C = A \<union> B"
  shows   "f integrable_on C"
  using integrable_union[of A B f] assms by simp

lemma has_integral_unions:
  fixes f :: "'n::euclidean_space \<Rightarrow> 'a::banach"
  assumes "finite t"
    and "\<forall>s\<in>t. (f has_integral (i s)) s"
    and "\<forall>s\<in>t. \<forall>s'\<in>t. s \<noteq> s' \<longrightarrow> negligible (s \<inter> s')"
  shows "(f has_integral (setsum i t)) (\<Union>t)"
proof -
  note * = has_integral_restrict_univ[symmetric, of f]
  have **: "negligible (\<Union>((\<lambda>(a,b). a \<inter> b) ` {(a,b). a \<in> t \<and> b \<in> {y. y \<in> t \<and> a \<noteq> y}}))"
    apply (rule negligible_Union)
    apply (rule finite_imageI)
    apply (rule finite_subset[of _ "t \<times> t"])
    defer
    apply (rule finite_cartesian_product[OF assms(1,1)])
    using assms(3)
    apply auto
    done
  note assms(2)[unfolded *]
  note has_integral_setsum[OF assms(1) this]
  then show ?thesis
    unfolding *
    apply -
    apply (rule has_integral_spike[OF **])
    defer
    apply assumption
    apply safe
  proof goal_cases
    case prems: (1 x)
    then show ?case
    proof (cases "x \<in> \<Union>t")
      case True
      then guess s unfolding Union_iff .. note s=this
      then have *: "\<forall>b\<in>t. x \<in> b \<longleftrightarrow> b = s"
        using prems(3) by blast
      show ?thesis
        unfolding if_P[OF True]
        apply (rule trans)
        defer
        apply (rule setsum.cong)
        apply (rule refl)
        apply (subst *)
        apply assumption
        apply (rule refl)
        unfolding setsum.delta[OF assms(1)]
        using s
        apply auto
        done
    qed auto
  qed
qed


text \<open>In particular adding integrals over a division, maybe not of an interval.\<close>

lemma has_integral_combine_division:
  fixes f :: "'n::euclidean_space \<Rightarrow> 'a::banach"
  assumes "d division_of s"
    and "\<forall>k\<in>d. (f has_integral (i k)) k"
  shows "(f has_integral (setsum i d)) s"
proof -
  note d = division_ofD[OF assms(1)]
  show ?thesis
    unfolding d(6)[symmetric]
    apply (rule has_integral_unions)
    apply (rule d assms)+
    apply rule
    apply rule
    apply rule
  proof goal_cases
    case prems: (1 s s')
    from d(4)[OF this(1)] d(4)[OF this(2)] guess a c b d by (elim exE) note obt=this
    from d(5)[OF prems] show ?case
      unfolding obt interior_cbox
      apply -
      apply (rule negligible_subset[of "(cbox a b-box a b) \<union> (cbox c d-box c d)"])
      apply (rule negligible_Un negligible_frontier_interval)+
      apply auto
      done
  qed
qed

lemma integral_combine_division_bottomup:
  fixes f :: "'n::euclidean_space \<Rightarrow> 'a::banach"
  assumes "d division_of s"
    and "\<forall>k\<in>d. f integrable_on k"
  shows "integral s f = setsum (\<lambda>i. integral i f) d"
  apply (rule integral_unique)
  apply (rule has_integral_combine_division[OF assms(1)])
  using assms(2)
  unfolding has_integral_integral
  apply assumption
  done

lemma has_integral_combine_division_topdown:
  fixes f :: "'n::euclidean_space \<Rightarrow> 'a::banach"
  assumes "f integrable_on s"
    and "d division_of k"
    and "k \<subseteq> s"
  shows "(f has_integral (setsum (\<lambda>i. integral i f) d)) k"
  apply (rule has_integral_combine_division[OF assms(2)])
  apply safe
  unfolding has_integral_integral[symmetric]
proof goal_cases
  case (1 k)
  from division_ofD(2,4)[OF assms(2) this]
  show ?case
    apply safe
    apply (rule integrable_on_subcbox)
    apply (rule assms)
    using assms(3)
    apply auto
    done
qed

lemma integral_combine_division_topdown:
  fixes f :: "'n::euclidean_space \<Rightarrow> 'a::banach"
  assumes "f integrable_on s"
    and "d division_of s"
  shows "integral s f = setsum (\<lambda>i. integral i f) d"
  apply (rule integral_unique)
  apply (rule has_integral_combine_division_topdown)
  using assms
  apply auto
  done

lemma integrable_combine_division:
  fixes f :: "'n::euclidean_space \<Rightarrow> 'a::banach"
  assumes "d division_of s"
    and "\<forall>i\<in>d. f integrable_on i"
  shows "f integrable_on s"
  using assms(2)
  unfolding integrable_on_def
  by (metis has_integral_combine_division[OF assms(1)])

lemma integrable_on_subdivision:
  fixes f :: "'n::euclidean_space \<Rightarrow> 'a::banach"
  assumes "d division_of i"
    and "f integrable_on s"
    and "i \<subseteq> s"
  shows "f integrable_on i"
  apply (rule integrable_combine_division assms)+
  apply safe
proof goal_cases
  case 1
  note division_ofD(2,4)[OF assms(1) this]
  then show ?case
    apply safe
    apply (rule integrable_on_subcbox[OF assms(2)])
    using assms(3)
    apply auto
    done
qed


subsection \<open>Also tagged divisions\<close>

lemma has_integral_combine_tagged_division:
  fixes f :: "'n::euclidean_space \<Rightarrow> 'a::banach"
  assumes "p tagged_division_of s"
    and "\<forall>(x,k) \<in> p. (f has_integral (i k)) k"
  shows "(f has_integral (setsum (\<lambda>(x,k). i k) p)) s"
proof -
  have *: "(f has_integral (setsum (\<lambda>k. integral k f) (snd ` p))) s"
    apply (rule has_integral_combine_division)
    apply (rule division_of_tagged_division[OF assms(1)])
    using assms(2)
    unfolding has_integral_integral[symmetric]
    apply safe
    apply auto
    done
  then show ?thesis
    apply -
    apply (rule subst[where P="\<lambda>i. (f has_integral i) s"])
    defer
    apply assumption
    apply (rule trans[of _ "setsum (\<lambda>(x,k). integral k f) p"])
    apply (subst eq_commute)
    apply (rule setsum.over_tagged_division_lemma[OF assms(1)])
    apply (rule integral_null)
    apply assumption
    apply (rule setsum.cong)
    using assms(2)
    apply auto
    done
qed

lemma integral_combine_tagged_division_bottomup:
  fixes f :: "'n::euclidean_space \<Rightarrow> 'a::banach"
  assumes "p tagged_division_of (cbox a b)"
    and "\<forall>(x,k)\<in>p. f integrable_on k"
  shows "integral (cbox a b) f = setsum (\<lambda>(x,k). integral k f) p"
  apply (rule integral_unique)
  apply (rule has_integral_combine_tagged_division[OF assms(1)])
  using assms(2)
  apply auto
  done

lemma has_integral_combine_tagged_division_topdown:
  fixes f :: "'n::euclidean_space \<Rightarrow> 'a::banach"
  assumes "f integrable_on cbox a b"
    and "p tagged_division_of (cbox a b)"
  shows "(f has_integral (setsum (\<lambda>(x,k). integral k f) p)) (cbox a b)"
  apply (rule has_integral_combine_tagged_division[OF assms(2)])
  apply safe
proof goal_cases
  case 1
  note tagged_division_ofD(3-4)[OF assms(2) this]
  then show ?case
    using integrable_subinterval[OF assms(1)] by blast
qed

lemma integral_combine_tagged_division_topdown:
  fixes f :: "'n::euclidean_space \<Rightarrow> 'a::banach"
  assumes "f integrable_on cbox a b"
    and "p tagged_division_of (cbox a b)"
  shows "integral (cbox a b) f = setsum (\<lambda>(x,k). integral k f) p"
  apply (rule integral_unique)
  apply (rule has_integral_combine_tagged_division_topdown)
  using assms
  apply auto
  done


subsection \<open>Henstock's lemma\<close>

lemma henstock_lemma_part1:
  fixes f :: "'n::euclidean_space \<Rightarrow> 'a::banach"
  assumes "f integrable_on cbox a b"
    and "e > 0"
    and "gauge d"
    and "(\<forall>p. p tagged_division_of (cbox a b) \<and> d fine p \<longrightarrow>
      norm (setsum (\<lambda>(x,k). content k *\<^sub>R f x) p - integral(cbox a b) f) < e)"
    and p: "p tagged_partial_division_of (cbox a b)" "d fine p"
  shows "norm (setsum (\<lambda>(x,k). content k *\<^sub>R f x - integral k f) p) \<le> e"
  (is "?x \<le> e")
proof -
  { presume "\<And>k. 0<k \<Longrightarrow> ?x \<le> e + k" then show ?thesis by (blast intro: field_le_epsilon) }
  fix k :: real
  assume k: "k > 0"
  note p' = tagged_partial_division_ofD[OF p(1)]
  have "\<Union>(snd ` p) \<subseteq> cbox a b"
    using p'(3) by fastforce
  note partial_division_of_tagged_division[OF p(1)] this
  from partial_division_extend_interval[OF this] guess q . note q=this and q' = division_ofD[OF this(2)]
  define r where "r = q - snd ` p"
  have "snd ` p \<inter> r = {}"
    unfolding r_def by auto
  have r: "finite r"
    using q' unfolding r_def by auto

  have "\<forall>i\<in>r. \<exists>p. p tagged_division_of i \<and> d fine p \<and>
    norm (setsum (\<lambda>(x,j). content j *\<^sub>R f x) p - integral i f) < k / (real (card r) + 1)"
    apply safe
  proof goal_cases
    case (1 i)
    then have i: "i \<in> q"
      unfolding r_def by auto
    from q'(4)[OF this] guess u v by (elim exE) note uv=this
    have *: "k / (real (card r) + 1) > 0" using k by simp
    have "f integrable_on cbox u v"
      apply (rule integrable_subinterval[OF assms(1)])
      using q'(2)[OF i]
      unfolding uv
      apply auto
      done
    note integrable_integral[OF this, unfolded has_integral[of f]]
    from this[rule_format,OF *] guess dd .. note dd=conjunctD2[OF this,rule_format]
    note gauge_inter[OF \<open>gauge d\<close> dd(1)]
    from fine_division_exists[OF this,of u v] guess qq .
    then show ?case
      apply (rule_tac x=qq in exI)
      using dd(2)[of qq]
      unfolding fine_inter uv
      apply auto
      done
  qed
  from bchoice[OF this] guess qq .. note qq=this[rule_format]

  let ?p = "p \<union> \<Union>(qq ` r)"
  have "norm ((\<Sum>(x, k)\<in>?p. content k *\<^sub>R f x) - integral (cbox a b) f) < e"
    apply (rule assms(4)[rule_format])
  proof
    show "d fine ?p"
      apply (rule fine_union)
      apply (rule p)
      apply (rule fine_unions)
      using qq
      apply auto
      done
    note * = tagged_partial_division_of_union_self[OF p(1)]
    have "p \<union> \<Union>(qq ` r) tagged_division_of \<Union>(snd ` p) \<union> \<Union>r"
      using r
    proof (rule tagged_division_union[OF * tagged_division_unions], goal_cases)
      case 1
      then show ?case
        using qq by auto
    next
      case 2
      then show ?case
        apply rule
        apply rule
        apply rule
        apply(rule q'(5))
        unfolding r_def
        apply auto
        done
    next
      case 3
      then show ?case
        apply (rule inter_interior_unions_intervals)
        apply fact
        apply rule
        apply rule
        apply (rule q')
        defer
        apply rule
        apply (subst Int_commute)
        apply (rule inter_interior_unions_intervals)
        apply (rule finite_imageI)
        apply (rule p')
        apply rule
        defer
        apply rule
        apply (rule q')
        using q(1) p'
        unfolding r_def
        apply auto
        done
    qed
    moreover have "\<Union>(snd ` p) \<union> \<Union>r = cbox a b" and "{qq i |i. i \<in> r} = qq ` r"
      unfolding Union_Un_distrib[symmetric] r_def
      using q
      by auto
    ultimately show "?p tagged_division_of (cbox a b)"
      by fastforce
  qed

  then have "norm ((\<Sum>(x, k)\<in>p. content k *\<^sub>R f x) + (\<Sum>(x, k)\<in>\<Union>(qq ` r). content k *\<^sub>R f x) -
    integral (cbox a b) f) < e"
    apply (subst setsum.union_inter_neutral[symmetric])
    apply (rule p')
    prefer 3
    apply assumption
    apply rule
    apply (rule r)
    apply safe
    apply (drule qq)
  proof -
    fix x l k
    assume as: "(x, l) \<in> p" "(x, l) \<in> qq k" "k \<in> r"
    note qq[OF this(3)]
    note tagged_division_ofD(3,4)[OF conjunct1[OF this] as(2)]
    from this(2) guess u v by (elim exE) note uv=this
    have "l\<in>snd ` p" unfolding image_iff apply(rule_tac x="(x,l)" in bexI) using as by auto
    then have "l \<in> q" "k \<in> q" "l \<noteq> k"
      using as(1,3) q(1) unfolding r_def by auto
    note q'(5)[OF this]
    then have "interior l = {}"
      using interior_mono[OF \<open>l \<subseteq> k\<close>] by blast
    then show "content l *\<^sub>R f x = 0"
      unfolding uv content_eq_0_interior[symmetric] by auto
  qed auto

  then have "norm ((\<Sum>(x, k)\<in>p. content k *\<^sub>R f x) + setsum (setsum (\<lambda>(x, k). content k *\<^sub>R f x))
    (qq ` r) - integral (cbox a b) f) < e"
    apply (subst (asm) setsum.Union_comp)
    prefer 2
    unfolding split_paired_all split_conv image_iff
    apply (erule bexE)+
  proof -
    fix x m k l T1 T2
    assume "(x, m) \<in> T1" "(x, m) \<in> T2" "T1 \<noteq> T2" "k \<in> r" "l \<in> r" "T1 = qq k" "T2 = qq l"
    note as = this(1-5)[unfolded this(6-)]
    note kl = tagged_division_ofD(3,4)[OF qq[THEN conjunct1]]
    from this(2)[OF as(4,1)] guess u v by (elim exE) note uv=this
    have *: "interior (k \<inter> l) = {}"
      by (metis DiffE \<open>T1 = qq k\<close> \<open>T1 \<noteq> T2\<close> \<open>T2 = qq l\<close> as(4) as(5) interior_Int q'(5) r_def)
    have "interior m = {}"
      unfolding subset_empty[symmetric]
      unfolding *[symmetric]
      apply (rule interior_mono)
      using kl(1)[OF as(4,1)] kl(1)[OF as(5,2)]
      apply auto
      done
    then show "content m *\<^sub>R f x = 0"
      unfolding uv content_eq_0_interior[symmetric]
      by auto
  qed (insert qq, auto)

  then have **: "norm ((\<Sum>(x, k)\<in>p. content k *\<^sub>R f x) + setsum (setsum (\<lambda>(x, k). content k *\<^sub>R f x) \<circ> qq) r -
    integral (cbox a b) f) < e"
    apply (subst (asm) setsum.reindex_nontrivial)
    apply fact
    apply (rule setsum.neutral)
    apply rule
    unfolding split_paired_all split_conv
    defer
    apply assumption
  proof -
    fix k l x m
    assume as: "k \<in> r" "l \<in> r" "k \<noteq> l" "qq k = qq l" "(x, m) \<in> qq k"
    note tagged_division_ofD(6)[OF qq[THEN conjunct1]]
    from this[OF as(1)] this[OF as(2)] show "content m *\<^sub>R f x = 0"
      using as(3) unfolding as by auto
  qed

  have *: "norm (cp - ip) \<le> e + k"
    if "norm ((cp + cr) - i) < e"
    and "norm (cr - ir) < k"
    and "ip + ir = i"
    for ir ip i cr cp
  proof -
    from that show ?thesis
      using norm_triangle_le[of "cp + cr - i" "- (cr - ir)"]
      unfolding that(3)[symmetric] norm_minus_cancel
      by (auto simp add: algebra_simps)
  qed

  have "?x =  norm ((\<Sum>(x, k)\<in>p. content k *\<^sub>R f x) - (\<Sum>(x, k)\<in>p. integral k f))"
    unfolding split_def setsum_subtractf ..
  also have "\<dots> \<le> e + k"
    apply (rule *[OF **, where ir1="setsum (\<lambda>k. integral k f) r"])
  proof goal_cases
    case 1
    have *: "k * real (card r) / (1 + real (card r)) < k"
      using k by (auto simp add: field_simps)
    show ?case
      apply (rule le_less_trans[of _ "setsum (\<lambda>x. k / (real (card r) + 1)) r"])
      unfolding setsum_subtractf[symmetric]
      apply (rule setsum_norm_le)
      apply rule
      apply (drule qq)
      defer
      unfolding divide_inverse setsum_distrib_right[symmetric]
      unfolding divide_inverse[symmetric]
      using * apply (auto simp add: field_simps)
      done
  next
    case 2
    have *: "(\<Sum>(x, k)\<in>p. integral k f) = (\<Sum>k\<in>snd ` p. integral k f)"
      apply (subst setsum.reindex_nontrivial)
      apply fact
      unfolding split_paired_all snd_conv split_def o_def
    proof -
      fix x l y m
      assume as: "(x, l) \<in> p" "(y, m) \<in> p" "(x, l) \<noteq> (y, m)" "l = m"
      from p'(4)[OF as(1)] guess u v by (elim exE) note uv=this
      show "integral l f = 0"
        unfolding uv
        apply (rule integral_unique)
        apply (rule has_integral_null)
        unfolding content_eq_0_interior
        using p'(5)[OF as(1-3)]
        unfolding uv as(4)[symmetric]
        apply auto
        done
    qed auto
    from q(1) have **: "snd ` p \<union> q = q" by auto
    show ?case
      unfolding integral_combine_division_topdown[OF assms(1) q(2)] * r_def
      using ** q'(1) p'(1) setsum.union_disjoint [of "snd ` p" "q - snd ` p" "\<lambda>k. integral k f", symmetric]
        by simp
  qed
  finally show "?x \<le> e + k" .
qed

lemma henstock_lemma_part2:
  fixes f :: "'m::euclidean_space \<Rightarrow> 'n::euclidean_space"
  assumes "f integrable_on cbox a b"
    and "e > 0"
    and "gauge d"
    and "\<forall>p. p tagged_division_of (cbox a b) \<and> d fine p \<longrightarrow>
      norm (setsum (\<lambda>(x,k). content k *\<^sub>R f x) p - integral (cbox a b) f) < e"
    and "p tagged_partial_division_of (cbox a b)"
    and "d fine p"
  shows "setsum (\<lambda>(x,k). norm (content k *\<^sub>R f x - integral k f)) p \<le> 2 * real (DIM('n)) * e"
  unfolding split_def
  apply (rule setsum_norm_allsubsets_bound)
  defer
  apply (rule henstock_lemma_part1[unfolded split_def,OF assms(1-3)])
  apply safe
  apply (rule assms[rule_format,unfolded split_def])
  defer
  apply (rule tagged_partial_division_subset)
  apply (rule assms)
  apply assumption
  apply (rule fine_subset)
  apply assumption
  apply (rule assms)
  using assms(5)
  apply auto
  done

lemma henstock_lemma:
  fixes f :: "'m::euclidean_space \<Rightarrow> 'n::euclidean_space"
  assumes "f integrable_on cbox a b"
    and "e > 0"
  obtains d where "gauge d"
    and "\<forall>p. p tagged_partial_division_of (cbox a b) \<and> d fine p \<longrightarrow>
      setsum (\<lambda>(x,k). norm(content k *\<^sub>R f x - integral k f)) p < e"
proof -
  have *: "e / (2 * (real DIM('n) + 1)) > 0" using assms(2) by simp
  from integrable_integral[OF assms(1),unfolded has_integral[of f],rule_format,OF this]
  guess d .. note d = conjunctD2[OF this]
  show thesis
    apply (rule that)
    apply (rule d)
  proof (safe, goal_cases)
    case (1 p)
    note * = henstock_lemma_part2[OF assms(1) * d this]
    show ?case
      apply (rule le_less_trans[OF *])
      using \<open>e > 0\<close>
      apply (auto simp add: field_simps)
      done
  qed
qed


subsection \<open>Geometric progression\<close>

text \<open>FIXME: Should one or more of these theorems be moved to
  \<^file>\<open>~~/src/HOL/Set_Interval.thy\<close>, alongside \<open>geometric_sum\<close>?\<close>

lemma sum_gp_basic:
  fixes x :: "'a::ring_1"
  shows "(1 - x) * setsum (\<lambda>i. x^i) {0 .. n} = (1 - x^(Suc n))"
proof -
  define y where "y = 1 - x"
  have "y * (\<Sum>i=0..n. (1 - y) ^ i) = 1 - (1 - y) ^ Suc n"
    by (induct n) (simp_all add: algebra_simps)
  then show ?thesis
    unfolding y_def by simp
qed

lemma sum_gp_multiplied:
  assumes mn: "m \<le> n"
  shows "((1::'a::{field}) - x) * setsum (op ^ x) {m..n} = x^m - x^ Suc n"
  (is "?lhs = ?rhs")
proof -
  let ?S = "{0..(n - m)}"
  from mn have mn': "n - m \<ge> 0"
    by arith
  let ?f = "op + m"
  have i: "inj_on ?f ?S"
    unfolding inj_on_def by auto
  have f: "?f ` ?S = {m..n}"
    using mn
    apply (auto simp add: image_iff Bex_def)
    apply presburger
    done
  have th: "op ^ x \<circ> op + m = (\<lambda>i. x^m * x^i)"
    by (rule ext) (simp add: power_add power_mult)
  from setsum.reindex[OF i, of "op ^ x", unfolded f th setsum_distrib_left[symmetric]]
  have "?lhs = x^m * ((1 - x) * setsum (op ^ x) {0..n - m})"
    by simp
  then show ?thesis
    unfolding sum_gp_basic
    using mn
    by (simp add: field_simps power_add[symmetric])
qed

lemma sum_gp:
  "setsum (op ^ (x::'a::{field})) {m .. n} =
    (if n < m then 0
     else if x = 1 then of_nat ((n + 1) - m)
     else (x^ m - x^ (Suc n)) / (1 - x))"
proof -
  {
    assume nm: "n < m"
    then have ?thesis by simp
  }
  moreover
  {
    assume "\<not> n < m"
    then have nm: "m \<le> n"
      by arith
    {
      assume x: "x = 1"
      then have ?thesis
        by simp
    }
    moreover
    {
      assume x: "x \<noteq> 1"
      then have nz: "1 - x \<noteq> 0"
        by simp
      from sum_gp_multiplied[OF nm, of x] nz have ?thesis
        by (simp add: field_simps)
    }
    ultimately have ?thesis by blast
  }
  ultimately show ?thesis by blast
qed

lemma sum_gp_offset:
  "setsum (op ^ (x::'a::{field})) {m .. m+n} =
    (if x = 1 then of_nat n + 1 else x^m * (1 - x^Suc n) / (1 - x))"
  unfolding sum_gp[of x m "m + n"] power_Suc
  by (simp add: field_simps power_add)


subsection \<open>Monotone convergence (bounded interval first)\<close>

lemma monotone_convergence_interval:
  fixes f :: "nat \<Rightarrow> 'n::euclidean_space \<Rightarrow> real"
  assumes "\<forall>k. (f k) integrable_on cbox a b"
    and "\<forall>k. \<forall>x\<in>cbox a b.(f k x) \<le> f (Suc k) x"
    and "\<forall>x\<in>cbox a b. ((\<lambda>k. f k x) \<longlongrightarrow> g x) sequentially"
    and "bounded {integral (cbox a b) (f k) | k . k \<in> UNIV}"
  shows "g integrable_on cbox a b \<and> ((\<lambda>k. integral (cbox a b) (f k)) \<longlongrightarrow> integral (cbox a b) g) sequentially"
proof (cases "content (cbox a b) = 0")
  case True
  show ?thesis
    using integrable_on_null[OF True]
    unfolding integral_null[OF True]
    using tendsto_const
    by auto
next
  case False
  have fg: "\<forall>x\<in>cbox a b. \<forall>k. (f k x) \<bullet> 1 \<le> (g x) \<bullet> 1"
  proof safe
    fix x k
    assume x: "x \<in> cbox a b"
    note * = Lim_component_ge[OF assms(3)[rule_format, OF x] trivial_limit_sequentially]
    show "f k x \<bullet> 1 \<le> g x \<bullet> 1"
      apply (rule *)
      unfolding eventually_sequentially
      apply (rule_tac x=k in exI)
      apply -
      apply (rule transitive_stepwise_le)
      using assms(2)[rule_format, OF x]
      apply auto
      done
  qed
  have "\<exists>i. ((\<lambda>k. integral (cbox a b) (f k)) \<longlongrightarrow> i) sequentially"
    apply (rule bounded_increasing_convergent)
    defer
    apply rule
    apply (rule integral_le)
    apply safe
    apply (rule assms(1-2)[rule_format])+
    using assms(4)
    apply auto
    done
  then guess i .. note i=this
  have i': "\<And>k. (integral(cbox a b) (f k)) \<le> i\<bullet>1"
    apply (rule Lim_component_ge)
    apply (rule i)
    apply (rule trivial_limit_sequentially)
    unfolding eventually_sequentially
    apply (rule_tac x=k in exI)
    apply (rule transitive_stepwise_le)
    prefer 3
    unfolding inner_simps real_inner_1_right
    apply (rule integral_le)
    apply (rule assms(1-2)[rule_format])+
    using assms(2)
    apply auto
    done

  have "(g has_integral i) (cbox a b)"
    unfolding has_integral
  proof (safe, goal_cases)
    case e: (1 e)
    then have "\<forall>k. (\<exists>d. gauge d \<and> (\<forall>p. p tagged_division_of (cbox a b) \<and> d fine p \<longrightarrow>
      norm ((\<Sum>(x, ka)\<in>p. content ka *\<^sub>R f k x) - integral (cbox a b) (f k)) < e / 2 ^ (k + 2)))"
      apply -
      apply rule
      apply (rule assms(1)[unfolded has_integral_integral has_integral,rule_format])
      apply auto
      done
    from choice[OF this] guess c .. note c=conjunctD2[OF this[rule_format],rule_format]

    have "\<exists>r. \<forall>k\<ge>r. 0 \<le> i\<bullet>1 - (integral (cbox a b) (f k)) \<and> i\<bullet>1 - (integral (cbox a b) (f k)) < e / 4"
    proof -
      have "e/4 > 0"
        using e by auto
      from LIMSEQ_D [OF i this] guess r ..
      then show ?thesis
        apply (rule_tac x=r in exI)
        apply rule
        apply (erule_tac x=k in allE)
        subgoal for k using i'[of k] by auto
        done
    qed
    then guess r .. note r=conjunctD2[OF this[rule_format]]

    have "\<forall>x\<in>cbox a b. \<exists>n\<ge>r. \<forall>k\<ge>n. 0 \<le> (g x)\<bullet>1 - (f k x)\<bullet>1 \<and>
      (g x)\<bullet>1 - (f k x)\<bullet>1 < e / (4 * content(cbox a b))"
    proof (rule, goal_cases)
      case prems: (1 x)
      have "e / (4 * content (cbox a b)) > 0"
        using \<open>e>0\<close> False content_pos_le[of a b] by (simp add: less_le)
      from assms(3)[rule_format, OF prems, THEN LIMSEQ_D, OF this]
      guess n .. note n=this
      then show ?case
        apply (rule_tac x="n + r" in exI)
        apply safe
        apply (erule_tac[2-3] x=k in allE)
        unfolding dist_real_def
        using fg[rule_format, OF prems]
        apply (auto simp add: field_simps)
        done
    qed
    from bchoice[OF this] guess m .. note m=conjunctD2[OF this[rule_format],rule_format]
    define d where "d x = c (m x) x" for x
    show ?case
      apply (rule_tac x=d in exI)
    proof safe
      show "gauge d"
        using c(1) unfolding gauge_def d_def by auto
    next
      fix p
      assume p: "p tagged_division_of (cbox a b)" "d fine p"
      note p'=tagged_division_ofD[OF p(1)]
      have "\<exists>a. \<forall>x\<in>p. m (fst x) \<le> a"
        by (metis finite_imageI finite_nat_set_iff_bounded_le p'(1) rev_image_eqI)
      then guess s .. note s=this
      have *: "\<forall>a b c d. norm(a - b) \<le> e / 4 \<and> norm(b - c) < e / 2 \<and>
        norm (c - d) < e / 4 \<longrightarrow> norm (a - d) < e"
      proof (safe, goal_cases)
        case (1 a b c d)
        then show ?case
          using norm_triangle_lt[of "a - b" "b - c" "3* e/4"]
            norm_triangle_lt[of "a - b + (b - c)" "c - d" e]
          unfolding norm_minus_cancel
          by (auto simp add: algebra_simps)
      qed
      show "norm ((\<Sum>(x, k)\<in>p. content k *\<^sub>R g x) - i) < e"
        apply (rule *[rule_format,where
          b="\<Sum>(x, k)\<in>p. content k *\<^sub>R f (m x) x" and c="\<Sum>(x, k)\<in>p. integral k (f (m x))"])
      proof (safe, goal_cases)
        case 1
        show ?case
          apply (rule order_trans[of _ "\<Sum>(x, k)\<in>p. content k * (e / (4 * content (cbox a b)))"])
          unfolding setsum_subtractf[symmetric]
          apply (rule order_trans)
          apply (rule norm_setsum)
          apply (rule setsum_mono)
          unfolding split_paired_all split_conv
          unfolding split_def setsum_distrib_right[symmetric] scaleR_diff_right[symmetric]
          unfolding additive_content_tagged_division[OF p(1), unfolded split_def]
        proof -
          fix x k
          assume xk: "(x, k) \<in> p"
          then have x: "x \<in> cbox a b"
            using p'(2-3)[OF xk] by auto
          from p'(4)[OF xk] guess u v by (elim exE) note uv=this
          show "norm (content k *\<^sub>R (g x - f (m x) x)) \<le> content k * (e / (4 * content (cbox a b)))"
            unfolding norm_scaleR uv
            unfolding abs_of_nonneg[OF content_pos_le]
            apply (rule mult_left_mono)
            using m(2)[OF x,of "m x"]
            apply auto
            done
        qed (insert False, auto)

      next
        case 2
        show ?case
          apply (rule le_less_trans[of _ "norm (\<Sum>j = 0..s.
            \<Sum>(x, k)\<in>{xk\<in>p. m (fst xk) = j}. content k *\<^sub>R f (m x) x - integral k (f (m x)))"])
          apply (subst setsum_group)
          apply fact
          apply (rule finite_atLeastAtMost)
          defer
          apply (subst split_def)+
          unfolding setsum_subtractf
          apply rule
        proof -
          show "norm (\<Sum>j = 0..s. \<Sum>(x, k)\<in>{xk \<in> p.
            m (fst xk) = j}. content k *\<^sub>R f (m x) x - integral k (f (m x))) < e / 2"
            apply (rule le_less_trans[of _ "setsum (\<lambda>i. e / 2^(i+2)) {0..s}"])
            apply (rule setsum_norm_le)
          proof
            show "(\<Sum>i = 0..s. e / 2 ^ (i + 2)) < e / 2"
              unfolding power_add divide_inverse inverse_mult_distrib
              unfolding setsum_distrib_left[symmetric] setsum_distrib_right[symmetric]
              unfolding power_inverse [symmetric] sum_gp
              apply(rule mult_strict_left_mono[OF _ e])
              unfolding power2_eq_square
              apply auto
              done
            fix t
            assume "t \<in> {0..s}"
            show "norm (\<Sum>(x, k)\<in>{xk \<in> p. m (fst xk) = t}. content k *\<^sub>R f (m x) x -
              integral k (f (m x))) \<le> e / 2 ^ (t + 2)"
              apply (rule order_trans
                [of _ "norm (setsum (\<lambda>(x,k). content k *\<^sub>R f t x - integral k (f t)) {xk \<in> p. m (fst xk) = t})"])
              apply (rule eq_refl)
              apply (rule arg_cong[where f=norm])
              apply (rule setsum.cong)
              apply (rule refl)
              defer
              apply (rule henstock_lemma_part1)
              apply (rule assms(1)[rule_format])
              apply (simp add: e)
              apply safe
              apply (rule c)+
              apply rule
              apply assumption+
              apply (rule tagged_partial_division_subset[of p])
              apply (rule p(1)[unfolded tagged_division_of_def,THEN conjunct1])
              defer
              unfolding fine_def
              apply safe
              apply (drule p(2)[unfolded fine_def,rule_format])
              unfolding d_def
              apply auto
              done
          qed
        qed (insert s, auto)
      next
        case 3
        note comb = integral_combine_tagged_division_topdown[OF assms(1)[rule_format] p(1)]
        have *: "\<And>sr sx ss ks kr::real. kr = sr \<longrightarrow> ks = ss \<longrightarrow>
          ks \<le> i \<and> sr \<le> sx \<and> sx \<le> ss \<and> 0 \<le> i\<bullet>1 - kr\<bullet>1 \<and> i\<bullet>1 - kr\<bullet>1 < e/4 \<longrightarrow> \<bar>sx - i\<bar> < e/4"
          by auto
        show ?case
          unfolding real_norm_def
          apply (rule *[rule_format])
          apply safe
          apply (rule comb[of r])
          apply (rule comb[of s])
          apply (rule i'[unfolded real_inner_1_right])
          apply (rule_tac[1-2] setsum_mono)
          unfolding split_paired_all split_conv
          apply (rule_tac[1-2] integral_le[OF ])
        proof safe
          show "0 \<le> i\<bullet>1 - (integral (cbox a b) (f r))\<bullet>1"
            using r(1) by auto
          show "i\<bullet>1 - (integral (cbox a b) (f r))\<bullet>1 < e / 4"
            using r(2) by auto
          fix x k
          assume xk: "(x, k) \<in> p"
          from p'(4)[OF this] guess u v by (elim exE) note uv=this
          show "f r integrable_on k"
            and "f s integrable_on k"
            and "f (m x) integrable_on k"
            and "f (m x) integrable_on k"
            unfolding uv
            apply (rule_tac[!] integrable_on_subcbox[OF assms(1)[rule_format]])
            using p'(3)[OF xk]
            unfolding uv
            apply auto
            done
          fix y
          assume "y \<in> k"
          then have "y \<in> cbox a b"
            using p'(3)[OF xk] by auto
          then have *: "\<And>m. \<forall>n\<ge>m. f m y \<le> f n y"
            apply -
            apply (rule transitive_stepwise_le)
            using assms(2)
            apply auto
            done
          show "f r y \<le> f (m x) y" and "f (m x) y \<le> f s y"
            apply (rule_tac[!] *[rule_format])
            using s[rule_format,OF xk] m(1)[of x] p'(2-3)[OF xk]
            apply auto
            done
        qed
      qed
    qed
  qed note * = this

  have "integral (cbox a b) g = i"
    by (rule integral_unique) (rule *)
  then show ?thesis
    using i * by auto
qed

lemma monotone_convergence_increasing:
  fixes f :: "nat \<Rightarrow> 'n::euclidean_space \<Rightarrow> real"
  assumes "\<forall>k. (f k) integrable_on s"
    and "\<forall>k. \<forall>x\<in>s. (f k x) \<le> (f (Suc k) x)"
    and "\<forall>x\<in>s. ((\<lambda>k. f k x) \<longlongrightarrow> g x) sequentially"
    and "bounded {integral s (f k)| k. True}"
  shows "g integrable_on s \<and> ((\<lambda>k. integral s (f k)) \<longlongrightarrow> integral s g) sequentially"
proof -
  have lem: "g integrable_on s \<and> ((\<lambda>k. integral s (f k)) \<longlongrightarrow> integral s g) sequentially"
    if "\<forall>k. \<forall>x\<in>s. 0 \<le> f k x"
    and "\<forall>k. (f k) integrable_on s"
    and "\<forall>k. \<forall>x\<in>s. f k x \<le> f (Suc k) x"
    and "\<forall>x\<in>s. ((\<lambda>k. f k x) \<longlongrightarrow> g x) sequentially"
    and "bounded {integral s (f k)| k. True}"
    for f :: "nat \<Rightarrow> 'n::euclidean_space \<Rightarrow> real" and g s
  proof -
    note assms=that[rule_format]
    have "\<forall>x\<in>s. \<forall>k. (f k x)\<bullet>1 \<le> (g x)\<bullet>1"
      apply safe
      apply (rule Lim_component_ge)
      apply (rule that(4)[rule_format])
      apply assumption
      apply (rule trivial_limit_sequentially)
      unfolding eventually_sequentially
      apply (rule_tac x=k in exI)
      apply (rule transitive_stepwise_le)
      using that(3)
      apply auto
      done
    note fg=this[rule_format]

    have "\<exists>i. ((\<lambda>k. integral s (f k)) \<longlongrightarrow> i) sequentially"
      apply (rule bounded_increasing_convergent)
      apply (rule that(5))
      apply rule
      apply (rule integral_le)
      apply (rule that(2)[rule_format])+
      using that(3)
      apply auto
      done
    then guess i .. note i=this
    have "\<And>k. \<forall>x\<in>s. \<forall>n\<ge>k. f k x \<le> f n x"
      apply rule
      apply (rule transitive_stepwise_le)
      using that(3)
      apply auto
      done
    then have i': "\<forall>k. (integral s (f k))\<bullet>1 \<le> i\<bullet>1"
      apply -
      apply rule
      apply (rule Lim_component_ge)
      apply (rule i)
      apply (rule trivial_limit_sequentially)
      unfolding eventually_sequentially
      apply (rule_tac x=k in exI)
      apply safe
      apply (rule integral_component_le)
      apply simp
      apply (rule that(2)[rule_format])+
      apply auto
      done

    note int = assms(2)[unfolded integrable_alt[of _ s],THEN conjunct1,rule_format]
    have ifif: "\<And>k t. (\<lambda>x. if x \<in> t then if x \<in> s then f k x else 0 else 0) =
      (\<lambda>x. if x \<in> t \<inter> s then f k x else 0)"
      by (rule ext) auto
    have int': "\<And>k a b. f k integrable_on cbox a b \<inter> s"
      apply (subst integrable_restrict_univ[symmetric])
      apply (subst ifif[symmetric])
      apply (subst integrable_restrict_univ)
      apply (rule int)
      done
    have "\<And>a b. (\<lambda>x. if x \<in> s then g x else 0) integrable_on cbox a b \<and>
      ((\<lambda>k. integral (cbox a b) (\<lambda>x. if x \<in> s then f k x else 0)) \<longlongrightarrow>
      integral (cbox a b) (\<lambda>x. if x \<in> s then g x else 0)) sequentially"
    proof (rule monotone_convergence_interval, safe, goal_cases)
      case 1
      show ?case by (rule int)
    next
      case (2 _ _ _ x)
      then show ?case
        apply (cases "x \<in> s")
        using assms(3)
        apply auto
        done
    next
      case (3 _ _ x)
      then show ?case
        apply (cases "x \<in> s")
        using assms(4)
        apply auto
        done
    next
      case (4 a b)
      note * = integral_nonneg
      have "\<And>k. norm (integral (cbox a b) (\<lambda>x. if x \<in> s then f k x else 0)) \<le> norm (integral s (f k))"
        unfolding real_norm_def
        apply (subst abs_of_nonneg)
        apply (rule *[OF int])
        apply safe
        apply (case_tac "x \<in> s")
        apply (drule assms(1))
        prefer 3
        apply (subst abs_of_nonneg)
        apply (rule *[OF assms(2) that(1)[THEN spec]])
        apply (subst integral_restrict_univ[symmetric,OF int])
        unfolding ifif
        unfolding integral_restrict_univ[OF int']
        apply (rule integral_subset_le[OF _ int' assms(2)])
        using assms(1)
        apply auto
        done
      then show ?case
        using assms(5)
        unfolding bounded_iff
        apply safe
        apply (rule_tac x=aa in exI)
        apply safe
        apply (erule_tac x="integral s (f k)" in ballE)
        apply (rule order_trans)
        apply assumption
        apply auto
        done
    qed
    note g = conjunctD2[OF this]

    have "(g has_integral i) s"
      unfolding has_integral_alt'
      apply safe
      apply (rule g(1))
    proof goal_cases
      case (1 e)
      then have "e/4>0"
        by auto
      from LIMSEQ_D [OF i this] guess N .. note N=this
      note assms(2)[of N,unfolded has_integral_integral has_integral_alt'[of "f N"]]
      from this[THEN conjunct2,rule_format,OF \<open>e/4>0\<close>] guess B .. note B=conjunctD2[OF this]
      show ?case
        apply rule
        apply rule
        apply (rule B)
        apply safe
      proof -
        fix a b :: 'n
        assume ab: "ball 0 B \<subseteq> cbox a b"
        from \<open>e > 0\<close> have "e/2 > 0"
          by auto
        from LIMSEQ_D [OF g(2)[of a b] this] guess M .. note M=this
        have **: "norm (integral (cbox a b) (\<lambda>x. if x \<in> s then f N x else 0) - i) < e/2"
          apply (rule norm_triangle_half_l)
          using B(2)[rule_format,OF ab] N[rule_format,of N]
          apply -
          defer
          apply (subst norm_minus_commute)
          apply auto
          done
        have *: "\<And>f1 f2 g. \<bar>f1 - i\<bar> < e / 2 \<longrightarrow> \<bar>f2 - g\<bar> < e / 2 \<longrightarrow>
          f1 \<le> f2 \<longrightarrow> f2 \<le> i \<longrightarrow> \<bar>g - i\<bar> < e"
          unfolding real_inner_1_right by arith
        show "norm (integral (cbox a b) (\<lambda>x. if x \<in> s then g x else 0) - i) < e"
          unfolding real_norm_def
          apply (rule *[rule_format])
          apply (rule **[unfolded real_norm_def])
          apply (rule M[rule_format,of "M + N",unfolded real_norm_def])
          apply (rule le_add1)
          apply (rule integral_le[OF int int])
          defer
          apply (rule order_trans[OF _ i'[rule_format,of "M + N",unfolded real_inner_1_right]])
        proof (safe, goal_cases)
          case (2 x)
          have "\<And>m. x \<in> s \<Longrightarrow> \<forall>n\<ge>m. (f m x)\<bullet>1 \<le> (f n x)\<bullet>1"
            apply (rule transitive_stepwise_le)
            using assms(3)
            apply auto
            done
          then show ?case
            by auto
        next
          case 1
          show ?case
            apply (subst integral_restrict_univ[symmetric,OF int])
            unfolding ifif integral_restrict_univ[OF int']
            apply (rule integral_subset_le[OF _ int'])
            using assms
            apply auto
            done
        qed
      qed
    qed
    then show ?thesis
      apply safe
      defer
      apply (drule integral_unique)
      using i
      apply auto
      done
  qed

  have sub: "\<And>k. integral s (\<lambda>x. f k x - f 0 x) = integral s (f k) - integral s (f 0)"
    apply (subst integral_diff)
    apply (rule assms(1)[rule_format])+
    apply rule
    done
  have "\<And>x m. x \<in> s \<Longrightarrow> \<forall>n\<ge>m. f m x \<le> f n x"
    apply (rule transitive_stepwise_le)
    using assms(2)
    apply auto
    done
  note * = this[rule_format]
  have "(\<lambda>x. g x - f 0 x) integrable_on s \<and> ((\<lambda>k. integral s (\<lambda>x. f (Suc k) x - f 0 x)) \<longlongrightarrow>
    integral s (\<lambda>x. g x - f 0 x)) sequentially"
    apply (rule lem)
    apply safe
  proof goal_cases
    case (1 k x)
    then show ?case
      using *[of x 0 "Suc k"] by auto
  next
    case (2 k)
    then show ?case
      apply (rule integrable_diff)
      using assms(1)
      apply auto
      done
  next
    case (3 k x)
    then show ?case
      using *[of x "Suc k" "Suc (Suc k)"] by auto
  next
    case (4 x)
    then show ?case
      apply -
      apply (rule tendsto_diff)
      using LIMSEQ_ignore_initial_segment[OF assms(3)[rule_format],of x 1]
      apply auto
      done
  next
    case 5
    then show ?case
      using assms(4)
      unfolding bounded_iff
      apply safe
      apply (rule_tac x="a + norm (integral s (\<lambda>x. f 0 x))" in exI)
      apply safe
      apply (erule_tac x="integral s (\<lambda>x. f (Suc k) x)" in ballE)
      unfolding sub
      apply (rule order_trans[OF norm_triangle_ineq4])
      apply auto
      done
  qed
  note conjunctD2[OF this]
  note tendsto_add[OF this(2) tendsto_const[of "integral s (f 0)"]]
    integrable_add[OF this(1) assms(1)[rule_format,of 0]]
  then show ?thesis
    unfolding sub
    apply -
    apply rule
    defer
    apply (subst(asm) integral_diff)
    using assms(1)
    apply auto
    apply (rule LIMSEQ_imp_Suc)
    apply assumption
    done
qed

lemma has_integral_monotone_convergence_increasing:
  fixes f :: "nat \<Rightarrow> 'a::euclidean_space \<Rightarrow> real"
  assumes f: "\<And>k. (f k has_integral x k) s"
  assumes "\<And>k x. x \<in> s \<Longrightarrow> f k x \<le> f (Suc k) x"
  assumes "\<And>x. x \<in> s \<Longrightarrow> (\<lambda>k. f k x) \<longlonglongrightarrow> g x"
  assumes "x \<longlonglongrightarrow> x'"
  shows "(g has_integral x') s"
proof -
  have x_eq: "x = (\<lambda>i. integral s (f i))"
    by (simp add: integral_unique[OF f])
  then have x: "{integral s (f k) |k. True} = range x"
    by auto

  have *: "g integrable_on s \<and> (\<lambda>k. integral s (f k)) \<longlonglongrightarrow> integral s g"
  proof (intro monotone_convergence_increasing allI ballI assms)
    show "bounded {integral s (f k) |k. True}"
      unfolding x by (rule convergent_imp_bounded) fact
  qed (auto intro: f)
  then have "integral s g = x'"
    by (intro LIMSEQ_unique[OF _ \<open>x \<longlonglongrightarrow> x'\<close>]) (simp add: x_eq)
  with * show ?thesis
    by (simp add: has_integral_integral)
qed

lemma monotone_convergence_decreasing:
  fixes f :: "nat \<Rightarrow> 'n::euclidean_space \<Rightarrow> real"
  assumes "\<forall>k. (f k) integrable_on s"
    and "\<forall>k. \<forall>x\<in>s. f (Suc k) x \<le> f k x"
    and "\<forall>x\<in>s. ((\<lambda>k. f k x) \<longlongrightarrow> g x) sequentially"
    and "bounded {integral s (f k)| k. True}"
  shows "g integrable_on s \<and> ((\<lambda>k. integral s (f k)) \<longlongrightarrow> integral s g) sequentially"
proof -
  note assm = assms[rule_format]
  have *: "{integral s (\<lambda>x. - f k x) |k. True} = op *\<^sub>R (- 1) ` {integral s (f k)| k. True}"
    apply safe
    unfolding image_iff
    apply (rule_tac x="integral s (f k)" in bexI)
    prefer 3
    apply (rule_tac x=k in exI)
    apply auto
    done
  have "(\<lambda>x. - g x) integrable_on s \<and>
    ((\<lambda>k. integral s (\<lambda>x. - f k x)) \<longlongrightarrow> integral s (\<lambda>x. - g x)) sequentially"
    apply (rule monotone_convergence_increasing)
    apply safe
    apply (rule integrable_neg)
    apply (rule assm)
    defer
    apply (rule tendsto_minus)
    apply (rule assm)
    apply assumption
    unfolding *
    apply (rule bounded_scaling)
    using assm
    apply auto
    done
  note * = conjunctD2[OF this]
  show ?thesis
    using integrable_neg[OF *(1)] tendsto_minus[OF *(2)]
    by auto
qed


subsection \<open>Absolute integrability (this is the same as Lebesgue integrability)\<close>

definition absolutely_integrable_on (infixr "absolutely'_integrable'_on" 46)
  where "f absolutely_integrable_on s \<longleftrightarrow> f integrable_on s \<and> (\<lambda>x. (norm(f x))) integrable_on s"

lemma absolutely_integrable_onI[intro?]:
  "f integrable_on s \<Longrightarrow>
    (\<lambda>x. (norm(f x))) integrable_on s \<Longrightarrow> f absolutely_integrable_on s"
  unfolding absolutely_integrable_on_def
  by auto

lemma absolutely_integrable_onD[dest]:
  assumes "f absolutely_integrable_on s"
  shows "f integrable_on s"
    and "(\<lambda>x. norm (f x)) integrable_on s"
  using assms
  unfolding absolutely_integrable_on_def
  by auto

(*lemma absolutely_integrable_on_trans[simp]:
  fixes f::"'n::euclidean_space \<Rightarrow> real"
  shows "(vec1 \<circ> f) absolutely_integrable_on s \<longleftrightarrow> f absolutely_integrable_on s"
  unfolding absolutely_integrable_on_def o_def by auto*)

lemma integral_norm_bound_integral:
  fixes f :: "'n::euclidean_space \<Rightarrow> 'a::banach"
  assumes "f integrable_on s"
    and "g integrable_on s"
    and "\<forall>x\<in>s. norm (f x) \<le> g x"
  shows "norm (integral s f) \<le> integral s g"
proof -
  have *: "\<And>x y. (\<forall>e::real. 0 < e \<longrightarrow> x < y + e) \<Longrightarrow> x \<le> y"
    apply (rule ccontr)
    apply (erule_tac x="x - y" in allE)
    apply auto
    done
  have norm: "norm ig < dia + e"
    if "norm sg \<le> dsa"
    and "\<bar>dsa - dia\<bar> < e / 2"
    and "norm (sg - ig) < e / 2"
    for e dsa dia and sg ig :: 'a
    apply (rule le_less_trans[OF norm_triangle_sub[of ig sg]])
    apply (subst real_sum_of_halves[of e,symmetric])
    unfolding add.assoc[symmetric]
    apply (rule add_le_less_mono)
    defer
    apply (subst norm_minus_commute)
    apply (rule that(3))
    apply (rule order_trans[OF that(1)])
    using that(2)
    apply arith
    done
  have lem: "norm (integral(cbox a b) f) \<le> integral (cbox a b) g"
    if "f integrable_on cbox a b"
    and "g integrable_on cbox a b"
    and "\<forall>x\<in>cbox a b. norm (f x) \<le> g x"
    for f :: "'n \<Rightarrow> 'a" and g a b
  proof (rule *[rule_format])
    fix e :: real
    assume "e > 0"
    then have *: "e/2 > 0"
      by auto
    from integrable_integral[OF that(1),unfolded has_integral[of f],rule_format,OF *]
    guess d1 .. note d1 = conjunctD2[OF this,rule_format]
    from integrable_integral[OF that(2),unfolded has_integral[of g],rule_format,OF *]
    guess d2 .. note d2 = conjunctD2[OF this,rule_format]
    note gauge_inter[OF d1(1) d2(1)]
    from fine_division_exists[OF this, of a b] guess p . note p=this
    show "norm (integral (cbox a b) f) < integral (cbox a b) g + e"
      apply (rule norm)
      defer
      apply (rule d2(2)[OF conjI[OF p(1)],unfolded real_norm_def])
      defer
      apply (rule d1(2)[OF conjI[OF p(1)]])
      defer
      apply (rule setsum_norm_le)
    proof safe
      fix x k
      assume "(x, k) \<in> p"
      note as = tagged_division_ofD(2-4)[OF p(1) this]
      from this(3) guess u v by (elim exE) note uv=this
      show "norm (content k *\<^sub>R f x) \<le> content k *\<^sub>R g x"
        unfolding uv norm_scaleR
        unfolding abs_of_nonneg[OF content_pos_le] real_scaleR_def
        apply (rule mult_left_mono)
        using that(3) as
        apply auto
        done
    qed (insert p[unfolded fine_inter], auto)
  qed

  { presume "\<And>e. 0 < e \<Longrightarrow> norm (integral s f) < integral s g + e"
    then show ?thesis by (rule *[rule_format]) auto }
  fix e :: real
  assume "e > 0"
  then have e: "e/2 > 0"
    by auto
  note assms(1)[unfolded integrable_alt[of f]] note f=this[THEN conjunct1,rule_format]
  note assms(2)[unfolded integrable_alt[of g]] note g=this[THEN conjunct1,rule_format]
  from integrable_integral[OF assms(1),unfolded has_integral'[of f],rule_format,OF e]
  guess B1 .. note B1=conjunctD2[OF this[rule_format],rule_format]
  from integrable_integral[OF assms(2),unfolded has_integral'[of g],rule_format,OF e]
  guess B2 .. note B2=conjunctD2[OF this[rule_format],rule_format]
  from bounded_subset_cbox[OF bounded_ball, of "0::'n" "max B1 B2"]
  guess a b by (elim exE) note ab=this[unfolded ball_max_Un]

  have "ball 0 B1 \<subseteq> cbox a b"
    using ab by auto
  from B1(2)[OF this] guess z .. note z=conjunctD2[OF this]
  have "ball 0 B2 \<subseteq> cbox a b"
    using ab by auto
  from B2(2)[OF this] guess w .. note w=conjunctD2[OF this]

  show "norm (integral s f) < integral s g + e"
    apply (rule norm)
    apply (rule lem[OF f g, of a b])
    unfolding integral_unique[OF z(1)] integral_unique[OF w(1)]
    defer
    apply (rule w(2)[unfolded real_norm_def])
    apply (rule z(2))
    apply safe
    apply (case_tac "x \<in> s")
    unfolding if_P
    apply (rule assms(3)[rule_format])
    apply auto
    done
qed

lemma integral_norm_bound_integral_component:
  fixes f :: "'n::euclidean_space \<Rightarrow> 'a::banach"
  fixes g :: "'n \<Rightarrow> 'b::euclidean_space"
  assumes "f integrable_on s"
    and "g integrable_on s"
    and "\<forall>x\<in>s. norm(f x) \<le> (g x)\<bullet>k"
  shows "norm (integral s f) \<le> (integral s g)\<bullet>k"
proof -
  have "norm (integral s f) \<le> integral s ((\<lambda>x. x \<bullet> k) \<circ> g)"
    apply (rule integral_norm_bound_integral[OF assms(1)])
    apply (rule integrable_linear[OF assms(2)])
    apply rule
    unfolding o_def
    apply (rule assms)
    done
  then show ?thesis
    unfolding o_def integral_component_eq[OF assms(2)] .
qed

lemma has_integral_norm_bound_integral_component:
  fixes f :: "'n::euclidean_space \<Rightarrow> 'a::banach"
  fixes g :: "'n \<Rightarrow> 'b::euclidean_space"
  assumes "(f has_integral i) s"
    and "(g has_integral j) s"
    and "\<forall>x\<in>s. norm (f x) \<le> (g x)\<bullet>k"
  shows "norm i \<le> j\<bullet>k"
  using integral_norm_bound_integral_component[of f s g k]
  unfolding integral_unique[OF assms(1)] integral_unique[OF assms(2)]
  using assms
  by auto

lemma absolutely_integrable_le:
  fixes f :: "'n::euclidean_space \<Rightarrow> 'a::banach"
  assumes "f absolutely_integrable_on s"
  shows "norm (integral s f) \<le> integral s (\<lambda>x. norm (f x))"
  apply (rule integral_norm_bound_integral)
  using assms
  apply auto
  done

lemma absolutely_integrable_0[intro]:
  "(\<lambda>x. 0) absolutely_integrable_on s"
  unfolding absolutely_integrable_on_def
  by auto

lemma absolutely_integrable_cmul[intro]:
  "f absolutely_integrable_on s \<Longrightarrow>
    (\<lambda>x. c *\<^sub>R f x) absolutely_integrable_on s"
  unfolding absolutely_integrable_on_def
  using integrable_cmul[of f s c]
  using integrable_cmul[of "\<lambda>x. norm (f x)" s "\<bar>c\<bar>"]
  by auto

lemma absolutely_integrable_neg[intro]:
  "f absolutely_integrable_on s \<Longrightarrow>
    (\<lambda>x. -f(x)) absolutely_integrable_on s"
  apply (drule absolutely_integrable_cmul[where c="-1"])
  apply auto
  done

lemma absolutely_integrable_norm[intro]:
  "f absolutely_integrable_on s \<Longrightarrow>
    (\<lambda>x. norm (f x)) absolutely_integrable_on s"
  unfolding absolutely_integrable_on_def
  by auto

lemma absolutely_integrable_abs[intro]:
  "f absolutely_integrable_on s \<Longrightarrow>
    (\<lambda>x. \<bar>f x::real\<bar>) absolutely_integrable_on s"
  apply (drule absolutely_integrable_norm)
  unfolding real_norm_def
  apply assumption
  done

lemma absolutely_integrable_on_subinterval:
  fixes f :: "'n::euclidean_space \<Rightarrow> 'a::banach"
  shows "f absolutely_integrable_on s \<Longrightarrow>
    cbox a b \<subseteq> s \<Longrightarrow> f absolutely_integrable_on cbox a b"
  unfolding absolutely_integrable_on_def
  by (metis integrable_on_subcbox)

lemma absolutely_integrable_bounded_variation:
  fixes f :: "'n::euclidean_space \<Rightarrow> 'a::banach"
  assumes "f absolutely_integrable_on UNIV"
  obtains B where "\<forall>d. d division_of (\<Union>d) \<longrightarrow> setsum (\<lambda>k. norm(integral k f)) d \<le> B"
  apply (rule that[of "integral UNIV (\<lambda>x. norm (f x))"])
  apply safe
proof goal_cases
  case prems: (1 d)
  note d = division_ofD[OF prems(2)]
  have "(\<Sum>k\<in>d. norm (integral k f)) \<le> (\<Sum>i\<in>d. integral i (\<lambda>x. norm (f x)))"
    apply (rule setsum_mono,rule absolutely_integrable_le)
    apply (drule d(4))
    apply safe
    apply (rule absolutely_integrable_on_subinterval[OF assms])
    apply auto
    done
  also have "\<dots> \<le> integral (\<Union>d) (\<lambda>x. norm (f x))"
    apply (subst integral_combine_division_topdown[OF _ prems(2)])
    using integrable_on_subdivision[OF prems(2)]
    using assms
    apply auto
    done
  also have "\<dots> \<le> integral UNIV (\<lambda>x. norm (f x))"
    apply (rule integral_subset_le)
    using integrable_on_subdivision[OF prems(2)]
    using assms
    apply auto
    done
  finally show ?case .
qed

lemma helplemma:
  assumes "setsum (\<lambda>x. norm (f x - g x)) s < e"
    and "finite s"
  shows "\<bar>setsum (\<lambda>x. norm(f x)) s - setsum (\<lambda>x. norm(g x)) s\<bar> < e"
  unfolding setsum_subtractf[symmetric]
  apply (rule le_less_trans[OF setsum_abs])
  apply (rule le_less_trans[OF _ assms(1)])
  apply (rule setsum_mono)
  apply (rule norm_triangle_ineq3)
  done

lemma bounded_variation_absolutely_integrable_interval:
  fixes f :: "'n::euclidean_space \<Rightarrow> 'm::euclidean_space"
  assumes f: "f integrable_on cbox a b"
    and *: "\<forall>d. d division_of (cbox a b) \<longrightarrow> setsum (\<lambda>k. norm(integral k f)) d \<le> B"
  shows "f absolutely_integrable_on cbox a b"
proof -
  let ?f = "\<lambda>d. \<Sum>k\<in>d. norm (integral k f)" and ?D = "{d. d division_of (cbox a b)}"
  have D_1: "?D \<noteq> {}"
    by (rule elementary_interval[of a b]) auto
  have D_2: "bdd_above (?f`?D)"
    by (metis * mem_Collect_eq bdd_aboveI2)
  note D = D_1 D_2
  let ?S = "SUP x:?D. ?f x"
  show ?thesis
    apply (rule absolutely_integrable_onI [OF f has_integral_integrable])
    apply (subst has_integral[of _ ?S])
    apply safe
  proof goal_cases
    case e: (1 e)
    then have "?S - e / 2 < ?S" by simp
    then obtain d where d: "d division_of (cbox a b)" "?S - e / 2 < (\<Sum>k\<in>d. norm (integral k f))"
      unfolding less_cSUP_iff[OF D] by auto
    note d' = division_ofD[OF this(1)]

    have "\<forall>x. \<exists>e>0. \<forall>i\<in>d. x \<notin> i \<longrightarrow> ball x e \<inter> i = {}"
    proof
      fix x
      have "\<exists>da>0. \<forall>xa\<in>\<Union>{i \<in> d. x \<notin> i}. da \<le> dist x xa"
        apply (rule separate_point_closed)
        apply (rule closed_Union)
        apply (rule finite_subset[OF _ d'(1)])
        using d'(4)
        apply auto
        done
      then show "\<exists>e>0. \<forall>i\<in>d. x \<notin> i \<longrightarrow> ball x e \<inter> i = {}"
        by force
    qed
    from choice[OF this] guess k .. note k=conjunctD2[OF this[rule_format],rule_format]

    have "e/2 > 0"
      using e by auto
    from henstock_lemma[OF assms(1) this] guess g . note g=this[rule_format]
    let ?g = "\<lambda>x. g x \<inter> ball x (k x)"
    show ?case
      apply (rule_tac x="?g" in exI)
      apply safe
    proof -
      show "gauge ?g"
        using g(1) k(1)
        unfolding gauge_def
        by auto
      fix p
      assume "p tagged_division_of (cbox a b)" and "?g fine p"
      note p = this(1) conjunctD2[OF this(2)[unfolded fine_inter]]
      note p' = tagged_division_ofD[OF p(1)]
      define p' where "p' = {(x,k) | x k. \<exists>i l. x \<in> i \<and> i \<in> d \<and> (x,l) \<in> p \<and> k = i \<inter> l}"
      have gp': "g fine p'"
        using p(2)
        unfolding p'_def fine_def
        by auto
      have p'': "p' tagged_division_of (cbox a b)"
        apply (rule tagged_division_ofI)
      proof -
        show "finite p'"
          apply (rule finite_subset[of _ "(\<lambda>(k,(x,l)). (x,k \<inter> l)) `
            {(k,xl) | k xl. k \<in> d \<and> xl \<in> p}"])
          unfolding p'_def
          defer
          apply (rule finite_imageI,rule finite_product_dependent[OF d'(1) p'(1)])
          apply safe
          unfolding image_iff
          apply (rule_tac x="(i,x,l)" in bexI)
          apply auto
          done
        fix x k
        assume "(x, k) \<in> p'"
        then have "\<exists>i l. x \<in> i \<and> i \<in> d \<and> (x, l) \<in> p \<and> k = i \<inter> l"
          unfolding p'_def by auto
        then guess i l by (elim exE) note il=conjunctD4[OF this]
        show "x \<in> k" and "k \<subseteq> cbox a b"
          using p'(2-3)[OF il(3)] il by auto
        show "\<exists>a b. k = cbox a b"
          unfolding il using p'(4)[OF il(3)] d'(4)[OF il(2)]
          apply safe
          unfolding inter_interval
          apply auto
          done
      next
        fix x1 k1
        assume "(x1, k1) \<in> p'"
        then have "\<exists>i l. x1 \<in> i \<and> i \<in> d \<and> (x1, l) \<in> p \<and> k1 = i \<inter> l"
          unfolding p'_def by auto
        then guess i1 l1 by (elim exE) note il1=conjunctD4[OF this]
        fix x2 k2
        assume "(x2,k2)\<in>p'"
        then have "\<exists>i l. x2 \<in> i \<and> i \<in> d \<and> (x2, l) \<in> p \<and> k2 = i \<inter> l"
          unfolding p'_def by auto
        then guess i2 l2 by (elim exE) note il2=conjunctD4[OF this]
        assume "(x1, k1) \<noteq> (x2, k2)"
        then have "interior i1 \<inter> interior i2 = {} \<or> interior l1 \<inter> interior l2 = {}"
          using d'(5)[OF il1(2) il2(2)] p'(5)[OF il1(3) il2(3)]
          unfolding il1 il2
          by auto
        then show "interior k1 \<inter> interior k2 = {}"
          unfolding il1 il2 by auto
      next
        have *: "\<forall>(x, X) \<in> p'. X \<subseteq> cbox a b"
          unfolding p'_def using d' by auto
        show "\<Union>{k. \<exists>x. (x, k) \<in> p'} = cbox a b"
          apply rule
          apply (rule Union_least)
          unfolding mem_Collect_eq
          apply (erule exE)
          apply (drule *[rule_format])
          apply safe
        proof -
          fix y
          assume y: "y \<in> cbox a b"
          then have "\<exists>x l. (x, l) \<in> p \<and> y\<in>l"
            unfolding p'(6)[symmetric] by auto
          then guess x l by (elim exE) note xl=conjunctD2[OF this]
          then have "\<exists>k. k \<in> d \<and> y \<in> k"
            using y unfolding d'(6)[symmetric] by auto
          then guess i .. note i = conjunctD2[OF this]
          have "x \<in> i"
            using fineD[OF p(3) xl(1)]
            using k(2)[OF i(1), of x]
            using i(2) xl(2)
            by auto
          then show "y \<in> \<Union>{k. \<exists>x. (x, k) \<in> p'}"
            unfolding p'_def Union_iff
            apply (rule_tac x="i \<inter> l" in bexI)
            using i xl
            apply auto
            done
        qed
      qed

      then have "(\<Sum>(x, k)\<in>p'. norm (content k *\<^sub>R f x - integral k f)) < e / 2"
        apply -
        apply (rule g(2)[rule_format])
        unfolding tagged_division_of_def
        apply safe
        apply (rule gp')
        done
      then have **: "\<bar>(\<Sum>(x,k)\<in>p'. norm (content k *\<^sub>R f x)) - (\<Sum>(x,k)\<in>p'. norm (integral k f))\<bar> < e / 2"
        unfolding split_def
        using p''
        by (force intro!: helplemma)

      have p'alt: "p' = {(x,(i \<inter> l)) | x i l. (x,l) \<in> p \<and> i \<in> d \<and> i \<inter> l \<noteq> {}}"
      proof (safe, goal_cases)
        case prems: (2 _ _ x i l)
        have "x \<in> i"
          using fineD[OF p(3) prems(1)] k(2)[OF prems(2), of x] prems(4-)
          by auto
        then have "(x, i \<inter> l) \<in> p'"
          unfolding p'_def
          using prems
          apply safe
          apply (rule_tac x=x in exI)
          apply (rule_tac x="i \<inter> l" in exI)
          apply safe
          using prems
          apply auto
          done
        then show ?case
          using prems(3) by auto
      next
        fix x k
        assume "(x, k) \<in> p'"
        then have "\<exists>i l. x \<in> i \<and> i \<in> d \<and> (x, l) \<in> p \<and> k = i \<inter> l"
          unfolding p'_def by auto
        then guess i l by (elim exE) note il=conjunctD4[OF this]
        then show "\<exists>y i l. (x, k) = (y, i \<inter> l) \<and> (y, l) \<in> p \<and> i \<in> d \<and> i \<inter> l \<noteq> {}"
          apply (rule_tac x=x in exI)
          apply (rule_tac x=i in exI)
          apply (rule_tac x=l in exI)
          using p'(2)[OF il(3)]
          apply auto
          done
      qed
      have sum_p': "(\<Sum>(x, k)\<in>p'. norm (integral k f)) = (\<Sum>k\<in>snd ` p'. norm (integral k f))"
        apply (subst setsum.over_tagged_division_lemma[OF p'',of "\<lambda>k. norm (integral k f)"])
        unfolding norm_eq_zero
        apply (rule integral_null)
        apply assumption
        apply rule
        done
      note snd_p = division_ofD[OF division_of_tagged_division[OF p(1)]]

      have *: "\<And>sni sni' sf sf'. \<bar>sf' - sni'\<bar> < e / 2 \<longrightarrow> ?S - e / 2 < sni \<and> sni' \<le> ?S \<and>
        sni \<le> sni' \<and> sf' = sf \<longrightarrow> \<bar>sf - ?S\<bar> < e"
        by arith
      show "norm ((\<Sum>(x, k)\<in>p. content k *\<^sub>R norm (f x)) - ?S) < e"
        unfolding real_norm_def
        apply (rule *[rule_format,OF **])
        apply safe
        apply(rule d(2))
      proof goal_cases
        case 1
        show ?case
          by (auto simp: sum_p' division_of_tagged_division[OF p''] D intro!: cSUP_upper)
      next
        case 2
        have *: "{k \<inter> l | k l. k \<in> d \<and> l \<in> snd ` p} =
          (\<lambda>(k,l). k \<inter> l) ` {(k,l)|k l. k \<in> d \<and> l \<in> snd ` p}"
          by auto
        have "(\<Sum>k\<in>d. norm (integral k f)) \<le> (\<Sum>i\<in>d. \<Sum>l\<in>snd ` p. norm (integral (i \<inter> l) f))"
        proof (rule setsum_mono, goal_cases)
          case k: (1 k)
          from d'(4)[OF this] guess u v by (elim exE) note uv=this
          define d' where "d' = {cbox u v \<inter> l |l. l \<in> snd ` p \<and>  cbox u v \<inter> l \<noteq> {}}"
          note uvab = d'(2)[OF k[unfolded uv]]
          have "d' division_of cbox u v"
            apply (subst d'_def)
            apply (rule division_inter_1)
            apply (rule division_of_tagged_division[OF p(1)])
            apply (rule uvab)
            done
          then have "norm (integral k f) \<le> setsum (\<lambda>k. norm (integral k f)) d'"
            unfolding uv
            apply (subst integral_combine_division_topdown[of _ _ d'])
            apply (rule integrable_on_subcbox[OF assms(1) uvab])
            apply assumption
            apply (rule setsum_norm_le)
            apply auto
            done
          also have "\<dots> = (\<Sum>k\<in>{k \<inter> l |l. l \<in> snd ` p}. norm (integral k f))"
            apply (rule setsum.mono_neutral_left)
            apply (subst Setcompr_eq_image)
            apply (rule finite_imageI)+
            apply fact
            unfolding d'_def uv
            apply blast
          proof (rule, goal_cases)
            case prems: (1 i)
            then have "i \<in> {cbox u v \<inter> l |l. l \<in> snd ` p}"
              by auto
            from this[unfolded mem_Collect_eq] guess l .. note l=this
            then have "cbox u v \<inter> l = {}"
              using prems by auto
            then show ?case
              using l by auto
          qed
          also have "\<dots> = (\<Sum>l\<in>snd ` p. norm (integral (k \<inter> l) f))"
            unfolding Setcompr_eq_image
            apply (rule setsum.reindex_nontrivial [unfolded o_def])
            apply (rule finite_imageI)
            apply (rule p')
          proof goal_cases
            case prems: (1 l y)
            have "interior (k \<inter> l) \<subseteq> interior (l \<inter> y)"
              apply (subst(2) interior_Int)
              apply (rule Int_greatest)
              defer
              apply (subst prems(4))
              apply auto
              done
            then have *: "interior (k \<inter> l) = {}"
              using snd_p(5)[OF prems(1-3)] by auto
            from d'(4)[OF k] snd_p(4)[OF prems(1)] guess u1 v1 u2 v2 by (elim exE) note uv=this
            show ?case
              using *
              unfolding uv inter_interval content_eq_0_interior[symmetric]
              by auto
          qed
          finally show ?case .
        qed
        also have "\<dots> = (\<Sum>(i,l)\<in>{(i, l) |i l. i \<in> d \<and> l \<in> snd ` p}. norm (integral (i\<inter>l) f))"
          apply (subst sum_sum_product[symmetric])
          apply fact
          using p'(1)
          apply auto
          done
        also have "\<dots> = (\<Sum>x\<in>{(i, l) |i l. i \<in> d \<and> l \<in> snd ` p}. norm (integral (case_prod op \<inter> x) f))"
          unfolding split_def ..
        also have "\<dots> = (\<Sum>k\<in>{i \<inter> l |i l. i \<in> d \<and> l \<in> snd ` p}. norm (integral k f))"
          unfolding *
          apply (rule setsum.reindex_nontrivial [symmetric, unfolded o_def])
          apply (rule finite_product_dependent)
          apply fact
          apply (rule finite_imageI)
          apply (rule p')
          unfolding split_paired_all mem_Collect_eq split_conv o_def
        proof -
          note * = division_ofD(4,5)[OF division_of_tagged_division,OF p(1)]
          fix l1 l2 k1 k2
          assume as:
            "(l1, k1) \<noteq> (l2, k2)"
            "l1 \<inter> k1 = l2 \<inter> k2"
            "\<exists>i l. (l1, k1) = (i, l) \<and> i \<in> d \<and> l \<in> snd ` p"
            "\<exists>i l. (l2, k2) = (i, l) \<and> i \<in> d \<and> l \<in> snd ` p"
          then have "l1 \<in> d" and "k1 \<in> snd ` p"
            by auto from d'(4)[OF this(1)] *(1)[OF this(2)]
          guess u1 v1 u2 v2 by (elim exE) note uv=this
          have "l1 \<noteq> l2 \<or> k1 \<noteq> k2"
            using as by auto
          then have "interior k1 \<inter> interior k2 = {} \<or> interior l1 \<inter> interior l2 = {}"
            apply -
            apply (erule disjE)
            apply (rule disjI2)
            apply (rule d'(5))
            prefer 4
            apply (rule disjI1)
            apply (rule *)
            using as
            apply auto
            done
          moreover have "interior (l1 \<inter> k1) = interior (l2 \<inter> k2)"
            using as(2) by auto
          ultimately have "interior(l1 \<inter> k1) = {}"
            by auto
          then show "norm (integral (l1 \<inter> k1) f) = 0"
            unfolding uv inter_interval
            unfolding content_eq_0_interior[symmetric]
            by auto
        qed
        also have "\<dots> = (\<Sum>(x, k)\<in>p'. norm (integral k f))"
          unfolding sum_p'
          apply (rule setsum.mono_neutral_right)
          apply (subst *)
          apply (rule finite_imageI[OF finite_product_dependent])
          apply fact
          apply (rule finite_imageI[OF p'(1)])
          apply safe
        proof goal_cases
          case (2 i ia l a b)
          then have "ia \<inter> b = {}"
            unfolding p'alt image_iff Bex_def not_ex
            apply (erule_tac x="(a, ia \<inter> b)" in allE)
            apply auto
            done
          then show ?case
            by auto
        next
          case (1 x a b)
          then show ?case
            unfolding p'_def
            apply safe
            apply (rule_tac x=i in exI)
            apply (rule_tac x=l in exI)
            unfolding snd_conv image_iff
            apply safe
            apply (rule_tac x="(a,l)" in bexI)
            apply auto
            done
        qed
        finally show ?case .
      next
        case 3
        let ?S = "{(x, i \<inter> l) |x i l. (x, l) \<in> p \<and> i \<in> d}"
        have Sigma_alt: "\<And>s t. s \<times> t = {(i, j) |i j. i \<in> s \<and> j \<in> t}"
          by auto
        have *: "?S = (\<lambda>(xl,i). (fst xl, snd xl \<inter> i)) ` (p \<times> d)"
          apply safe
          unfolding image_iff
          apply (rule_tac x="((x,l),i)" in bexI)
          apply auto
          done
        note pdfin = finite_cartesian_product[OF p'(1) d'(1)]
        have "(\<Sum>(x, k)\<in>p'. norm (content k *\<^sub>R f x)) = (\<Sum>(x, k)\<in>?S. \<bar>content k\<bar> * norm (f x))"
          unfolding norm_scaleR
          apply (rule setsum.mono_neutral_left)
          apply (subst *)
          apply (rule finite_imageI)
          apply fact
          unfolding p'alt
          apply blast
          apply safe
          apply (rule_tac x=x in exI)
          apply (rule_tac x=i in exI)
          apply (rule_tac x=l in exI)
          apply auto
          done
        also have "\<dots> = (\<Sum>((x,l),i)\<in>p \<times> d. \<bar>content (l \<inter> i)\<bar> * norm (f x))"
          unfolding *
          apply (subst setsum.reindex_nontrivial)
          apply fact
          unfolding split_paired_all
          unfolding o_def split_def snd_conv fst_conv mem_Sigma_iff prod.inject
          apply (elim conjE)
        proof -
          fix x1 l1 k1 x2 l2 k2
          assume as: "(x1, l1) \<in> p" "(x2, l2) \<in> p" "k1 \<in> d" "k2 \<in> d"
            "x1 = x2" "l1 \<inter> k1 = l2 \<inter> k2" "\<not> ((x1 = x2 \<and> l1 = l2) \<and> k1 = k2)"
          from d'(4)[OF as(3)] p'(4)[OF as(1)] guess u1 v1 u2 v2 by (elim exE) note uv=this
          from as have "l1 \<noteq> l2 \<or> k1 \<noteq> k2"
            by auto
          then have "interior k1 \<inter> interior k2 = {} \<or> interior l1 \<inter> interior l2 = {}"
            apply -
            apply (erule disjE)
            apply (rule disjI2)
            defer
            apply (rule disjI1)
            apply (rule d'(5)[OF as(3-4)])
            apply assumption
            apply (rule p'(5)[OF as(1-2)])
            apply auto
            done
          moreover have "interior (l1 \<inter> k1) = interior (l2 \<inter> k2)"
            unfolding  as ..
          ultimately have "interior (l1 \<inter> k1) = {}"
            by auto
          then show "\<bar>content (l1 \<inter> k1)\<bar> * norm (f x1) = 0"
            unfolding uv inter_interval
            unfolding content_eq_0_interior[symmetric]
            by auto
        qed safe
        also have "\<dots> = (\<Sum>(x, k)\<in>p. content k *\<^sub>R norm (f x))"
          unfolding Sigma_alt
          apply (subst sum_sum_product[symmetric])
          apply (rule p')
          apply rule
          apply (rule d')
          apply (rule setsum.cong)
          apply (rule refl)
          unfolding split_paired_all split_conv
        proof -
          fix x l
          assume as: "(x, l) \<in> p"
          note xl = p'(2-4)[OF this]
          from this(3) guess u v by (elim exE) note uv=this
          have "(\<Sum>i\<in>d. \<bar>content (l \<inter> i)\<bar>) = (\<Sum>k\<in>d. content (k \<inter> cbox u v))"
            apply (rule setsum.cong)
            apply (rule refl)
            apply (drule d'(4))
            apply safe
            apply (subst Int_commute)
            unfolding inter_interval uv
            apply (subst abs_of_nonneg)
            apply auto
            done
          also have "\<dots> = setsum content {k \<inter> cbox u v| k. k \<in> d}"
            unfolding Setcompr_eq_image
            apply (rule setsum.reindex_nontrivial [unfolded o_def, symmetric])
            apply (rule d')
          proof goal_cases
            case prems: (1 k y)
            from d'(4)[OF this(1)] d'(4)[OF this(2)]
            guess u1 v1 u2 v2 by (elim exE) note uv=this
            have "{} = interior ((k \<inter> y) \<inter> cbox u v)"
              apply (subst interior_Int)
              using d'(5)[OF prems(1-3)]
              apply auto
              done
            also have "\<dots> = interior (y \<inter> (k \<inter> cbox u v))"
              by auto
            also have "\<dots> = interior (k \<inter> cbox u v)"
              unfolding prems(4) by auto
            finally show ?case
              unfolding uv inter_interval content_eq_0_interior ..
          qed
          also have "\<dots> = setsum content {cbox u v \<inter> k |k. k \<in> d \<and> cbox u v \<inter> k \<noteq> {}}"
            apply (rule setsum.mono_neutral_right)
            unfolding Setcompr_eq_image
            apply (rule finite_imageI)
            apply (rule d')
            apply blast
            apply safe
            apply (rule_tac x=k in exI)
          proof goal_cases
            case prems: (1 i k)
            from d'(4)[OF this(1)] guess a b by (elim exE) note ab=this
            have "interior (k \<inter> cbox u v) \<noteq> {}"
              using prems(2)
              unfolding ab inter_interval content_eq_0_interior
              by auto
            then show ?case
              using prems(1)
              using interior_subset[of "k \<inter> cbox u v"]
              by auto
          qed
          finally show "(\<Sum>i\<in>d. \<bar>content (l \<inter> i)\<bar> * norm (f x)) = content l *\<^sub>R norm (f x)"
            unfolding setsum_distrib_right[symmetric] real_scaleR_def
            apply (subst(asm) additive_content_division[OF division_inter_1[OF d(1)]])
            using xl(2)[unfolded uv]
            unfolding uv
            apply auto
            done
        qed
        finally show ?case .
      qed
    qed
  qed
qed

lemma bounded_variation_absolutely_integrable:
  fixes f :: "'n::euclidean_space \<Rightarrow> 'm::euclidean_space"
  assumes "f integrable_on UNIV"
    and "\<forall>d. d division_of (\<Union>d) \<longrightarrow> setsum (\<lambda>k. norm (integral k f)) d \<le> B"
  shows "f absolutely_integrable_on UNIV"
proof (rule absolutely_integrable_onI, fact, rule)
  let ?f = "\<lambda>d. \<Sum>k\<in>d. norm (integral k f)" and ?D = "{d. d division_of  (\<Union>d)}"
  have D_1: "?D \<noteq> {}"
    by (rule elementary_interval) auto
  have D_2: "bdd_above (?f`?D)"
    by (intro bdd_aboveI2[where M=B] assms(2)[rule_format]) simp
  note D = D_1 D_2
  let ?S = "SUP d:?D. ?f d"
  have f_int: "\<And>a b. f absolutely_integrable_on cbox a b"
    apply (rule bounded_variation_absolutely_integrable_interval[where B=B])
    apply (rule integrable_on_subcbox[OF assms(1)])
    defer
    apply safe
    apply (rule assms(2)[rule_format])
    apply auto
    done
  show "((\<lambda>x. norm (f x)) has_integral ?S) UNIV"
    apply (subst has_integral_alt')
    apply safe
  proof goal_cases
    case (1 a b)
    show ?case
      using f_int[of a b] by auto
  next
    case prems: (2 e)
    have "\<exists>y\<in>setsum (\<lambda>k. norm (integral k f)) ` {d. d division_of \<Union>d}. \<not> y \<le> ?S - e"
    proof (rule ccontr)
      assume "\<not> ?thesis"
      then have "?S \<le> ?S - e"
        by (intro cSUP_least[OF D(1)]) auto
      then show False
        using prems by auto
    qed
    then obtain K where *: "\<exists>x\<in>{d. d division_of \<Union>d}. K = (\<Sum>k\<in>x. norm (integral k f))"
      "SUPREMUM {d. d division_of \<Union>d} (setsum (\<lambda>k. norm (integral k f))) - e < K"
      by (auto simp add: image_iff not_le)
    from this(1) obtain d where "d division_of \<Union>d"
      and "K = (\<Sum>k\<in>d. norm (integral k f))"
      by auto
    note d = this(1) *(2)[unfolded this(2)]
    note d'=division_ofD[OF this(1)]
    have "bounded (\<Union>d)"
      by (rule elementary_bounded,fact)
    from this[unfolded bounded_pos] obtain K where
       K: "0 < K" "\<forall>x\<in>\<Union>d. norm x \<le> K" by auto
    show ?case
      apply (rule_tac x="K + 1" in exI)
      apply safe
    proof -
      fix a b :: 'n
      assume ab: "ball 0 (K + 1) \<subseteq> cbox a b"
      have *: "\<forall>s s1. ?S - e < s1 \<and> s1 \<le> s \<and> s < ?S + e \<longrightarrow> \<bar>s - ?S\<bar> < e"
        by arith
      show "norm (integral (cbox a b) (\<lambda>x. if x \<in> UNIV then norm (f x) else 0) - ?S) < e"
        unfolding real_norm_def
        apply (rule *[rule_format])
        apply safe
        apply (rule d(2))
      proof goal_cases
        case 1
        have "(\<Sum>k\<in>d. norm (integral k f)) \<le> setsum (\<lambda>k. integral k (\<lambda>x. norm (f x))) d"
          apply (rule setsum_mono)
          apply (rule absolutely_integrable_le)
          apply (drule d'(4))
          apply safe
          apply (rule f_int)
          done
        also have "\<dots> = integral (\<Union>d) (\<lambda>x. norm (f x))"
          apply (rule integral_combine_division_bottomup[symmetric])
          apply (rule d)
          unfolding forall_in_division[OF d(1)]
          using f_int
          apply auto
          done
        also have "\<dots> \<le> integral (cbox a b) (\<lambda>x. if x \<in> UNIV then norm (f x) else 0)"
        proof -
          have "\<Union>d \<subseteq> cbox a b"
            apply rule
            apply (drule K(2)[rule_format])
            apply (rule ab[unfolded subset_eq,rule_format])
            apply (auto simp add: dist_norm)
            done
          then show ?thesis
            apply -
            apply (subst if_P)
            apply rule
            apply (rule integral_subset_le)
            defer
            apply (rule integrable_on_subdivision[of _ _ _ "cbox a b"])
            apply (rule d)
            using f_int[of a b]
            apply auto
            done
        qed
        finally show ?case .
      next
        note f = absolutely_integrable_onD[OF f_int[of a b]]
        note * = this(2)[unfolded has_integral_integral has_integral[of "\<lambda>x. norm (f x)"],rule_format]
        have "e/2>0"
          using \<open>e > 0\<close> by auto
        from * [OF this] obtain d1 where
          d1: "gauge d1" "\<forall>p. p tagged_division_of (cbox a b) \<and> d1 fine p \<longrightarrow>
            norm ((\<Sum>(x, k)\<in>p. content k *\<^sub>R norm (f x)) - integral (cbox a b) (\<lambda>x. norm (f x))) < e / 2"
          by auto
        from henstock_lemma [OF f(1) \<open>e/2>0\<close>] obtain d2 where
          d2: "gauge d2" "\<forall>p. p tagged_partial_division_of (cbox a b) \<and> d2 fine p \<longrightarrow>
            (\<Sum>(x, k)\<in>p. norm (content k *\<^sub>R f x - integral k f)) < e / 2" .
         obtain p where
          p: "p tagged_division_of (cbox a b)" "d1 fine p" "d2 fine p"
          by (rule fine_division_exists [OF gauge_inter [OF d1(1) d2(1)], of a b])
            (auto simp add: fine_inter)
        have *: "\<And>sf sf' si di. sf' = sf \<longrightarrow> si \<le> ?S \<longrightarrow> \<bar>sf - si\<bar> < e / 2 \<longrightarrow>
          \<bar>sf' - di\<bar> < e / 2 \<longrightarrow> di < ?S + e"
          by arith
        show "integral (cbox a b) (\<lambda>x. if x \<in> UNIV then norm (f x) else 0) < ?S + e"
          apply (subst if_P)
          apply rule
        proof (rule *[rule_format])
          show "\<bar>(\<Sum>(x,k)\<in>p. norm (content k *\<^sub>R f x)) - (\<Sum>(x,k)\<in>p. norm (integral k f))\<bar> < e / 2"
            unfolding split_def
            apply (rule helplemma)
            using d2(2)[rule_format,of p]
            using p(1,3)
            unfolding tagged_division_of_def split_def
            apply auto
            done
          show "\<bar>(\<Sum>(x, k)\<in>p. content k *\<^sub>R norm (f x)) - integral (cbox a b) (\<lambda>x. norm(f x))\<bar> < e / 2"
            using d1(2)[rule_format,OF conjI[OF p(1,2)]]
            by (simp only: real_norm_def)
          show "(\<Sum>(x, k)\<in>p. content k *\<^sub>R norm (f x)) = (\<Sum>(x, k)\<in>p. norm (content k *\<^sub>R f x))"
            apply (rule setsum.cong)
            apply (rule refl)
            unfolding split_paired_all split_conv
            apply (drule tagged_division_ofD(4)[OF p(1)])
            unfolding norm_scaleR
            apply (subst abs_of_nonneg)
            apply auto
            done
          show "(\<Sum>(x, k)\<in>p. norm (integral k f)) \<le> ?S"
            using partial_division_of_tagged_division[of p "cbox a b"] p(1)
            apply (subst setsum.over_tagged_division_lemma[OF p(1)])
            apply (simp add: integral_null)
            apply (intro cSUP_upper2[OF D(2), of "snd ` p"])
            apply (auto simp: tagged_partial_division_of_def)
            done
        qed
      qed
    qed (insert K, auto)
  qed
qed

lemma absolutely_integrable_restrict_univ:
  "(\<lambda>x. if x \<in> s then f x else (0::'a::banach)) absolutely_integrable_on UNIV \<longleftrightarrow>
    f absolutely_integrable_on s"
  unfolding absolutely_integrable_on_def if_distrib norm_zero integrable_restrict_univ ..

lemma absolutely_integrable_add[intro]:
  fixes f g :: "'n::euclidean_space \<Rightarrow> 'm::euclidean_space"
  assumes "f absolutely_integrable_on s"
    and "g absolutely_integrable_on s"
  shows "(\<lambda>x. f x + g x) absolutely_integrable_on s"
proof -
  let ?P = "\<And>f g::'n \<Rightarrow> 'm. f absolutely_integrable_on UNIV \<Longrightarrow>
    g absolutely_integrable_on UNIV \<Longrightarrow> (\<lambda>x. f x + g x) absolutely_integrable_on UNIV"
  {
    presume as: "PROP ?P"
    note a = absolutely_integrable_restrict_univ[symmetric]
    have *: "\<And>x. (if x \<in> s then f x else 0) + (if x \<in> s then g x else 0) =
      (if x \<in> s then f x + g x else 0)" by auto
    show ?thesis
      apply (subst a)
      using as[OF assms[unfolded a[of f] a[of g]]]
      apply (simp only: *)
      done
  }
  fix f g :: "'n \<Rightarrow> 'm"
  assume assms: "f absolutely_integrable_on UNIV" "g absolutely_integrable_on UNIV"
  note absolutely_integrable_bounded_variation
  from this[OF assms(1)] this[OF assms(2)] guess B1 B2 . note B=this[rule_format]
  show "(\<lambda>x. f x + g x) absolutely_integrable_on UNIV"
    apply (rule bounded_variation_absolutely_integrable[of _ "B1+B2"])
    apply (rule integrable_add)
    prefer 3
    apply safe
  proof goal_cases
    case prems: (1 d)
    have "\<And>k. k \<in> d \<Longrightarrow> f integrable_on k \<and> g integrable_on k"
      apply (drule division_ofD(4)[OF prems])
      apply safe
      apply (rule_tac[!] integrable_on_subcbox[of _ UNIV])
      using assms
      apply auto
      done
    then have "(\<Sum>k\<in>d. norm (integral k (\<lambda>x. f x + g x))) \<le>
      (\<Sum>k\<in>d. norm (integral k f)) + (\<Sum>k\<in>d. norm (integral k g))"
      apply -
      unfolding setsum.distrib [symmetric]
      apply (rule setsum_mono)
      apply (subst integral_add)
      prefer 3
      apply (rule norm_triangle_ineq)
      apply auto
      done
    also have "\<dots> \<le> B1 + B2"
      using B(1)[OF prems] B(2)[OF prems] by auto
    finally show ?case .
  qed (insert assms, auto)
qed

lemma absolutely_integrable_sub[intro]:
  fixes f g :: "'n::euclidean_space \<Rightarrow> 'm::euclidean_space"
  assumes "f absolutely_integrable_on s"
    and "g absolutely_integrable_on s"
  shows "(\<lambda>x. f x - g x) absolutely_integrable_on s"
  using absolutely_integrable_add[OF assms(1) absolutely_integrable_neg[OF assms(2)]]
  by (simp add: algebra_simps)

lemma absolutely_integrable_linear:
  fixes f :: "'m::euclidean_space \<Rightarrow> 'n::euclidean_space"
    and h :: "'n::euclidean_space \<Rightarrow> 'p::euclidean_space"
  assumes "f absolutely_integrable_on s"
    and "bounded_linear h"
  shows "(h \<circ> f) absolutely_integrable_on s"
proof -
  {
    presume as: "\<And>f::'m \<Rightarrow> 'n. \<And>h::'n \<Rightarrow> 'p. f absolutely_integrable_on UNIV \<Longrightarrow>
      bounded_linear h \<Longrightarrow> (h \<circ> f) absolutely_integrable_on UNIV"
    note a = absolutely_integrable_restrict_univ[symmetric]
    show ?thesis
      apply (subst a)
      using as[OF assms[unfolded a[of f] a[of g]]]
      apply (simp only: o_def if_distrib linear_simps[OF assms(2)])
      done
  }
  fix f :: "'m \<Rightarrow> 'n"
  fix h :: "'n \<Rightarrow> 'p"
  assume assms: "f absolutely_integrable_on UNIV" "bounded_linear h"
  from absolutely_integrable_bounded_variation[OF assms(1)] guess B . note B=this
  from bounded_linear.pos_bounded[OF assms(2)] guess b .. note b=conjunctD2[OF this]
  show "(h \<circ> f) absolutely_integrable_on UNIV"
    apply (rule bounded_variation_absolutely_integrable[of _ "B * b"])
    apply (rule integrable_linear[OF _ assms(2)])
    apply safe
  proof goal_cases
    case prems: (2 d)
    have "(\<Sum>k\<in>d. norm (integral k (h \<circ> f))) \<le> setsum (\<lambda>k. norm(integral k f)) d * b"
      unfolding setsum_distrib_right
      apply (rule setsum_mono)
    proof goal_cases
      case (1 k)
      from division_ofD(4)[OF prems this]
      guess u v by (elim exE) note uv=this
      have *: "f integrable_on k"
        unfolding uv
        apply (rule integrable_on_subcbox[of _ UNIV])
        using assms
        apply auto
        done
      note this[unfolded has_integral_integral]
      note has_integral_linear[OF this assms(2)] integrable_linear[OF * assms(2)]
      note * = has_integral_unique[OF this(2)[unfolded has_integral_integral] this(1)]
      show ?case
        unfolding * using b by auto
    qed
    also have "\<dots> \<le> B * b"
      apply (rule mult_right_mono)
      using B prems b
      apply auto
      done
    finally show ?case .
  qed (insert assms, auto)
qed

lemma absolutely_integrable_setsum:
  fixes f :: "'a \<Rightarrow> 'n::euclidean_space \<Rightarrow> 'm::euclidean_space"
  assumes "finite t"
    and "\<And>a. a \<in> t \<Longrightarrow> (f a) absolutely_integrable_on s"
  shows "(\<lambda>x. setsum (\<lambda>a. f a x) t) absolutely_integrable_on s"
  using assms(1,2)
  by induct auto

lemma absolutely_integrable_vector_abs:
  fixes f :: "'a::euclidean_space => 'b::euclidean_space"
    and T :: "'c::euclidean_space \<Rightarrow> 'b"
  assumes f: "f absolutely_integrable_on s"
  shows "(\<lambda>x. (\<Sum>i\<in>Basis. \<bar>f x\<bullet>T i\<bar> *\<^sub>R i)) absolutely_integrable_on s"
  (is "?Tf absolutely_integrable_on s")
proof -
  have if_distrib: "\<And>P A B x. (if P then A else B) *\<^sub>R x = (if P then A *\<^sub>R x else B *\<^sub>R x)"
    by simp
  have *: "\<And>x. ?Tf x = (\<Sum>i\<in>Basis.
    ((\<lambda>y. (\<Sum>j\<in>Basis. (if j = i then y else 0) *\<^sub>R j)) o
     (\<lambda>x. (norm (\<Sum>j\<in>Basis. (if j = i then f x\<bullet>T i else 0) *\<^sub>R j)))) x)"
    by (simp add: comp_def if_distrib setsum.If_cases)
  show ?thesis
    unfolding *
    apply (rule absolutely_integrable_setsum[OF finite_Basis])
    apply (rule absolutely_integrable_linear)
    apply (rule absolutely_integrable_norm)
    apply (rule absolutely_integrable_linear[OF f, unfolded o_def])
    apply (auto simp: linear_linear euclidean_eq_iff[where 'a='c] inner_simps intro!: linearI)
    done
qed

lemma absolutely_integrable_max:
  fixes f g :: "'m::euclidean_space \<Rightarrow> 'n::euclidean_space"
  assumes "f absolutely_integrable_on s"
    and "g absolutely_integrable_on s"
  shows "(\<lambda>x. (\<Sum>i\<in>Basis. max (f(x)\<bullet>i) (g(x)\<bullet>i) *\<^sub>R i)::'n) absolutely_integrable_on s"
proof -
  have *:"\<And>x. (1 / 2) *\<^sub>R (((\<Sum>i\<in>Basis. \<bar>(f x - g x) \<bullet> i\<bar> *\<^sub>R i)::'n) + (f x + g x)) =
      (\<Sum>i\<in>Basis. max (f(x)\<bullet>i) (g(x)\<bullet>i) *\<^sub>R i)"
    unfolding euclidean_eq_iff[where 'a='n] by (auto simp: inner_simps)
  note absolutely_integrable_sub[OF assms] absolutely_integrable_add[OF assms]
  note absolutely_integrable_vector_abs[OF this(1), where T="\<lambda>x. x"] this(2)
  note absolutely_integrable_add[OF this]
  note absolutely_integrable_cmul[OF this, of "1/2"]
  then show ?thesis unfolding * .
qed

lemma absolutely_integrable_min:
  fixes f g::"'m::euclidean_space \<Rightarrow> 'n::euclidean_space"
  assumes "f absolutely_integrable_on s"
    and "g absolutely_integrable_on s"
  shows "(\<lambda>x. (\<Sum>i\<in>Basis. min (f(x)\<bullet>i) (g(x)\<bullet>i) *\<^sub>R i)::'n) absolutely_integrable_on s"
proof -
  have *:"\<And>x. (1 / 2) *\<^sub>R ((f x + g x) - (\<Sum>i\<in>Basis. \<bar>(f x - g x) \<bullet> i\<bar> *\<^sub>R i::'n)) =
      (\<Sum>i\<in>Basis. min (f(x)\<bullet>i) (g(x)\<bullet>i) *\<^sub>R i)"
    unfolding euclidean_eq_iff[where 'a='n] by (auto simp: inner_simps)

  note absolutely_integrable_add[OF assms] absolutely_integrable_sub[OF assms]
  note this(1) absolutely_integrable_vector_abs[OF this(2), where T="\<lambda>x. x"]
  note absolutely_integrable_sub[OF this]
  note absolutely_integrable_cmul[OF this,of "1/2"]
  then show ?thesis unfolding * .
qed

lemma absolutely_integrable_abs_eq:
  fixes f::"'n::euclidean_space \<Rightarrow> 'm::euclidean_space"
  shows "f absolutely_integrable_on s \<longleftrightarrow> f integrable_on s \<and>
    (\<lambda>x. (\<Sum>i\<in>Basis. \<bar>f x\<bullet>i\<bar> *\<^sub>R i)::'m) integrable_on s"
  (is "?l = ?r")
proof
  assume ?l
  then show ?r
    apply -
    apply rule
    defer
    apply (drule absolutely_integrable_vector_abs)
    apply auto
    done
next
  assume ?r
  {
    presume lem: "\<And>f::'n \<Rightarrow> 'm. f integrable_on UNIV \<Longrightarrow>
      (\<lambda>x. (\<Sum>i\<in>Basis. \<bar>f x\<bullet>i\<bar> *\<^sub>R i)::'m) integrable_on UNIV \<Longrightarrow>
        f absolutely_integrable_on UNIV"
    have *: "\<And>x. (\<Sum>i\<in>Basis. \<bar>(if x \<in> s then f x else 0) \<bullet> i\<bar> *\<^sub>R i) =
      (if x \<in> s then (\<Sum>i\<in>Basis. \<bar>f x \<bullet> i\<bar> *\<^sub>R i) else (0::'m))"
      unfolding euclidean_eq_iff[where 'a='m]
      by auto
    show ?l
      apply (subst absolutely_integrable_restrict_univ[symmetric])
      apply (rule lem)
      unfolding integrable_restrict_univ *
      using \<open>?r\<close>
      apply auto
      done
  }
  fix f :: "'n \<Rightarrow> 'm"
  assume assms: "f integrable_on UNIV" "(\<lambda>x. (\<Sum>i\<in>Basis. \<bar>f x\<bullet>i\<bar> *\<^sub>R i)::'m) integrable_on UNIV"
  let ?B = "\<Sum>i\<in>Basis. integral UNIV (\<lambda>x. (\<Sum>i\<in>Basis. \<bar>f x\<bullet>i\<bar> *\<^sub>R i)::'m) \<bullet> i"
  show "f absolutely_integrable_on UNIV"
    apply (rule bounded_variation_absolutely_integrable[OF assms(1), where B="?B"])
    apply safe
  proof goal_cases
    case d: (1 d)
    note d'=division_ofD[OF d]
    have "(\<Sum>k\<in>d. norm (integral k f)) \<le>
      (\<Sum>k\<in>d. setsum (op \<bullet> (integral k (\<lambda>x. (\<Sum>i\<in>Basis. \<bar>f x\<bullet>i\<bar> *\<^sub>R i)::'m))) Basis)"
      apply (rule setsum_mono)
      apply (rule order_trans[OF norm_le_l1])
      apply (rule setsum_mono)
      unfolding lessThan_iff
    proof -
      fix k
      fix i :: 'm
      assume "k \<in> d" and i: "i \<in> Basis"
      from d'(4)[OF this(1)] guess a b by (elim exE) note ab=this
      show "\<bar>integral k f \<bullet> i\<bar> \<le> integral k (\<lambda>x. (\<Sum>i\<in>Basis. \<bar>f x\<bullet>i\<bar> *\<^sub>R i)::'m) \<bullet> i"
        apply (rule abs_leI)
        unfolding inner_minus_left[symmetric]
        defer
        apply (subst integral_neg[symmetric])
        apply (rule_tac[1-2] integral_component_le[OF i])
        using integrable_on_subcbox[OF assms(1),of a b]
          integrable_on_subcbox[OF assms(2),of a b] i  integrable_neg
        unfolding ab
        apply auto
        done
    qed
    also have "\<dots> \<le> setsum (op \<bullet> (integral UNIV (\<lambda>x. (\<Sum>i\<in>Basis. \<bar>f x\<bullet>i\<bar> *\<^sub>R i)::'m))) Basis"
      apply (subst setsum.commute)
      apply (rule setsum_mono)
    proof goal_cases
      case (1 j)
      have *: "(\<lambda>x. \<Sum>i\<in>Basis. \<bar>f x\<bullet>i\<bar> *\<^sub>R i::'m) integrable_on \<Union>d"
        using integrable_on_subdivision[OF d assms(2)] by auto
      have "(\<Sum>i\<in>d. integral i (\<lambda>x. \<Sum>i\<in>Basis. \<bar>f x\<bullet>i\<bar> *\<^sub>R i::'m) \<bullet> j) =
        integral (\<Union>d) (\<lambda>x. \<Sum>i\<in>Basis. \<bar>f x\<bullet>i\<bar> *\<^sub>R i::'m) \<bullet> j"
        unfolding inner_setsum_left[symmetric] integral_combine_division_topdown[OF * d] ..
      also have "\<dots> \<le> integral UNIV (\<lambda>x. \<Sum>i\<in>Basis. \<bar>f x\<bullet>i\<bar> *\<^sub>R i::'m) \<bullet> j"
        apply (rule integral_subset_component_le)
        using assms * \<open>j \<in> Basis\<close>
        apply auto
        done
      finally show ?case .
    qed
    finally show ?case .
  qed
qed

lemma nonnegative_absolutely_integrable:
  fixes f :: "'n::euclidean_space \<Rightarrow> 'm::euclidean_space"
  assumes "\<forall>x\<in>s. \<forall>i\<in>Basis. 0 \<le> f x \<bullet> i"
    and "f integrable_on s"
  shows "f absolutely_integrable_on s"
  unfolding absolutely_integrable_abs_eq
  apply rule
  apply (rule assms)thm integrable_eq
  apply (rule integrable_eq[of _ f])
  using assms
  apply (auto simp: euclidean_eq_iff[where 'a='m])
  done

lemma absolutely_integrable_integrable_bound:
  fixes f :: "'n::euclidean_space \<Rightarrow> 'm::euclidean_space"
  assumes "\<forall>x\<in>s. norm (f x) \<le> g x"
    and "f integrable_on s"
    and "g integrable_on s"
  shows "f absolutely_integrable_on s"
proof -
  {
    presume *: "\<And>f::'n \<Rightarrow> 'm. \<And>g. \<forall>x. norm (f x) \<le> g x \<Longrightarrow> f integrable_on UNIV \<Longrightarrow>
      g integrable_on UNIV \<Longrightarrow> f absolutely_integrable_on UNIV"
    show ?thesis
      apply (subst absolutely_integrable_restrict_univ[symmetric])
      apply (rule *[of _ "\<lambda>x. if x\<in>s then g x else 0"])
      using assms
      unfolding integrable_restrict_univ
      apply auto
      done
  }
  fix g
  fix f :: "'n \<Rightarrow> 'm"
  assume assms: "\<forall>x. norm (f x) \<le> g x" "f integrable_on UNIV" "g integrable_on UNIV"
  show "f absolutely_integrable_on UNIV"
    apply (rule bounded_variation_absolutely_integrable[OF assms(2),where B="integral UNIV g"])
    apply safe
  proof goal_cases
    case d: (1 d)
    note d'=division_ofD[OF d]
    have "(\<Sum>k\<in>d. norm (integral k f)) \<le> (\<Sum>k\<in>d. integral k g)"
      apply (rule setsum_mono)
      apply (rule integral_norm_bound_integral)
      apply (drule_tac[!] d'(4))
      apply safe
      apply (rule_tac[1-2] integrable_on_subcbox)
      using assms
      apply auto
      done
    also have "\<dots> = integral (\<Union>d) g"
      apply (rule integral_combine_division_bottomup[symmetric])
      apply (rule d)
      apply safe
      apply (drule d'(4))
      apply safe
      apply (rule integrable_on_subcbox[OF assms(3)])
      apply auto
      done
    also have "\<dots> \<le> integral UNIV g"
      apply (rule integral_subset_le)
      defer
      apply (rule integrable_on_subdivision[OF d,of _ UNIV])
      prefer 4
      apply rule
      apply (rule_tac y="norm (f x)" in order_trans)
      using assms
      apply auto
      done
    finally show ?case .
  qed
qed

lemma absolutely_integrable_absolutely_integrable_bound:
  fixes f :: "'n::euclidean_space \<Rightarrow> 'm::euclidean_space"
    and g :: "'n::euclidean_space \<Rightarrow> 'p::euclidean_space"
  assumes "\<forall>x\<in>s. norm (f x) \<le> norm (g x)"
    and "f integrable_on s"
    and "g absolutely_integrable_on s"
  shows "f absolutely_integrable_on s"
  apply (rule absolutely_integrable_integrable_bound[of s f "\<lambda>x. norm (g x)"])
  using assms
  apply auto
  done

lemma absolutely_integrable_inf_real:
  assumes "finite k"
    and "k \<noteq> {}"
    and "\<forall>i\<in>k. (\<lambda>x. (fs x i)::real) absolutely_integrable_on s"
  shows "(\<lambda>x. (Inf ((fs x) ` k))) absolutely_integrable_on s"
  using assms
proof induct
  case (insert a k)
  let ?P = "(\<lambda>x.
    if fs x ` k = {} then fs x a
    else min (fs x a) (Inf (fs x ` k))) absolutely_integrable_on s"
  show ?case
    unfolding image_insert
    apply (subst Inf_insert_finite)
    apply (rule finite_imageI[OF insert(1)])
  proof (cases "k = {}")
    case True
    then show ?P
      apply (subst if_P)
      defer
      apply (rule insert(5)[rule_format])
      apply auto
      done
  next
    case False
    then show ?P
      apply (subst if_not_P)
      defer
      apply (rule absolutely_integrable_min[where 'n=real, unfolded Basis_real_def, simplified])
      defer
      apply(rule insert(3)[OF False])
      using insert(5)
      apply auto
      done
  qed
next
  case empty
  then show ?case by auto
qed

lemma absolutely_integrable_sup_real:
  assumes "finite k"
    and "k \<noteq> {}"
    and "\<forall>i\<in>k. (\<lambda>x. (fs x i)::real) absolutely_integrable_on s"
  shows "(\<lambda>x. (Sup ((fs x) ` k))) absolutely_integrable_on s"
  using assms
proof induct
  case (insert a k)
  let ?P = "(\<lambda>x.
    if fs x ` k = {} then fs x a
    else max (fs x a) (Sup (fs x ` k))) absolutely_integrable_on s"
  show ?case
    unfolding image_insert
    apply (subst Sup_insert_finite)
    apply (rule finite_imageI[OF insert(1)])
  proof (cases "k = {}")
    case True
    then show ?P
      apply (subst if_P)
      defer
      apply (rule insert(5)[rule_format])
      apply auto
      done
  next
    case False
    then show ?P
      apply (subst if_not_P)
      defer
      apply (rule absolutely_integrable_max[where 'n=real, unfolded Basis_real_def, simplified])
      defer
      apply (rule insert(3)[OF False])
      using insert(5)
      apply auto
      done
  qed
qed auto


subsection \<open>differentiation under the integral sign\<close>

lemma tube_lemma:
  assumes "compact K"
  assumes "open W"
  assumes "{x0} \<times> K \<subseteq> W"
  shows "\<exists>X0. x0 \<in> X0 \<and> open X0 \<and> X0 \<times> K \<subseteq> W"
proof -
  {
    fix y assume "y \<in> K"
    then have "(x0, y) \<in> W" using assms by auto
    with \<open>open W\<close>
    have "\<exists>X0 Y. open X0 \<and> open Y \<and> x0 \<in> X0 \<and> y \<in> Y \<and> X0 \<times> Y \<subseteq> W"
      by (rule open_prod_elim) blast
  }
  then obtain X0 Y where
    *: "\<forall>y \<in> K. open (X0 y) \<and> open (Y y) \<and> x0 \<in> X0 y \<and> y \<in> Y y \<and> X0 y \<times> Y y \<subseteq> W"
    by metis
  from * have "\<forall>t\<in>Y ` K. open t" "K \<subseteq> \<Union>(Y ` K)" by auto
  with \<open>compact K\<close> obtain CC where CC: "CC \<subseteq> Y ` K" "finite CC" "K \<subseteq> \<Union>CC"
    by (rule compactE)
  then obtain c where c: "\<And>C. C \<in> CC \<Longrightarrow> c C \<in> K \<and> C = Y (c C)"
    by (force intro!: choice)
  with * CC show ?thesis
    by (force intro!: exI[where x="\<Inter>C\<in>CC. X0 (c C)"]) (* SLOW *)
qed

lemma continuous_on_prod_compactE:
  fixes fx::"'a::topological_space \<times> 'b::topological_space \<Rightarrow> 'c::metric_space"
    and e::real
  assumes cont_fx: "continuous_on (U \<times> C) fx"
  assumes "compact C"
  assumes [intro]: "x0 \<in> U"
  notes [continuous_intros] = continuous_on_compose2[OF cont_fx]
  assumes "e > 0"
  obtains X0 where "x0 \<in> X0" "open X0"
    "\<forall>x\<in>X0 \<inter> U. \<forall>t \<in> C. dist (fx (x, t)) (fx (x0, t)) \<le> e"
proof -
  define psi where "psi = (\<lambda>(x, t). dist (fx (x, t)) (fx (x0, t)))"
  define W0 where "W0 = {(x, t) \<in> U \<times> C. psi (x, t) < e}"
  have W0_eq: "W0 = psi -` {..<e} \<inter> U \<times> C"
    by (auto simp: vimage_def W0_def)
  have "open {..<e}" by simp
  have "continuous_on (U \<times> C) psi"
    by (auto intro!: continuous_intros simp: psi_def split_beta')
  from this[unfolded continuous_on_open_invariant, rule_format, OF \<open>open {..<e}\<close>]
  obtain W where W: "open W" "W \<inter> U \<times> C = W0 \<inter> U \<times> C"
    unfolding W0_eq by blast
  have "{x0} \<times> C \<subseteq> W \<inter> U \<times> C"
    unfolding W
    by (auto simp: W0_def psi_def \<open>0 < e\<close>)
  then have "{x0} \<times> C \<subseteq> W" by blast
  from tube_lemma[OF \<open>compact C\<close> \<open>open W\<close> this]
  obtain X0 where X0: "x0 \<in> X0" "open X0" "X0 \<times> C \<subseteq> W"
    by blast

  have "\<forall>x\<in>X0 \<inter> U. \<forall>t \<in> C. dist (fx (x, t)) (fx (x0, t)) \<le> e"
  proof safe
    fix x assume x: "x \<in> X0" "x \<in> U"
    fix t assume t: "t \<in> C"
    have "dist (fx (x, t)) (fx (x0, t)) = psi (x, t)"
      by (auto simp: psi_def)
    also
    {
      have "(x, t) \<in> X0 \<times> C"
        using t x
        by auto
      also note \<open>\<dots> \<subseteq> W\<close>
      finally have "(x, t) \<in> W" .
      with t x have "(x, t) \<in> W \<inter> U \<times> C"
        by blast
      also note \<open>W \<inter> U \<times> C = W0 \<inter> U \<times> C\<close>
      finally  have "psi (x, t) < e"
        by (auto simp: W0_def)
    }
    finally show "dist (fx (x, t)) (fx (x0, t)) \<le> e" by simp
  qed
  from X0(1,2) this show ?thesis ..
qed

lemma integral_continuous_on_param:
  fixes f::"'a::topological_space \<Rightarrow> 'b::euclidean_space \<Rightarrow> 'c::banach"
  assumes cont_fx: "continuous_on (U \<times> cbox a b) (\<lambda>(x, t). f x t)"
  shows "continuous_on U (\<lambda>x. integral (cbox a b) (f x))"
proof cases
  assume "content (cbox a b) \<noteq> 0"
  then have ne: "cbox a b \<noteq> {}" by auto

  note [continuous_intros] =
    continuous_on_compose2[OF cont_fx, where f="\<lambda>y. Pair x y" for x,
      unfolded split_beta fst_conv snd_conv]

  show ?thesis
    unfolding continuous_on_def
  proof (safe intro!: tendstoI)
    fix e'::real and x
    assume "e' > 0"
    define e where "e = e' / (content (cbox a b) + 1)"
    have "e > 0" using \<open>e' > 0\<close> by (auto simp: e_def intro!: divide_pos_pos add_nonneg_pos)
    assume "x \<in> U"
    from continuous_on_prod_compactE[OF cont_fx compact_cbox \<open>x \<in> U\<close> \<open>0 < e\<close>]
    obtain X0 where X0: "x \<in> X0" "open X0"
      and fx_bound: "\<And>y t. y \<in> X0 \<inter> U \<Longrightarrow> t \<in> cbox a b \<Longrightarrow> norm (f y t - f x t) \<le> e"
      unfolding split_beta fst_conv snd_conv dist_norm
      by metis
    have "\<forall>\<^sub>F y in at x within U. y \<in> X0 \<inter> U"
      using X0(1) X0(2) eventually_at_topological by auto
    then show "\<forall>\<^sub>F y in at x within U. dist (integral (cbox a b) (f y)) (integral (cbox a b) (f x)) < e'"
    proof eventually_elim
      case (elim y)
      have "dist (integral (cbox a b) (f y)) (integral (cbox a b) (f x)) =
        norm (integral (cbox a b) (\<lambda>t. f y t - f x t))"
        using elim \<open>x \<in> U\<close>
        unfolding dist_norm
        by (subst integral_diff)
           (auto intro!: integrable_continuous continuous_intros)
      also have "\<dots> \<le> e * content (cbox a b)"
        using elim \<open>x \<in> U\<close>
        by (intro integrable_bound)
           (auto intro!: fx_bound \<open>x \<in> U \<close> less_imp_le[OF \<open>0 < e\<close>]
              integrable_continuous continuous_intros)
      also have "\<dots> < e'"
        using \<open>0 < e'\<close> \<open>e > 0\<close>
        by (auto simp: e_def divide_simps)
      finally show "dist (integral (cbox a b) (f y)) (integral (cbox a b) (f x)) < e'" .
    qed
  qed
qed (auto intro!: continuous_on_const)

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

lemma leibniz_rule:
  fixes f::"'a::banach \<Rightarrow> 'b::euclidean_space \<Rightarrow> 'c::banach"
  assumes fx: "\<And>x t. x \<in> U \<Longrightarrow> t \<in> cbox a b \<Longrightarrow>
    ((\<lambda>x. f x t) has_derivative blinfun_apply (fx x t)) (at x within U)"
  assumes integrable_f2: "\<And>x. x \<in> U \<Longrightarrow> f x integrable_on cbox a b"
  assumes cont_fx: "continuous_on (U \<times> (cbox a b)) (\<lambda>(x, t). fx x t)"
  assumes [intro]: "x0 \<in> U"
  assumes "convex U"
  shows
    "((\<lambda>x. integral (cbox a b) (f x)) has_derivative integral (cbox a b) (fx x0)) (at x0 within U)"
    (is "(?F has_derivative ?dF) _")
proof cases
  assume "content (cbox a b) \<noteq> 0"
  then have ne: "cbox a b \<noteq> {}" by auto
  note [continuous_intros] =
    continuous_on_compose2[OF cont_fx, where f="\<lambda>y. Pair x y" for x,
      unfolded split_beta fst_conv snd_conv]
  show ?thesis
  proof (intro has_derivativeI bounded_linear_scaleR_left tendstoI, fold norm_conv_dist)
    have cont_f1: "\<And>t. t \<in> cbox a b \<Longrightarrow> continuous_on U (\<lambda>x. f x t)"
      by (auto simp: continuous_on_eq_continuous_within intro!: has_derivative_continuous fx)
    note [continuous_intros] = continuous_on_compose2[OF cont_f1]
    fix e'::real
    assume "e' > 0"
    define e where "e = e' / (content (cbox a b) + 1)"
    have "e > 0" using \<open>e' > 0\<close> by (auto simp: e_def intro!: divide_pos_pos add_nonneg_pos)
    from continuous_on_prod_compactE[OF cont_fx compact_cbox \<open>x0 \<in> U\<close> \<open>e > 0\<close>]
    obtain X0 where X0: "x0 \<in> X0" "open X0"
      and fx_bound: "\<And>x t. x \<in> X0 \<inter> U \<Longrightarrow> t \<in> cbox a b \<Longrightarrow> norm (fx x t - fx x0 t) \<le> e"
      unfolding split_beta fst_conv snd_conv
      by (metis dist_norm)

    note eventually_closed_segment[OF \<open>open X0\<close> \<open>x0 \<in> X0\<close>, of U]
    moreover
    have "\<forall>\<^sub>F x in at x0 within U. x \<in> X0"
      using \<open>open X0\<close> \<open>x0 \<in> X0\<close> eventually_at_topological by blast
    moreover have "\<forall>\<^sub>F x in at x0 within U. x \<noteq> x0"
      by (auto simp: eventually_at_filter)
    moreover have "\<forall>\<^sub>F x in at x0 within U. x \<in> U"
      by (auto simp: eventually_at_filter)
    ultimately
    show "\<forall>\<^sub>F x in at x0 within U. norm ((?F x - ?F x0 - ?dF (x - x0)) /\<^sub>R norm (x - x0)) < e'"
    proof eventually_elim
      case (elim x)
      from elim have "0 < norm (x - x0)" by simp
      have "closed_segment x0 x \<subseteq> U"
        by (rule \<open>convex U\<close>[unfolded convex_contains_segment, rule_format, OF \<open>x0 \<in> U\<close> \<open>x \<in> U\<close>])
      from elim have [intro]: "x \<in> U" by auto

      have "?F x - ?F x0 - ?dF (x - x0) =
        integral (cbox a b) (\<lambda>y. f x y - f x0 y - fx x0 y (x - x0))"
        (is "_ = ?id")
        using \<open>x \<noteq> x0\<close>
        by (subst blinfun_apply_integral integral_diff,
            auto intro!: integrable_diff integrable_f2 continuous_intros
              intro: integrable_continuous)+
      also
      {
        fix t assume t: "t \<in> (cbox a b)"
        have seg: "\<And>t. t \<in> {0..1} \<Longrightarrow> x0 + t *\<^sub>R (x - x0) \<in> X0 \<inter> U"
          using \<open>closed_segment x0 x \<subseteq> U\<close>
            \<open>closed_segment x0 x \<subseteq> X0\<close>
          by (force simp: closed_segment_def algebra_simps)
        from t have deriv:
          "((\<lambda>x. f x t) has_derivative (fx y t)) (at y within X0 \<inter> U)"
          if "y \<in> X0 \<inter> U" for y
          unfolding has_vector_derivative_def[symmetric]
          using that \<open>x \<in> X0\<close>
          by (intro has_derivative_within_subset[OF fx]) auto
        have "\<forall>x \<in> X0 \<inter> U. onorm (blinfun_apply (fx x t) - (fx x0 t)) \<le> e"
          using fx_bound t
          by (auto simp add: norm_blinfun_def fun_diff_def blinfun.bilinear_simps[symmetric])
        from differentiable_bound_linearization[OF seg deriv this] X0
        have "norm (f x t - f x0 t - fx x0 t (x - x0)) \<le> e * norm (x - x0)"
          by (auto simp add: ac_simps)
      }
      then have "norm ?id \<le> integral (cbox a b) (\<lambda>_. e * norm (x - x0))"
        by (intro integral_norm_bound_integral)
          (auto intro!: continuous_intros integrable_diff integrable_f2
            intro: integrable_continuous)
      also have "\<dots> = content (cbox a b) * e * norm (x - x0)"
        by simp
      also have "\<dots> < e' * norm (x - x0)"
        using \<open>e' > 0\<close> content_pos_le[of a b]
        by (intro mult_strict_right_mono[OF _ \<open>0 < norm (x - x0)\<close>])
           (auto simp: divide_simps e_def simp del: measure_nonneg)
      finally have "norm (?F x - ?F x0 - ?dF (x - x0)) < e' * norm (x - x0)" .
      then show ?case
        by (auto simp: divide_simps)
    qed
  qed (rule blinfun.bounded_linear_right)
qed (auto intro!: derivative_eq_intros simp: blinfun.bilinear_simps)

lemma
  has_vector_derivative_eq_has_derivative_blinfun:
  "(f has_vector_derivative f') (at x within U) \<longleftrightarrow>
    (f has_derivative blinfun_scaleR_left f') (at x within U)"
  by (simp add: has_vector_derivative_def)

lemma leibniz_rule_vector_derivative:
  fixes f::"real \<Rightarrow> 'b::euclidean_space \<Rightarrow> 'c::banach"
  assumes fx: "\<And>x t. x \<in> U \<Longrightarrow> t \<in> cbox a b \<Longrightarrow>
      ((\<lambda>x. f x t) has_vector_derivative (fx x t)) (at x within U)"
  assumes integrable_f2: "\<And>x. x \<in> U \<Longrightarrow> (f x) integrable_on cbox a b"
  assumes cont_fx: "continuous_on (U \<times> cbox a b) (\<lambda>(x, t). fx x t)"
  assumes U: "x0 \<in> U" "convex U"
  shows "((\<lambda>x. integral (cbox a b) (f x)) has_vector_derivative integral (cbox a b) (fx x0))
      (at x0 within U)"
proof -
  note [continuous_intros] =
    continuous_on_compose2[OF cont_fx, where f="\<lambda>y. Pair x y" for x,
      unfolded split_beta fst_conv snd_conv]
  have *: "blinfun_scaleR_left (integral (cbox a b) (fx x0)) =
    integral (cbox a b) (\<lambda>t. blinfun_scaleR_left (fx x0 t))"
    by (subst integral_linear[symmetric])
       (auto simp: has_vector_derivative_def o_def
         intro!: integrable_continuous U continuous_intros bounded_linear_intros)
  show ?thesis
    unfolding has_vector_derivative_eq_has_derivative_blinfun
    apply (rule has_derivative_eq_rhs)
    apply (rule leibniz_rule[OF _ integrable_f2 _ U, where fx="\<lambda>x t. blinfun_scaleR_left (fx x t)"])
    using fx cont_fx
    apply (auto simp: has_vector_derivative_def * split_beta intro!: continuous_intros)
    done
qed

lemma
  has_field_derivative_eq_has_derivative_blinfun:
  "(f has_field_derivative f') (at x within U) \<longleftrightarrow> (f has_derivative blinfun_mult_right f') (at x within U)"
  by (simp add: has_field_derivative_def)

lemma leibniz_rule_field_derivative:
  fixes f::"'a::{real_normed_field, banach} \<Rightarrow> 'b::euclidean_space \<Rightarrow> 'a"
  assumes fx: "\<And>x t. x \<in> U \<Longrightarrow> t \<in> cbox a b \<Longrightarrow> ((\<lambda>x. f x t) has_field_derivative fx x t) (at x within U)"
  assumes integrable_f2: "\<And>x. x \<in> U \<Longrightarrow> (f x) integrable_on cbox a b"
  assumes cont_fx: "continuous_on (U \<times> (cbox a b)) (\<lambda>(x, t). fx x t)"
  assumes U: "x0 \<in> U" "convex U"
  shows "((\<lambda>x. integral (cbox a b) (f x)) has_field_derivative integral (cbox a b) (fx x0)) (at x0 within U)"
proof -
  note [continuous_intros] =
    continuous_on_compose2[OF cont_fx, where f="\<lambda>y. Pair x y" for x,
      unfolded split_beta fst_conv snd_conv]
  have *: "blinfun_mult_right (integral (cbox a b) (fx x0)) =
    integral (cbox a b) (\<lambda>t. blinfun_mult_right (fx x0 t))"
    by (subst integral_linear[symmetric])
      (auto simp: has_vector_derivative_def o_def
        intro!: integrable_continuous U continuous_intros bounded_linear_intros)
  show ?thesis
    unfolding has_field_derivative_eq_has_derivative_blinfun
    apply (rule has_derivative_eq_rhs)
    apply (rule leibniz_rule[OF _ integrable_f2 _ U, where fx="\<lambda>x t. blinfun_mult_right (fx x t)"])
    using fx cont_fx
    apply (auto simp: has_field_derivative_def * split_beta intro!: continuous_intros)
    done
qed


subsection \<open>Exchange uniform limit and integral\<close>

lemma
  uniform_limit_integral:
  fixes f::"'a \<Rightarrow> 'b::euclidean_space \<Rightarrow> 'c::banach"
  assumes u: "uniform_limit (cbox a b) f g F"
  assumes c: "\<And>n. continuous_on (cbox a b) (f n)"
  assumes [simp]: "F \<noteq> bot"
  obtains I J where
    "\<And>n. (f n has_integral I n) (cbox a b)"
    "(g has_integral J) (cbox a b)"
    "(I \<longlongrightarrow> J) F"
proof -
  have fi[simp]: "f n integrable_on (cbox a b)" for n
    by (auto intro!: integrable_continuous assms)
  then obtain I where I: "\<And>n. (f n has_integral I n) (cbox a b)"
    by atomize_elim (auto simp: integrable_on_def intro!: choice)

  moreover

  have gi[simp]: "g integrable_on (cbox a b)"
    by (auto intro!: integrable_continuous uniform_limit_theorem[OF _ u] eventuallyI c)
  then obtain J where J: "(g has_integral J) (cbox a b)"
    by blast

  moreover

  have "(I \<longlongrightarrow> J) F"
  proof cases
    assume "content (cbox a b) = 0"
    hence "I = (\<lambda>_. 0)" "J = 0"
      by (auto intro!: has_integral_unique I J)
    thus ?thesis by simp
  next
    assume content_nonzero: "content (cbox a b) \<noteq> 0"
    show ?thesis
    proof (rule tendstoI)
      fix e::real
      assume "e > 0"
      define e' where "e' = e / 2"
      with \<open>e > 0\<close> have "e' > 0" by simp
      then have "\<forall>\<^sub>F n in F. \<forall>x\<in>cbox a b. norm (f n x - g x) < e' / content (cbox a b)"
        using u content_nonzero content_pos_le[of a b]
        by (auto simp: uniform_limit_iff dist_norm simp del: measure_nonneg)
      then show "\<forall>\<^sub>F n in F. dist (I n) J < e"
      proof eventually_elim
        case (elim n)
        have "I n = integral (cbox a b) (f n)"
            "J = integral (cbox a b) g"
          using I[of n] J by (simp_all add: integral_unique)
        then have "dist (I n) J = norm (integral (cbox a b) (\<lambda>x. f n x - g x))"
          by (simp add: integral_diff dist_norm)
        also have "\<dots> \<le> integral (cbox a b) (\<lambda>x. (e' / content (cbox a b)))"
          using elim
          by (intro integral_norm_bound_integral)
            (auto intro!: integrable_diff absolutely_integrable_onI)
        also have "\<dots> < e"
          using \<open>0 < e\<close>
          by (simp add: e'_def)
        finally show ?case .
      qed
    qed
  qed
  ultimately show ?thesis ..
qed


subsection \<open>Dominated convergence\<close>

context
begin

private lemma dominated_convergence_real:
  fixes f :: "nat \<Rightarrow> 'n::euclidean_space \<Rightarrow> real"
  assumes "\<And>k. (f k) integrable_on s" "h integrable_on s"
    and "\<And>k. \<forall>x \<in> s. norm (f k x) \<le> h x"
    and "\<forall>x \<in> s. ((\<lambda>k. f k x) \<longlongrightarrow> g x) sequentially"
  shows "g integrable_on s \<and> ((\<lambda>k. integral s (f k)) \<longlongrightarrow> integral s g) sequentially"
proof
  have bdd_below[simp]: "\<And>x P. x \<in> s \<Longrightarrow> bdd_below {f n x |n. P n}"
  proof (safe intro!: bdd_belowI)
    fix n x show "x \<in> s \<Longrightarrow> - h x \<le> f n x"
      using assms(3)[rule_format, of x n] by simp
  qed
  have bdd_above[simp]: "\<And>x P. x \<in> s \<Longrightarrow> bdd_above {f n x |n. P n}"
  proof (safe intro!: bdd_aboveI)
    fix n x show "x \<in> s \<Longrightarrow> f n x \<le> h x"
      using assms(3)[rule_format, of x n] by simp
  qed

  have "\<And>m. (\<lambda>x. Inf {f j x |j. m \<le> j}) integrable_on s \<and>
    ((\<lambda>k. integral s (\<lambda>x. Inf {f j x |j. j \<in> {m..m + k}})) \<longlongrightarrow>
    integral s (\<lambda>x. Inf {f j x |j. m \<le> j}))sequentially"
  proof (rule monotone_convergence_decreasing, safe)
    fix m :: nat
    show "bounded {integral s (\<lambda>x. Inf {f j x |j. j \<in> {m..m + k}}) |k. True}"
      unfolding bounded_iff
      apply (rule_tac x="integral s h" in exI)
    proof safe
      fix k :: nat
      show "norm (integral s (\<lambda>x. Inf {f j x |j. j \<in> {m..m + k}})) \<le> integral s h"
        apply (rule integral_norm_bound_integral)
        unfolding Setcompr_eq_image
        apply (rule absolutely_integrable_onD)
        apply (rule absolutely_integrable_inf_real)
        prefer 5
        unfolding real_norm_def
        apply rule
        apply (rule cInf_abs_ge)
        prefer 5
        apply rule
        apply (rule_tac g = h in absolutely_integrable_integrable_bound)
        using assms
        unfolding real_norm_def
        apply auto
        done
    qed
    fix k :: nat
    show "(\<lambda>x. Inf {f j x |j. j \<in> {m..m + k}}) integrable_on s"
      unfolding Setcompr_eq_image
      apply (rule absolutely_integrable_onD)
      apply (rule absolutely_integrable_inf_real)
      prefer 3
      using absolutely_integrable_integrable_bound[OF assms(3,1,2)]
      apply auto
      done
    fix x
    assume x: "x \<in> s"
    show "Inf {f j x |j. j \<in> {m..m + Suc k}} \<le> Inf {f j x |j. j \<in> {m..m + k}}"
      by (rule cInf_superset_mono) auto
    let ?S = "{f j x| j. m \<le> j}"
    show "((\<lambda>k. Inf {f j x |j. j \<in> {m..m + k}}) \<longlongrightarrow> Inf ?S) sequentially"
    proof (rule LIMSEQ_I, goal_cases)
      case r: (1 r)

      have "\<exists>y\<in>?S. y < Inf ?S + r"
        by (subst cInf_less_iff[symmetric]) (auto simp: \<open>x\<in>s\<close> r)
      then obtain N where N: "f N x < Inf ?S + r" "m \<le> N"
        by blast

      show ?case
        apply (rule_tac x=N in exI)
        apply safe
      proof goal_cases
        case prems: (1 n)
        have *: "\<And>y ix. y < Inf ?S + r \<longrightarrow> Inf ?S \<le> ix \<longrightarrow> ix \<le> y \<longrightarrow> \<bar>ix - Inf ?S\<bar> < r"
          by arith
        show ?case
          unfolding real_norm_def
            apply (rule *[rule_format, OF N(1)])
            apply (rule cInf_superset_mono, auto simp: \<open>x\<in>s\<close>) []
            apply (rule cInf_lower)
            using N prems
            apply auto []
            apply simp
            done
      qed
    qed
  qed
  note dec1 = conjunctD2[OF this]

  have "\<And>m. (\<lambda>x. Sup {f j x |j. m \<le> j}) integrable_on s \<and>
    ((\<lambda>k. integral s (\<lambda>x. Sup {f j x |j. j \<in> {m..m + k}})) \<longlongrightarrow>
    integral s (\<lambda>x. Sup {f j x |j. m \<le> j})) sequentially"
  proof (rule monotone_convergence_increasing,safe)
    fix m :: nat
    show "bounded {integral s (\<lambda>x. Sup {f j x |j. j \<in> {m..m + k}}) |k. True}"
      unfolding bounded_iff
      apply (rule_tac x="integral s h" in exI)
    proof safe
      fix k :: nat
      show "norm (integral s (\<lambda>x. Sup {f j x |j. j \<in> {m..m + k}})) \<le> integral s h"
        apply (rule integral_norm_bound_integral) unfolding Setcompr_eq_image
        apply (rule absolutely_integrable_onD)
        apply(rule absolutely_integrable_sup_real)
        prefer 5 unfolding real_norm_def
        apply rule
        apply (rule cSup_abs_le)
        using assms
        apply (force simp add: )
        prefer 4
        apply rule
        apply (rule_tac g=h in absolutely_integrable_integrable_bound)
        using assms
        unfolding real_norm_def
        apply auto
        done
    qed
    fix k :: nat
    show "(\<lambda>x. Sup {f j x |j. j \<in> {m..m + k}}) integrable_on s"
      unfolding Setcompr_eq_image
      apply (rule absolutely_integrable_onD)
      apply (rule absolutely_integrable_sup_real)
      prefer 3
      using absolutely_integrable_integrable_bound[OF assms(3,1,2)]
      apply auto
      done
    fix x
    assume x: "x\<in>s"
    show "Sup {f j x |j. j \<in> {m..m + Suc k}} \<ge> Sup {f j x |j. j \<in> {m..m + k}}"
      by (rule cSup_subset_mono) auto
    let ?S = "{f j x| j. m \<le> j}"
    show "((\<lambda>k. Sup {f j x |j. j \<in> {m..m + k}}) \<longlongrightarrow> Sup ?S) sequentially"
    proof (rule LIMSEQ_I, goal_cases)
      case r: (1 r)
      have "\<exists>y\<in>?S. Sup ?S - r < y"
        by (subst less_cSup_iff[symmetric]) (auto simp: r \<open>x\<in>s\<close>)
      then obtain N where N: "Sup ?S - r < f N x" "m \<le> N"
        by blast

      show ?case
        apply (rule_tac x=N in exI)
        apply safe
      proof goal_cases
        case prems: (1 n)
        have *: "\<And>y ix. Sup ?S - r < y \<longrightarrow> ix \<le> Sup ?S \<longrightarrow> y \<le> ix \<longrightarrow> \<bar>ix - Sup ?S\<bar> < r"
          by arith
        show ?case
          apply simp
          apply (rule *[rule_format, OF N(1)])
          apply (rule cSup_subset_mono, auto simp: \<open>x\<in>s\<close>) []
          apply (subst cSup_upper)
          using N prems
          apply auto
          done
      qed
    qed
  qed
  note inc1 = conjunctD2[OF this]

  have "g integrable_on s \<and>
    ((\<lambda>k. integral s (\<lambda>x. Inf {f j x |j. k \<le> j})) \<longlongrightarrow> integral s g) sequentially"
    apply (rule monotone_convergence_increasing,safe)
    apply fact
  proof -
    show "bounded {integral s (\<lambda>x. Inf {f j x |j. k \<le> j}) |k. True}"
      unfolding bounded_iff apply(rule_tac x="integral s h" in exI)
    proof safe
      fix k :: nat
      show "norm (integral s (\<lambda>x. Inf {f j x |j. k \<le> j})) \<le> integral s h"
        apply (rule integral_norm_bound_integral)
        apply fact+
        unfolding real_norm_def
        apply rule
        apply (rule cInf_abs_ge)
        using assms(3)
        apply auto
        done
    qed
    fix k :: nat and x
    assume x: "x \<in> s"

    have *: "\<And>x y::real. x \<ge> - y \<Longrightarrow> - x \<le> y" by auto
    show "Inf {f j x |j. k \<le> j} \<le> Inf {f j x |j. Suc k \<le> j}"
      by (intro cInf_superset_mono) (auto simp: \<open>x\<in>s\<close>)

    show "(\<lambda>k::nat. Inf {f j x |j. k \<le> j}) \<longlonglongrightarrow> g x"
    proof (rule LIMSEQ_I, goal_cases)
      case r: (1 r)
      then have "0<r/2"
        by auto
      from assms(4)[THEN bspec, THEN LIMSEQ_D, OF x this] guess N .. note N = this
      show ?case
        apply (rule_tac x=N in exI)
        apply safe
        unfolding real_norm_def
        apply (rule le_less_trans[of _ "r/2"])
        apply (rule cInf_asclose)
        apply safe
        defer
        apply (rule less_imp_le)
        using N r
        apply auto
        done
    qed
  qed
  note inc2 = conjunctD2[OF this]

  have "g integrable_on s \<and>
    ((\<lambda>k. integral s (\<lambda>x. Sup {f j x |j. k \<le> j})) \<longlongrightarrow> integral s g) sequentially"
    apply (rule monotone_convergence_decreasing,safe)
    apply fact
  proof -
    show "bounded {integral s (\<lambda>x. Sup {f j x |j. k \<le> j}) |k. True}"
      unfolding bounded_iff
      apply (rule_tac x="integral s h" in exI)
    proof safe
      fix k :: nat
      show "norm (integral s (\<lambda>x. Sup {f j x |j. k \<le> j})) \<le> integral s h"
        apply (rule integral_norm_bound_integral)
        apply fact+
        unfolding real_norm_def
        apply rule
        apply (rule cSup_abs_le)
        using assms(3)
        apply auto
        done
    qed
    fix k :: nat
    fix x
    assume x: "x \<in> s"

    show "Sup {f j x |j. k \<le> j} \<ge> Sup {f j x |j. Suc k \<le> j}"
      by (rule cSup_subset_mono) (auto simp: \<open>x\<in>s\<close>)
    show "((\<lambda>k. Sup {f j x |j. k \<le> j}) \<longlongrightarrow> g x) sequentially"
    proof (rule LIMSEQ_I, goal_cases)
      case r: (1 r)
      then have "0<r/2"
        by auto
      from assms(4)[THEN bspec, THEN LIMSEQ_D, OF x this] guess N .. note N=this
      show ?case
        apply (rule_tac x=N in exI,safe)
        unfolding real_norm_def
        apply (rule le_less_trans[of _ "r/2"])
        apply (rule cSup_asclose)
        apply safe
        defer
        apply (rule less_imp_le)
        using N r
        apply auto
        done
    qed
  qed
  note dec2 = conjunctD2[OF this]

  show "g integrable_on s" by fact
  show "((\<lambda>k. integral s (f k)) \<longlongrightarrow> integral s g) sequentially"
  proof (rule LIMSEQ_I, goal_cases)
    case r: (1 r)
    from LIMSEQ_D [OF inc2(2) r] guess N1 .. note N1=this[unfolded real_norm_def]
    from LIMSEQ_D [OF dec2(2) r] guess N2 .. note N2=this[unfolded real_norm_def]
    show ?case
    proof (rule_tac x="N1+N2" in exI, safe)
      fix n
      assume n: "n \<ge> N1 + N2"
      have *: "\<And>i0 i i1 g. \<bar>i0 - g\<bar> < r \<longrightarrow> \<bar>i1 - g\<bar> < r \<longrightarrow> i0 \<le> i \<longrightarrow> i \<le> i1 \<longrightarrow> \<bar>i - g\<bar> < r"
        by arith
      show "norm (integral s (f n) - integral s g) < r"
        unfolding real_norm_def
      proof (rule *[rule_format,OF N1[rule_format] N2[rule_format], of n n])
        show "integral s (\<lambda>x. Inf {f j x |j. n \<le> j}) \<le> integral s (f n)"
          by (rule integral_le[OF dec1(1) assms(1)]) (auto intro!: cInf_lower)
        show "integral s (f n) \<le> integral s (\<lambda>x. Sup {f j x |j. n \<le> j})"
          by (rule integral_le[OF assms(1) inc1(1)]) (auto intro!: cSup_upper)
      qed (insert n, auto)
    qed
  qed
qed

lemma dominated_convergence:
  fixes f :: "nat \<Rightarrow> 'n::euclidean_space \<Rightarrow> 'm::euclidean_space"
  assumes f: "\<And>k. (f k) integrable_on s" and h: "h integrable_on s"
    and le: "\<And>k. \<forall>x \<in> s. norm (f k x) \<le> h x"
    and conv: "\<forall>x \<in> s. ((\<lambda>k. f k x) \<longlongrightarrow> g x) sequentially"
  shows "g integrable_on s"
    and "((\<lambda>k. integral s (f k)) \<longlongrightarrow> integral s g) sequentially"
proof -
  {
    fix b :: 'm assume b: "b \<in> Basis"
    have A: "(\<lambda>x. g x \<bullet> b) integrable_on s \<and>
               (\<lambda>k. integral s (\<lambda>x. f k x \<bullet> b)) \<longlonglongrightarrow> integral s (\<lambda>x. g x \<bullet> b)"
    proof (rule dominated_convergence_real)
      fix k :: nat
      from f show "(\<lambda>x. f k x \<bullet> b) integrable_on s" by (rule integrable_component)
    next
      from h show "h integrable_on s" .
    next
      fix k :: nat
      show "\<forall>x\<in>s. norm (f k x \<bullet> b) \<le> h x"
      proof
        fix x assume x: "x \<in> s"
        have "norm (f k x \<bullet> b) \<le> norm (f k x)" by (simp add: Basis_le_norm b)
        also have "\<dots> \<le> h x" using le[of k] x by simp
        finally show "norm (f k x \<bullet> b) \<le> h x" .
      qed
    next
      from conv show "\<forall>x\<in>s. (\<lambda>k. f k x \<bullet> b) \<longlonglongrightarrow> g x \<bullet> b"
        by (auto intro!: tendsto_inner)
    qed
    have B: "integral s ((\<lambda>x. x *\<^sub>R b) \<circ> (\<lambda>x. f k x \<bullet> b)) = integral s (\<lambda>x. f k x \<bullet> b) *\<^sub>R b"
      for k by (rule integral_linear)
               (simp_all add: f integrable_component bounded_linear_scaleR_left)
    have C: "integral s ((\<lambda>x. x *\<^sub>R b) \<circ> (\<lambda>x. g x \<bullet> b)) = integral s (\<lambda>x. g x \<bullet> b) *\<^sub>R b"
      using A by (intro integral_linear)
                 (simp_all add: integrable_component bounded_linear_scaleR_left)
    note A B C
  } note A = this

  show "g integrable_on s" by (rule integrable_componentwise) (insert A, blast)
  with A f show "((\<lambda>k. integral s (f k)) \<longlongrightarrow> integral s g) sequentially"
    by (subst (1 2) integral_componentwise)
       (auto intro!: tendsto_setsum tendsto_scaleR simp: o_def)
qed

lemma has_integral_dominated_convergence:
  fixes f :: "nat \<Rightarrow> 'n::euclidean_space \<Rightarrow> 'm::euclidean_space"
  assumes "\<And>k. (f k has_integral y k) s" "h integrable_on s"
    "\<And>k. \<forall>x\<in>s. norm (f k x) \<le> h x" "\<forall>x\<in>s. (\<lambda>k. f k x) \<longlonglongrightarrow> g x"
    and x: "y \<longlonglongrightarrow> x"
  shows "(g has_integral x) s"
proof -
  have int_f: "\<And>k. (f k) integrable_on s"
    using assms by (auto simp: integrable_on_def)
  have "(g has_integral (integral s g)) s"
    by (intro integrable_integral dominated_convergence[OF int_f assms(2)]) fact+
  moreover have "integral s g = x"
  proof (rule LIMSEQ_unique)
    show "(\<lambda>i. integral s (f i)) \<longlonglongrightarrow> x"
      using integral_unique[OF assms(1)] x by simp
    show "(\<lambda>i. integral s (f i)) \<longlonglongrightarrow> integral s g"
      by (intro dominated_convergence[OF int_f assms(2)]) fact+
  qed
  ultimately show ?thesis
    by simp
qed

end


subsection \<open>Integration by parts\<close>

lemma integration_by_parts_interior_strong:
  assumes bilinear: "bounded_bilinear (prod :: _ \<Rightarrow> _ \<Rightarrow> 'b :: banach)"
  assumes s: "finite s" and le: "a \<le> b"
  assumes cont [continuous_intros]: "continuous_on {a..b} f" "continuous_on {a..b} g"
  assumes deriv: "\<And>x. x\<in>{a<..<b} - s \<Longrightarrow> (f has_vector_derivative f' x) (at x)"
                 "\<And>x. x\<in>{a<..<b} - s \<Longrightarrow> (g has_vector_derivative g' x) (at x)"
  assumes int: "((\<lambda>x. prod (f x) (g' x)) has_integral
                  (prod (f b) (g b) - prod (f a) (g a) - y)) {a..b}"
  shows   "((\<lambda>x. prod (f' x) (g x)) has_integral y) {a..b}"
proof -
  interpret bounded_bilinear prod by fact
  have "((\<lambda>x. prod (f x) (g' x) + prod (f' x) (g x)) has_integral
          (prod (f b) (g b) - prod (f a) (g a))) {a..b}"
    using deriv by (intro fundamental_theorem_of_calculus_interior_strong[OF s le])
                   (auto intro!: continuous_intros continuous_on has_vector_derivative)
  from has_integral_sub[OF this int] show ?thesis by (simp add: algebra_simps)
qed

lemma integration_by_parts_interior:
  assumes "bounded_bilinear (prod :: _ \<Rightarrow> _ \<Rightarrow> 'b :: banach)" "a \<le> b"
          "continuous_on {a..b} f" "continuous_on {a..b} g"
  assumes "\<And>x. x\<in>{a<..<b} \<Longrightarrow> (f has_vector_derivative f' x) (at x)"
          "\<And>x. x\<in>{a<..<b} \<Longrightarrow> (g has_vector_derivative g' x) (at x)"
  assumes "((\<lambda>x. prod (f x) (g' x)) has_integral (prod (f b) (g b) - prod (f a) (g a) - y)) {a..b}"
  shows   "((\<lambda>x. prod (f' x) (g x)) has_integral y) {a..b}"
  by (rule integration_by_parts_interior_strong[of _ "{}" _ _ f g f' g']) (insert assms, simp_all)

lemma integration_by_parts:
  assumes "bounded_bilinear (prod :: _ \<Rightarrow> _ \<Rightarrow> 'b :: banach)" "a \<le> b"
          "continuous_on {a..b} f" "continuous_on {a..b} g"
  assumes "\<And>x. x\<in>{a..b} \<Longrightarrow> (f has_vector_derivative f' x) (at x)"
          "\<And>x. x\<in>{a..b} \<Longrightarrow> (g has_vector_derivative g' x) (at x)"
  assumes "((\<lambda>x. prod (f x) (g' x)) has_integral (prod (f b) (g b) - prod (f a) (g a) - y)) {a..b}"
  shows   "((\<lambda>x. prod (f' x) (g x)) has_integral y) {a..b}"
  by (rule integration_by_parts_interior[of _ _ _ f g f' g']) (insert assms, simp_all)

lemma integrable_by_parts_interior_strong:
  assumes bilinear: "bounded_bilinear (prod :: _ \<Rightarrow> _ \<Rightarrow> 'b :: banach)"
  assumes s: "finite s" and le: "a \<le> b"
  assumes cont [continuous_intros]: "continuous_on {a..b} f" "continuous_on {a..b} g"
  assumes deriv: "\<And>x. x\<in>{a<..<b} - s \<Longrightarrow> (f has_vector_derivative f' x) (at x)"
                 "\<And>x. x\<in>{a<..<b} - s \<Longrightarrow> (g has_vector_derivative g' x) (at x)"
  assumes int: "(\<lambda>x. prod (f x) (g' x)) integrable_on {a..b}"
  shows   "(\<lambda>x. prod (f' x) (g x)) integrable_on {a..b}"
proof -
  from int obtain I where "((\<lambda>x. prod (f x) (g' x)) has_integral I) {a..b}"
    unfolding integrable_on_def by blast
  hence "((\<lambda>x. prod (f x) (g' x)) has_integral (prod (f b) (g b) - prod (f a) (g a) -
           (prod (f b) (g b) - prod (f a) (g a) - I))) {a..b}" by simp
  from integration_by_parts_interior_strong[OF assms(1-7) this]
    show ?thesis unfolding integrable_on_def by blast
qed

lemma integrable_by_parts_interior:
  assumes "bounded_bilinear (prod :: _ \<Rightarrow> _ \<Rightarrow> 'b :: banach)" "a \<le> b"
          "continuous_on {a..b} f" "continuous_on {a..b} g"
  assumes "\<And>x. x\<in>{a<..<b} \<Longrightarrow> (f has_vector_derivative f' x) (at x)"
          "\<And>x. x\<in>{a<..<b} \<Longrightarrow> (g has_vector_derivative g' x) (at x)"
  assumes "(\<lambda>x. prod (f x) (g' x)) integrable_on {a..b}"
  shows   "(\<lambda>x. prod (f' x) (g x)) integrable_on {a..b}"
  by (rule integrable_by_parts_interior_strong[of _ "{}" _ _ f g f' g']) (insert assms, simp_all)

lemma integrable_by_parts:
  assumes "bounded_bilinear (prod :: _ \<Rightarrow> _ \<Rightarrow> 'b :: banach)" "a \<le> b"
          "continuous_on {a..b} f" "continuous_on {a..b} g"
  assumes "\<And>x. x\<in>{a..b} \<Longrightarrow> (f has_vector_derivative f' x) (at x)"
          "\<And>x. x\<in>{a..b} \<Longrightarrow> (g has_vector_derivative g' x) (at x)"
  assumes "(\<lambda>x. prod (f x) (g' x)) integrable_on {a..b}"
  shows   "(\<lambda>x. prod (f' x) (g x)) integrable_on {a..b}"
  by (rule integrable_by_parts_interior_strong[of _ "{}" _ _ f g f' g']) (insert assms, simp_all)


subsection \<open>Integration by substitution\<close>


lemma has_integral_substitution_strong:
  fixes f :: "real \<Rightarrow> 'a::euclidean_space" and g :: "real \<Rightarrow> real"
  assumes s: "finite s" and le: "a \<le> b" "c \<le> d" "g a \<le> g b"
      and subset: "g ` {a..b} \<subseteq> {c..d}"
      and f [continuous_intros]: "continuous_on {c..d} f"
      and g [continuous_intros]: "continuous_on {a..b} g"
      and deriv [derivative_intros]:
              "\<And>x. x \<in> {a..b} - s \<Longrightarrow> (g has_field_derivative g' x) (at x within {a..b})"
    shows "((\<lambda>x. g' x *\<^sub>R f (g x)) has_integral (integral {g a..g b} f)) {a..b}"
proof -
  let ?F = "\<lambda>x. integral {c..g x} f"
  have cont_int: "continuous_on {a..b} ?F"
    by (rule continuous_on_compose2[OF _ g subset] indefinite_integral_continuous
          f integrable_continuous_real)+
  have deriv: "(((\<lambda>x. integral {c..x} f) \<circ> g) has_vector_derivative g' x *\<^sub>R f (g x))
                 (at x within {a..b})" if "x \<in> {a..b} - s" for x
    apply (rule has_vector_derivative_eq_rhs)
    apply (rule vector_diff_chain_within)
    apply (subst has_field_derivative_iff_has_vector_derivative [symmetric])
    apply (rule deriv that)+
    apply (rule has_vector_derivative_within_subset)
    apply (rule integral_has_vector_derivative f)+
    using that le subset
    apply blast+
    done
  have deriv: "(?F has_vector_derivative g' x *\<^sub>R f (g x))
                  (at x)" if "x \<in> {a..b} - (s \<union> {a,b})" for x
    using deriv[of x] that by (simp add: at_within_closed_interval o_def)


  have "((\<lambda>x. g' x *\<^sub>R f (g x)) has_integral (?F b - ?F a)) {a..b}"
    using le cont_int s deriv cont_int
    by (intro fundamental_theorem_of_calculus_interior_strong[of "s \<union> {a,b}"]) simp_all
  also from subset have "g x \<in> {c..d}" if "x \<in> {a..b}" for x using that by blast
  from this[of a] this[of b] le have "c \<le> g a" "g b \<le> d" by auto
  hence "integral {c..g a} f + integral {g a..g b} f = integral {c..g b} f"
    by (intro integral_combine integrable_continuous_real continuous_on_subset[OF f] le) simp_all
  hence "integral {c..g b} f - integral {c..g a} f = integral {g a..g b} f"
    by (simp add: algebra_simps)
  finally show ?thesis .
qed

lemma has_integral_substitution:
  fixes f :: "real \<Rightarrow> 'a::euclidean_space" and g :: "real \<Rightarrow> real"
  assumes "a \<le> b" "c \<le> d" "g a \<le> g b" "g ` {a..b} \<subseteq> {c..d}"
      and "continuous_on {c..d} f"
      and "\<And>x. x \<in> {a..b} \<Longrightarrow> (g has_field_derivative g' x) (at x within {a..b})"
    shows "((\<lambda>x. g' x *\<^sub>R f (g x)) has_integral (integral {g a..g b} f)) {a..b}"
  by (intro has_integral_substitution_strong[of "{}" a b c d] assms)
     (auto intro: DERIV_continuous_on assms)


subsection \<open>Compute a double integral using iterated integrals and switching the order of integration\<close>

lemma setcomp_dot1: "{z. P (z \<bullet> (i,0))} = {(x,y). P(x \<bullet> i)}"
  by auto

lemma setcomp_dot2: "{z. P (z \<bullet> (0,i))} = {(x,y). P(y \<bullet> i)}"
  by auto

lemma Sigma_Int_Paircomp1: "(Sigma A B) \<inter> {(x, y). P x} = Sigma (A \<inter> {x. P x}) B"
  by blast

lemma Sigma_Int_Paircomp2: "(Sigma A B) \<inter> {(x, y). P y} = Sigma A (\<lambda>z. B z \<inter> {y. P y})"
  by blast

lemma continuous_on_imp_integrable_on_Pair1:
  fixes f :: "_ \<Rightarrow> 'b::banach"
  assumes con: "continuous_on (cbox (a,c) (b,d)) f" and x: "x \<in> cbox a b"
  shows "(\<lambda>y. f (x, y)) integrable_on (cbox c d)"
proof -
  have "f \<circ> (\<lambda>y. (x, y)) integrable_on (cbox c d)"
    apply (rule integrable_continuous)
    apply (rule continuous_on_compose [OF _ continuous_on_subset [OF con]])
    using x
    apply (auto intro: continuous_on_Pair continuous_on_const continuous_on_id continuous_on_subset con)
    done
  then show ?thesis
    by (simp add: o_def)
qed

lemma integral_integrable_2dim:
  fixes f :: "('a::euclidean_space * 'b::euclidean_space) \<Rightarrow> 'c::banach"
  assumes "continuous_on (cbox (a,c) (b,d)) f"
    shows "(\<lambda>x. integral (cbox c d) (\<lambda>y. f (x,y))) integrable_on cbox a b"
proof (cases "content(cbox c d) = 0")
case True
  then show ?thesis
    by (simp add: True integrable_const)
next
  case False
  have uc: "uniformly_continuous_on (cbox (a,c) (b,d)) f"
    by (simp add: assms compact_cbox compact_uniformly_continuous)
  { fix x::'a and e::real
    assume x: "x \<in> cbox a b" and e: "0 < e"
    then have e2_gt: "0 < e / 2 / content (cbox c d)" and e2_less: "e / 2 / content (cbox c d) * content (cbox c d) < e"
      by (auto simp: False content_lt_nz e)
    then obtain dd
    where dd: "\<And>x x'. \<lbrakk>x\<in>cbox (a, c) (b, d); x'\<in>cbox (a, c) (b, d); norm (x' - x) < dd\<rbrakk>
                       \<Longrightarrow> norm (f x' - f x) \<le> e / (2 * content (cbox c d))"  "dd>0"
      using uc [unfolded uniformly_continuous_on_def, THEN spec, of "e / (2 * content (cbox c d))"]
      by (auto simp: dist_norm intro: less_imp_le)
    have "\<exists>delta>0. \<forall>x'\<in>cbox a b. norm (x' - x) < delta \<longrightarrow> norm (integral (cbox c d) (\<lambda>u. f (x', u) - f (x, u))) < e"
      apply (rule_tac x=dd in exI)
      using dd e2_gt assms x
      apply clarify
      apply (rule le_less_trans [OF _ e2_less])
      apply (rule integrable_bound)
      apply (auto intro: integrable_diff continuous_on_imp_integrable_on_Pair1)
      done
  } note * = this
  show ?thesis
    apply (rule integrable_continuous)
    apply (simp add: * continuous_on_iff dist_norm integral_diff [symmetric] continuous_on_imp_integrable_on_Pair1 [OF assms])
    done
qed

lemma norm_diff2: "\<lbrakk>y = y1 + y2; x = x1 + x2; e = e1 + e2; norm(y1 - x1) \<le> e1; norm(y2 - x2) \<le> e2\<rbrakk>
            \<Longrightarrow> norm(y - x) \<le> e"
using norm_triangle_mono [of "y1 - x1" "e1" "y2 - x2" "e2"]
  by (simp add: add_diff_add)

lemma integral_split:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::{real_normed_vector,complete_space}"
  assumes f: "f integrable_on (cbox a b)"
      and k: "k \<in> Basis"
  shows "integral (cbox a b) f =
           integral (cbox a b \<inter> {x. x\<bullet>k \<le> c}) f +
           integral (cbox a b \<inter> {x. x\<bullet>k \<ge> c}) f"
  apply (rule integral_unique [OF has_integral_split [where c=c]])
  using k f
  apply (auto simp: has_integral_integral [symmetric])
  done

lemma integral_swap_operative:
  fixes f :: "('a::euclidean_space * 'b::euclidean_space) \<Rightarrow> 'c::banach"
  assumes f: "continuous_on s f" and e: "0 < e"
    shows "comm_monoid.operative (op \<and>) True
           (\<lambda>k. \<forall>a b c d.
                cbox (a,c) (b,d) \<subseteq> k \<and> cbox (a,c) (b,d) \<subseteq> s
                \<longrightarrow> norm(integral (cbox (a,c) (b,d)) f -
                         integral (cbox a b) (\<lambda>x. integral (cbox c d) (\<lambda>y. f((x,y)))))
                    \<le> e * content (cbox (a,c) (b,d)))"
proof (auto simp: comm_monoid.operative_def[OF comm_monoid_and])
  fix a::'a and c::'b and b::'a and d::'b and u::'a and v::'a and w::'b and z::'b
  assume c0: "content (cbox (a, c) (b, d)) = 0"
     and cb1: "cbox (u, w) (v, z) \<subseteq> cbox (a, c) (b, d)"
     and cb2: "cbox (u, w) (v, z) \<subseteq> s"
  have c0': "content (cbox (u, w) (v, z)) = 0"
    by (fact content_0_subset [OF c0 cb1])
  show "norm (integral (cbox (u,w) (v,z)) f - integral (cbox u v) (\<lambda>x. integral (cbox w z) (\<lambda>y. f (x, y))))
          \<le> e * content (cbox (u,w) (v,z))"
    using content_cbox_pair_eq0_D [OF c0']
    by (force simp add: c0')
next
  fix a::'a and c::'b and b::'a and d::'b
  and M::real and i::'a and j::'b
  and u::'a and v::'a and w::'b and z::'b
  assume ij: "(i,j) \<in> Basis"
     and n1: "\<forall>a' b' c' d'.
                cbox (a',c') (b',d') \<subseteq> cbox (a,c) (b,d) \<and>
                cbox (a',c') (b',d') \<subseteq> {x. x \<bullet> (i,j) \<le> M} \<and> cbox (a',c') (b',d') \<subseteq> s \<longrightarrow>
                norm (integral (cbox (a',c') (b',d')) f - integral (cbox a' b') (\<lambda>x. integral (cbox c' d') (\<lambda>y. f (x,y))))
                \<le> e * content (cbox (a',c') (b',d'))"
     and n2: "\<forall>a' b' c' d'.
                cbox (a',c') (b',d') \<subseteq> cbox (a,c) (b,d) \<and>
                cbox (a',c') (b',d') \<subseteq> {x. M \<le> x \<bullet> (i,j)} \<and> cbox (a',c') (b',d') \<subseteq> s \<longrightarrow>
                norm (integral (cbox (a',c') (b',d')) f - integral (cbox a' b') (\<lambda>x. integral (cbox c' d') (\<lambda>y. f (x,y))))
                \<le> e * content (cbox (a',c') (b',d'))"
     and subs: "cbox (u,w) (v,z) \<subseteq> cbox (a,c) (b,d)"  "cbox (u,w) (v,z) \<subseteq> s"
  have fcont: "continuous_on (cbox (u, w) (v, z)) f"
    using assms(1) continuous_on_subset  subs(2) by blast
  then have fint: "f integrable_on cbox (u, w) (v, z)"
    by (metis integrable_continuous)
  consider "i \<in> Basis" "j=0" | "j \<in> Basis" "i=0"  using ij
    by (auto simp: Euclidean_Space.Basis_prod_def)
  then show "norm (integral (cbox (u,w) (v,z)) f - integral (cbox u v) (\<lambda>x. integral (cbox w z) (\<lambda>y. f (x,y))))
             \<le> e * content (cbox (u,w) (v,z))" (is ?normle)
  proof cases
    case 1
    then have e: "e * content (cbox (u, w) (v, z)) =
                  e * (content (cbox u v \<inter> {x. x \<bullet> i \<le> M}) * content (cbox w z)) +
                  e * (content (cbox u v \<inter> {x. M \<le> x \<bullet> i}) * content (cbox w z))"
      by (simp add: content_split [where c=M] content_Pair algebra_simps)
    have *: "integral (cbox u v) (\<lambda>x. integral (cbox w z) (\<lambda>y. f (x, y))) =
                integral (cbox u v \<inter> {x. x \<bullet> i \<le> M}) (\<lambda>x. integral (cbox w z) (\<lambda>y. f (x, y))) +
                integral (cbox u v \<inter> {x. M \<le> x \<bullet> i}) (\<lambda>x. integral (cbox w z) (\<lambda>y. f (x, y)))"
      using 1 f subs integral_integrable_2dim continuous_on_subset
      by (blast intro: integral_split)
    show ?normle
      apply (rule norm_diff2 [OF integral_split [where c=M, OF fint ij] * e])
      using 1 subs
      apply (simp_all add: cbox_Pair_eq setcomp_dot1 [of "\<lambda>u. M\<le>u"] setcomp_dot1 [of "\<lambda>u. u\<le>M"] Sigma_Int_Paircomp1)
      apply (simp_all add: interval_split ij)
      apply (simp_all add: cbox_Pair_eq [symmetric] content_Pair [symmetric])
      apply (force simp add: interval_split [symmetric] intro!: n1 [rule_format])
      apply (force simp add: interval_split [symmetric] intro!: n2 [rule_format])
      done
  next
    case 2
    then have e: "e * content (cbox (u, w) (v, z)) =
                  e * (content (cbox u v) * content (cbox w z \<inter> {x. x \<bullet> j \<le> M})) +
                  e * (content (cbox u v) * content (cbox w z \<inter> {x. M \<le> x \<bullet> j}))"
      by (simp add: content_split [where c=M] content_Pair algebra_simps)
    have "(\<lambda>x. integral (cbox w z \<inter> {x. x \<bullet> j \<le> M}) (\<lambda>y. f (x, y))) integrable_on cbox u v"
                "(\<lambda>x. integral (cbox w z \<inter> {x. M \<le> x \<bullet> j}) (\<lambda>y. f (x, y))) integrable_on cbox u v"
      using 2 subs
      apply (simp_all add: interval_split)
      apply (rule_tac [!] integral_integrable_2dim [OF continuous_on_subset [OF f]])
      apply (auto simp: cbox_Pair_eq interval_split [symmetric])
      done
    with 2 have *: "integral (cbox u v) (\<lambda>x. integral (cbox w z) (\<lambda>y. f (x, y))) =
                   integral (cbox u v) (\<lambda>x. integral (cbox w z \<inter> {x. x \<bullet> j \<le> M}) (\<lambda>y. f (x, y))) +
                   integral (cbox u v) (\<lambda>x. integral (cbox w z \<inter> {x. M \<le> x \<bullet> j}) (\<lambda>y. f (x, y)))"
      by (simp add: integral_add [symmetric] integral_split [symmetric]
                    continuous_on_imp_integrable_on_Pair1 [OF fcont] cong: integral_cong)
    show ?normle
      apply (rule norm_diff2 [OF integral_split [where c=M, OF fint ij] * e])
      using 2 subs
      apply (simp_all add: cbox_Pair_eq setcomp_dot2 [of "\<lambda>u. M\<le>u"] setcomp_dot2 [of "\<lambda>u. u\<le>M"] Sigma_Int_Paircomp2)
      apply (simp_all add: interval_split ij)
      apply (simp_all add: cbox_Pair_eq [symmetric] content_Pair [symmetric])
      apply (force simp add: interval_split [symmetric] intro!: n1 [rule_format])
      apply (force simp add: interval_split [symmetric] intro!: n2 [rule_format])
      done
  qed
qed

lemma integral_Pair_const:
    "integral (cbox (a,c) (b,d)) (\<lambda>x. k) =
     integral (cbox a b) (\<lambda>x. integral (cbox c d) (\<lambda>y. k))"
  by (simp add: content_Pair)

lemma norm_minus2: "norm (x1-x2, y1-y2) = norm (x2-x1, y2-y1)"
  by (simp add: norm_minus_eqI)

lemma integral_prod_continuous:
  fixes f :: "('a::euclidean_space * 'b::euclidean_space) \<Rightarrow> 'c::banach"
  assumes "continuous_on (cbox (a,c) (b,d)) f" (is "continuous_on ?CBOX f")
    shows "integral (cbox (a,c) (b,d)) f = integral (cbox a b) (\<lambda>x. integral (cbox c d) (\<lambda>y. f(x,y)))"
proof (cases "content ?CBOX = 0")
  case True
  then show ?thesis
    by (auto simp: content_Pair)
next
  case False
  then have cbp: "content ?CBOX > 0"
    using content_lt_nz by blast
  have "norm (integral ?CBOX f - integral (cbox a b) (\<lambda>x. integral (cbox c d) (\<lambda>y. f (x,y)))) = 0"
  proof (rule dense_eq0_I, simp)
    fix e::real  assume "0 < e"
    with cbp have e': "0 < e / content ?CBOX"
      by simp
    have f_int_acbd: "f integrable_on cbox (a,c) (b,d)"
      by (rule integrable_continuous [OF assms])
    { fix p
      assume p: "p division_of cbox (a,c) (b,d)"
      note opd1 = comm_monoid_set.operative_division [OF comm_monoid_set_and integral_swap_operative [OF assms e'], THEN iffD1,
                       THEN spec, THEN spec, THEN spec, THEN spec, of p "(a,c)" "(b,d)" a c b d]
      have "(\<And>t u v w z.
              \<lbrakk>t \<in> p; cbox (u,w) (v,z) \<subseteq> t;  cbox (u,w) (v,z) \<subseteq> cbox (a,c) (b,d)\<rbrakk> \<Longrightarrow>
              norm (integral (cbox (u,w) (v,z)) f - integral (cbox u v) (\<lambda>x. integral (cbox w z) (\<lambda>y. f (x,y))))
              \<le> e * content (cbox (u,w) (v,z)) / content?CBOX)
            \<Longrightarrow>
            norm (integral ?CBOX f - integral (cbox a b) (\<lambda>x. integral (cbox c d) (\<lambda>y. f (x,y)))) \<le> e"
        using opd1 [OF p] False  by (simp add: comm_monoid_set_F_and)
    } note op_acbd = this
    { fix k::real and p and u::'a and v w and z::'b and t1 t2 l
      assume k: "0 < k"
         and nf: "\<And>x y u v.
                  \<lbrakk>x \<in> cbox a b; y \<in> cbox c d; u \<in> cbox a b; v\<in>cbox c d; norm (u-x, v-y) < k\<rbrakk>
                  \<Longrightarrow> norm (f(u,v) - f(x,y)) < e / (2 * (content ?CBOX))"
         and p_acbd: "p tagged_division_of cbox (a,c) (b,d)"
         and fine: "(\<lambda>x. ball x k) fine p"  "((t1,t2), l) \<in> p"
         and uwvz_sub: "cbox (u,w) (v,z) \<subseteq> l" "cbox (u,w) (v,z) \<subseteq> cbox (a,c) (b,d)"
      have t: "t1 \<in> cbox a b" "t2 \<in> cbox c d"
        by (meson fine p_acbd cbox_Pair_iff tag_in_interval)+
      have ls: "l \<subseteq> ball (t1,t2) k"
        using fine by (simp add: fine_def Ball_def)
      { fix x1 x2
        assume xuvwz: "x1 \<in> cbox u v" "x2 \<in> cbox w z"
        then have x: "x1 \<in> cbox a b" "x2 \<in> cbox c d"
          using uwvz_sub by auto
        have "norm (x1 - t1, x2 - t2) < k"
          using xuvwz ls uwvz_sub unfolding ball_def
          by (force simp add: cbox_Pair_eq dist_norm norm_minus2)
        then have "norm (f (x1,x2) - f (t1,t2)) \<le> e / content ?CBOX / 2"
          using nf [OF t x]  by simp
      } note nf' = this
      have f_int_uwvz: "f integrable_on cbox (u,w) (v,z)"
        using f_int_acbd uwvz_sub integrable_on_subcbox by blast
      have f_int_uv: "\<And>x. x \<in> cbox u v \<Longrightarrow> (\<lambda>y. f (x,y)) integrable_on cbox w z"
        using assms continuous_on_subset uwvz_sub
        by (blast intro: continuous_on_imp_integrable_on_Pair1)
      have 1: "norm (integral (cbox (u,w) (v,z)) f - integral (cbox (u,w) (v,z)) (\<lambda>x. f (t1,t2)))
         \<le> e * content (cbox (u,w) (v,z)) / content ?CBOX / 2"
        apply (simp only: integral_diff [symmetric] f_int_uwvz integrable_const)
        apply (rule order_trans [OF integrable_bound [of "e / content ?CBOX / 2"]])
        using cbp e' nf'
        apply (auto simp: integrable_diff f_int_uwvz integrable_const)
        done
      have int_integrable: "(\<lambda>x. integral (cbox w z) (\<lambda>y. f (x, y))) integrable_on cbox u v"
        using assms integral_integrable_2dim continuous_on_subset uwvz_sub(2) by blast
      have normint_wz:
         "\<And>x. x \<in> cbox u v \<Longrightarrow>
               norm (integral (cbox w z) (\<lambda>y. f (x, y)) - integral (cbox w z) (\<lambda>y. f (t1, t2)))
               \<le> e * content (cbox w z) / content (cbox (a, c) (b, d)) / 2"
        apply (simp only: integral_diff [symmetric] f_int_uv integrable_const)
        apply (rule order_trans [OF integrable_bound [of "e / content ?CBOX / 2"]])
        using cbp e' nf'
        apply (auto simp: integrable_diff f_int_uv integrable_const)
        done
      have "norm (integral (cbox u v)
               (\<lambda>x. integral (cbox w z) (\<lambda>y. f (x,y)) - integral (cbox w z) (\<lambda>y. f (t1,t2))))
            \<le> e * content (cbox w z) / content ?CBOX / 2 * content (cbox u v)"
        apply (rule integrable_bound [OF _ _ normint_wz])
        using cbp e'
        apply (auto simp: divide_simps content_pos_le integrable_diff int_integrable integrable_const)
        done
      also have "... \<le> e * content (cbox (u,w) (v,z)) / content ?CBOX / 2"
        by (simp add: content_Pair divide_simps)
      finally have 2: "norm (integral (cbox u v) (\<lambda>x. integral (cbox w z) (\<lambda>y. f (x,y))) -
                      integral (cbox u v) (\<lambda>x. integral (cbox w z) (\<lambda>y. f (t1,t2))))
                \<le> e * content (cbox (u,w) (v,z)) / content ?CBOX / 2"
        by (simp only: integral_diff [symmetric] int_integrable integrable_const)
      have norm_xx: "\<lbrakk>x' = y'; norm(x - x') \<le> e/2; norm(y - y') \<le> e/2\<rbrakk> \<Longrightarrow> norm(x - y) \<le> e" for x::'c and y x' y' e
        using norm_triangle_mono [of "x-y'" "e/2" "y'-y" "e/2"] real_sum_of_halves
        by (simp add: norm_minus_commute)
      have "norm (integral (cbox (u,w) (v,z)) f - integral (cbox u v) (\<lambda>x. integral (cbox w z) (\<lambda>y. f (x,y))))
            \<le> e * content (cbox (u,w) (v,z)) / content ?CBOX"
        by (rule norm_xx [OF integral_Pair_const 1 2])
    } note * = this
    show "norm (integral ?CBOX f - integral (cbox a b) (\<lambda>x. integral (cbox c d) (\<lambda>y. f (x,y)))) \<le> e"
      using compact_uniformly_continuous [OF assms compact_cbox]
      apply (simp add: uniformly_continuous_on_def dist_norm)
      apply (drule_tac x="e / 2 / content?CBOX" in spec)
      using cbp \<open>0 < e\<close>
      apply (auto simp: zero_less_mult_iff)
      apply (rename_tac k)
      apply (rule_tac e1=k in fine_division_exists [OF gauge_ball, where a = "(a,c)" and b = "(b,d)"])
      apply assumption
      apply (rule op_acbd)
      apply (erule division_of_tagged_division)
      using *
      apply auto
      done
  qed
  then show ?thesis
    by simp
qed

lemma swap_continuous:
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

lemma integral_swap_2dim:
  fixes f :: "['a::euclidean_space, 'b::euclidean_space] \<Rightarrow> 'c::banach"
  assumes "continuous_on (cbox (a,c) (b,d)) (\<lambda>(x,y). f x y)"
    shows "integral (cbox (a, c) (b, d)) (\<lambda>(x, y). f x y) = integral (cbox (c, a) (d, b)) (\<lambda>(x, y). f y x)"
proof -
  have "((\<lambda>(x, y). f x y) has_integral integral (cbox (c, a) (d, b)) (\<lambda>(x, y). f y x)) (prod.swap ` (cbox (c, a) (d, b)))"
    apply (rule has_integral_twiddle [of 1 prod.swap prod.swap "\<lambda>(x,y). f y x" "integral (cbox (c, a) (d, b)) (\<lambda>(x, y). f y x)", simplified])
    apply (auto simp: isCont_swap content_Pair has_integral_integral [symmetric] integrable_continuous swap_continuous assms)
    done
 then show ?thesis
   by force
qed

theorem integral_swap_continuous:
  fixes f :: "['a::euclidean_space, 'b::euclidean_space] \<Rightarrow> 'c::banach"
  assumes "continuous_on (cbox (a,c) (b,d)) (\<lambda>(x,y). f x y)"
    shows "integral (cbox a b) (\<lambda>x. integral (cbox c d) (f x)) =
           integral (cbox c d) (\<lambda>y. integral (cbox a b) (\<lambda>x. f x y))"
proof -
  have "integral (cbox a b) (\<lambda>x. integral (cbox c d) (f x)) = integral (cbox (a, c) (b, d)) (\<lambda>(x, y). f x y)"
    using integral_prod_continuous [OF assms] by auto
  also have "... = integral (cbox (c, a) (d, b)) (\<lambda>(x, y). f y x)"
    by (rule integral_swap_2dim [OF assms])
  also have "... = integral (cbox c d) (\<lambda>y. integral (cbox a b) (\<lambda>x. f x y))"
    using integral_prod_continuous [OF swap_continuous] assms
    by auto
  finally show ?thesis .
qed


subsection \<open>Definite integrals for exponential and power function\<close>

lemma has_integral_exp_minus_to_infinity:
  assumes a: "a > 0"
  shows   "((\<lambda>x::real. exp (-a*x)) has_integral exp (-a*c)/a) {c..}"
proof -
  define f where "f = (\<lambda>k x. if x \<in> {c..real k} then exp (-a*x) else 0)"

  {
    fix k :: nat assume k: "of_nat k \<ge> c"
    from k a
      have "((\<lambda>x. exp (-a*x)) has_integral (-exp (-a*real k)/a - (-exp (-a*c)/a))) {c..real k}"
      by (intro fundamental_theorem_of_calculus)
         (auto intro!: derivative_eq_intros
               simp: has_field_derivative_iff_has_vector_derivative [symmetric])
    hence "(f k has_integral (exp (-a*c)/a - exp (-a*real k)/a)) {c..}" unfolding f_def
      by (subst has_integral_restrict) simp_all
  } note has_integral_f = this

  have [simp]: "f k = (\<lambda>_. 0)" if "of_nat k < c" for k using that by (auto simp: fun_eq_iff f_def)
  have integral_f: "integral {c..} (f k) =
                      (if real k \<ge> c then exp (-a*c)/a - exp (-a*real k)/a else 0)"
    for k using integral_unique[OF has_integral_f[of k]] by simp

  have A: "(\<lambda>x. exp (-a*x)) integrable_on {c..} \<and>
             (\<lambda>k. integral {c..} (f k)) \<longlonglongrightarrow> integral {c..} (\<lambda>x. exp (-a*x))"
  proof (intro monotone_convergence_increasing allI ballI)
    fix k ::nat
    have "(\<lambda>x. exp (-a*x)) integrable_on {c..of_real k}" (is ?P)
      unfolding f_def by (auto intro!: continuous_intros integrable_continuous_real)
    hence int: "(f k) integrable_on {c..of_real k}"
      by (rule integrable_eq[rotated]) (simp add: f_def)
    show "f k integrable_on {c..}"
      by (rule integrable_on_superset[OF _ _ int]) (auto simp: f_def)
  next
    fix x assume x: "x \<in> {c..}"
    have "sequentially \<le> principal {nat \<lceil>x\<rceil>..}" unfolding at_top_def by (simp add: Inf_lower)
    also have "{nat \<lceil>x\<rceil>..} \<subseteq> {k. x \<le> real k}" by auto
    also have "inf (principal \<dots>) (principal {k. \<not>x \<le> real k}) =
                 principal ({k. x \<le> real k} \<inter> {k. \<not>x \<le> real k})" by simp
    also have "{k. x \<le> real k} \<inter> {k. \<not>x \<le> real k} = {}" by blast
    finally have "inf sequentially (principal {k. \<not>x \<le> real k}) = bot"
      by (simp add: inf.coboundedI1 bot_unique)
    with x show "(\<lambda>k. f k x) \<longlonglongrightarrow> exp (-a*x)" unfolding f_def
      by (intro filterlim_If) auto
  next
    have "\<bar>integral {c..} (f k)\<bar> \<le> exp (-a*c)/a" for k
    proof (cases "c > of_nat k")
      case False
      hence "abs (integral {c..} (f k)) = abs (exp (- (a * c)) / a - exp (- (a * real k)) / a)"
        by (simp add: integral_f)
      also have "abs (exp (- (a * c)) / a - exp (- (a * real k)) / a) =
                   exp (- (a * c)) / a - exp (- (a * real k)) / a"
        using False a by (intro abs_of_nonneg) (simp_all add: field_simps)
      also have "\<dots> \<le> exp (- a * c) / a" using a by simp
      finally show ?thesis .
    qed (insert a, simp_all add: integral_f)
    thus "bounded {integral {c..} (f k) |k. True}"
      by (intro bounded_realI[of _ "exp (-a*c)/a"]) auto
  qed (auto simp: f_def)

  from eventually_gt_at_top[of "nat \<lceil>c\<rceil>"] have "eventually (\<lambda>k. of_nat k > c) sequentially"
    by eventually_elim linarith
  hence "eventually (\<lambda>k. exp (-a*c)/a - exp (-a * of_nat k)/a = integral {c..} (f k)) sequentially"
    by eventually_elim (simp add: integral_f)
  moreover have "(\<lambda>k. exp (-a*c)/a - exp (-a * of_nat k)/a) \<longlonglongrightarrow> exp (-a*c)/a - 0/a"
    by (intro tendsto_intros filterlim_compose[OF exp_at_bot]
          filterlim_tendsto_neg_mult_at_bot[OF tendsto_const] filterlim_real_sequentially)+
       (insert a, simp_all)
  ultimately have "(\<lambda>k. integral {c..} (f k)) \<longlonglongrightarrow> exp (-a*c)/a - 0/a"
    by (rule Lim_transform_eventually)
  from LIMSEQ_unique[OF conjunct2[OF A] this]
    have "integral {c..} (\<lambda>x. exp (-a*x)) = exp (-a*c)/a" by simp
  with conjunct1[OF A] show ?thesis
    by (simp add: has_integral_integral)
qed

lemma integrable_on_exp_minus_to_infinity: "a > 0 \<Longrightarrow> (\<lambda>x. exp (-a*x) :: real) integrable_on {c..}"
  using has_integral_exp_minus_to_infinity[of a c] unfolding integrable_on_def by blast

lemma has_integral_powr_from_0:
  assumes a: "a > (-1::real)" and c: "c \<ge> 0"
  shows   "((\<lambda>x. x powr a) has_integral (c powr (a+1) / (a+1))) {0..c}"
proof (cases "c = 0")
  case False
  define f where "f = (\<lambda>k x. if x \<in> {inverse (of_nat (Suc k))..c} then x powr a else 0)"
  define F where "F = (\<lambda>k. if inverse (of_nat (Suc k)) \<le> c then
                             c powr (a+1)/(a+1) - inverse (real (Suc k)) powr (a+1)/(a+1) else 0)"

  {
    fix k :: nat
    have "(f k has_integral F k) {0..c}"
    proof (cases "inverse (of_nat (Suc k)) \<le> c")
      case True
      {
        fix x assume x: "x \<ge> inverse (1 + real k)"
        have "0 < inverse (1 + real k)" by simp
        also note x
        finally have "x > 0" .
      } note x = this
      hence "((\<lambda>x. x powr a) has_integral c powr (a + 1) / (a + 1) -
               inverse (real (Suc k)) powr (a + 1) / (a + 1)) {inverse (real (Suc k))..c}"
        using True a by (intro fundamental_theorem_of_calculus)
           (auto intro!: derivative_eq_intros continuous_on_powr' continuous_on_const
             continuous_on_id simp: has_field_derivative_iff_has_vector_derivative [symmetric])
      with True show ?thesis unfolding f_def F_def by (subst has_integral_restrict) simp_all
    next
      case False
      thus ?thesis unfolding f_def F_def by (subst has_integral_restrict) auto
    qed
  } note has_integral_f = this
  have integral_f: "integral {0..c} (f k) = F k" for k
    using has_integral_f[of k] by (rule integral_unique)

  have A: "(\<lambda>x. x powr a) integrable_on {0..c} \<and>
           (\<lambda>k. integral {0..c} (f k)) \<longlonglongrightarrow> integral {0..c} (\<lambda>x. x powr a)"
  proof (intro monotone_convergence_increasing ballI allI)
    fix k from has_integral_f[of k] show "f k integrable_on {0..c}"
      by (auto simp: integrable_on_def)
  next
    fix k :: nat and x :: real
    {
      assume x: "inverse (real (Suc k)) \<le> x"
      have "inverse (real (Suc (Suc k))) \<le> inverse (real (Suc k))" by (simp add: field_simps)
      also note x
      finally have "inverse (real (Suc (Suc k))) \<le> x" .
    }
    thus "f k x \<le> f (Suc k) x" by (auto simp: f_def simp del: of_nat_Suc)
  next
    fix x assume x: "x \<in> {0..c}"
    show "(\<lambda>k. f k x) \<longlonglongrightarrow> x powr a"
    proof (cases "x = 0")
      case False
      with x have "x > 0" by simp
      from order_tendstoD(2)[OF LIMSEQ_inverse_real_of_nat this]
        have "eventually (\<lambda>k. x powr a = f k x) sequentially"
        by eventually_elim (insert x, simp add: f_def)
      moreover have "(\<lambda>_. x powr a) \<longlonglongrightarrow> x powr a" by simp
      ultimately show ?thesis by (rule Lim_transform_eventually)
    qed (simp_all add: f_def)
  next
    {
      fix k
      from a have "F k \<le> c powr (a + 1) / (a + 1)"
        by (auto simp add: F_def divide_simps)
      also from a have "F k \<ge> 0"
        by (auto simp: F_def divide_simps simp del: of_nat_Suc intro!: powr_mono2)
      hence "F k = abs (F k)" by simp
      finally have "abs (F k) \<le>  c powr (a + 1) / (a + 1)" .
    }
    thus "bounded {integral {0..c} (f k) |k. True}"
      by (intro bounded_realI[of _ "c powr (a+1) / (a+1)"]) (auto simp: integral_f)
  qed

  from False c have "c > 0" by simp
  from order_tendstoD(2)[OF LIMSEQ_inverse_real_of_nat this]
    have "eventually (\<lambda>k. c powr (a + 1) / (a + 1) - inverse (real (Suc k)) powr (a+1) / (a+1) =
            integral {0..c} (f k)) sequentially"
    by eventually_elim (simp add: integral_f F_def)
  moreover have "(\<lambda>k. c powr (a + 1) / (a + 1) - inverse (real (Suc k)) powr (a + 1) / (a + 1))
                   \<longlonglongrightarrow> c powr (a + 1) / (a + 1) - 0 powr (a + 1) / (a + 1)"
    using a by (intro tendsto_intros LIMSEQ_inverse_real_of_nat) auto
  hence "(\<lambda>k. c powr (a + 1) / (a + 1) - inverse (real (Suc k)) powr (a + 1) / (a + 1))
          \<longlonglongrightarrow> c powr (a + 1) / (a + 1)" by simp
  ultimately have "(\<lambda>k. integral {0..c} (f k)) \<longlonglongrightarrow> c powr (a+1) / (a+1)"
    by (rule Lim_transform_eventually)
  with A have "integral {0..c} (\<lambda>x. x powr a) = c powr (a+1) / (a+1)"
    by (blast intro: LIMSEQ_unique)
  with A show ?thesis by (simp add: has_integral_integral)
qed (simp_all add: has_integral_refl)

lemma integrable_on_powr_from_0:
  assumes a: "a > (-1::real)" and c: "c \<ge> 0"
  shows   "(\<lambda>x. x powr a) integrable_on {0..c}"
  using has_integral_powr_from_0[OF assms] unfolding integrable_on_def by blast

lemma has_integral_powr_to_inf:
  fixes a e :: real
  assumes "e < -1" "a > 0"
  shows   "((\<lambda>x. x powr e) has_integral -(a powr (e + 1)) / (e + 1)) {a..}"
proof -
  define f :: "nat \<Rightarrow> real \<Rightarrow> real" where "f = (\<lambda>n x. if x \<in> {a..n} then x powr e else 0)"
  define F where "F = (\<lambda>x. x powr (e + 1) / (e + 1))"

  have has_integral_f: "(f n has_integral (F n - F a)) {a..}"
    if n: "n \<ge> a" for n :: nat
  proof -
    from n assms have "((\<lambda>x. x powr e) has_integral (F n - F a)) {a..n}"
      by (intro fundamental_theorem_of_calculus) (auto intro!: derivative_eq_intros
            simp: has_field_derivative_iff_has_vector_derivative [symmetric] F_def)
    hence "(f n has_integral (F n - F a)) {a..n}"
      by (rule has_integral_eq [rotated]) (simp add: f_def)
    thus "(f n has_integral (F n - F a)) {a..}"
      by (rule has_integral_on_superset [rotated 2]) (auto simp: f_def)
  qed
  have integral_f: "integral {a..} (f n) = (if n \<ge> a then F n - F a else 0)" for n :: nat
  proof (cases "n \<ge> a")
    case True
    with has_integral_f[OF this] show ?thesis by (simp add: integral_unique)
  next
    case False
    have "(f n has_integral 0) {a}" by (rule has_integral_refl)
    hence "(f n has_integral 0) {a..}"
      by (rule has_integral_on_superset [rotated 2]) (insert False, simp_all add: f_def)
    with False show ?thesis by (simp add: integral_unique)
  qed

  have *: "(\<lambda>x. x powr e) integrable_on {a..} \<and>
           (\<lambda>n. integral {a..} (f n)) \<longlonglongrightarrow> integral {a..} (\<lambda>x. x powr e)"
  proof (intro monotone_convergence_increasing allI ballI)
    fix n :: nat
    from assms have "(\<lambda>x. x powr e) integrable_on {a..n}"
      by (auto intro!: integrable_continuous_real continuous_intros)
    hence "f n integrable_on {a..n}"
      by (rule integrable_eq [rotated]) (auto simp: f_def)
    thus "f n integrable_on {a..}"
      by (rule integrable_on_superset [rotated 2]) (auto simp: f_def)
  next
    fix n :: nat and x :: real
    show "f n x \<le> f (Suc n) x" by (auto simp: f_def)
  next
    fix x :: real assume x: "x \<in> {a..}"
    from filterlim_real_sequentially
      have "eventually (\<lambda>n. real n \<ge> x) at_top"
      by (simp add: filterlim_at_top)
    with x have "eventually (\<lambda>n. f n x = x powr e) at_top"
      by (auto elim!: eventually_mono simp: f_def)
    thus "(\<lambda>n. f n x) \<longlonglongrightarrow> x powr e" by (simp add: Lim_eventually)
  next
    have "norm (integral {a..} (f n)) \<le> -F a" for n :: nat
    proof (cases "n \<ge> a")
      case True
      with assms have "a powr (e + 1) \<ge> n powr (e + 1)"
        by (intro powr_mono2') simp_all
      with assms show ?thesis by (auto simp: divide_simps F_def integral_f)
    qed (insert assms, simp add: integral_f F_def divide_simps)
    thus "bounded {integral {a..} (f n) |n. True}"
      unfolding bounded_iff by (intro exI[of _ "-F a"]) auto
  qed

  from filterlim_real_sequentially
    have "eventually (\<lambda>n. real n \<ge> a) at_top"
    by (simp add: filterlim_at_top)
  hence "eventually (\<lambda>n. F n - F a = integral {a..} (f n)) at_top"
    by eventually_elim (simp add: integral_f)
  moreover have "(\<lambda>n. F n - F a) \<longlonglongrightarrow> 0 / (e + 1) - F a" unfolding F_def
    by (insert assms, (rule tendsto_intros filterlim_compose[OF tendsto_neg_powr]
          filterlim_ident filterlim_real_sequentially | simp)+)
  hence "(\<lambda>n. F n - F a) \<longlonglongrightarrow> -F a" by simp
  ultimately have "(\<lambda>n. integral {a..} (f n)) \<longlonglongrightarrow> -F a" by (rule Lim_transform_eventually)
  from conjunct2[OF *] and this
    have "integral {a..} (\<lambda>x. x powr e) = -F a" by (rule LIMSEQ_unique)
  with conjunct1[OF *] show ?thesis
    by (simp add: has_integral_integral F_def)
qed

lemma has_integral_inverse_power_to_inf:
  fixes a :: real and n :: nat
  assumes "n > 1" "a > 0"
  shows   "((\<lambda>x. 1 / x ^ n) has_integral 1 / (real (n - 1) * a ^ (n - 1))) {a..}"
proof -
  from assms have "real_of_int (-int n) < -1" by simp
  note has_integral_powr_to_inf[OF this \<open>a > 0\<close>]
  also have "- (a powr (real_of_int (- int n) + 1)) / (real_of_int (- int n) + 1) =
                 1 / (real (n - 1) * a powr (real (n - 1)))" using assms
    by (simp add: divide_simps powr_add [symmetric] of_nat_diff)
  also from assms have "a powr (real (n - 1)) = a ^ (n - 1)"
    by (intro powr_realpow)
  finally show ?thesis
    by (rule has_integral_eq [rotated])
       (insert assms, simp_all add: powr_minus powr_realpow divide_simps)
qed

subsubsection \<open>Adaption to ordered Euclidean spaces and the Cartesian Euclidean space\<close>

lemma integral_component_eq_cart[simp]:
  fixes f :: "'n::euclidean_space \<Rightarrow> real^'m"
  assumes "f integrable_on s"
  shows "integral s (\<lambda>x. f x $ k) = integral s f $ k"
  using integral_linear[OF assms(1) bounded_linear_component_cart,unfolded o_def] .

lemma content_closed_interval:
  fixes a :: "'a::ordered_euclidean_space"
  assumes "a \<le> b"
  shows "content {a .. b} = (\<Prod>i\<in>Basis. b\<bullet>i - a\<bullet>i)"
  using content_cbox[of a b] assms
  by (simp add: cbox_interval eucl_le[where 'a='a])

lemma integrable_const_ivl[intro]:
  fixes a::"'a::ordered_euclidean_space"
  shows "(\<lambda>x. c) integrable_on {a .. b}"
  unfolding cbox_interval[symmetric]
  by (rule integrable_const)

lemma integrable_on_subinterval:
  fixes f :: "'n::ordered_euclidean_space \<Rightarrow> 'a::banach"
  assumes "f integrable_on s"
    and "{a .. b} \<subseteq> s"
  shows "f integrable_on {a .. b}"
  using integrable_on_subcbox[of f s a b] assms
  by (simp add: cbox_interval)

end
