(*  Title:      HOL/Analysis/Uniform_Limit.thy
    Author:     Christoph Traut, TU München
    Author:     Fabian Immler, TU München
*)

section \<open>Uniform Limit and Uniform Convergence\<close>

theory Uniform_Limit
imports Connected Summation_Tests
begin


subsection \<open>Definition\<close>

definition\<^marker>\<open>tag important\<close> uniformly_on :: "'a set \<Rightarrow> ('a \<Rightarrow> 'b::metric_space) \<Rightarrow> ('a \<Rightarrow> 'b) filter"
  where "uniformly_on S l = (INF e\<in>{0 <..}. principal {f. \<forall>x\<in>S. dist (f x) (l x) < e})"

abbreviation\<^marker>\<open>tag important\<close>
  "uniform_limit S f l \<equiv> filterlim f (uniformly_on S l)"

definition uniformly_convergent_on where
  "uniformly_convergent_on X f \<longleftrightarrow> (\<exists>l. uniform_limit X f l sequentially)"

definition uniformly_Cauchy_on where
  "uniformly_Cauchy_on X f \<longleftrightarrow> (\<forall>e>0. \<exists>M. \<forall>x\<in>X. \<forall>(m::nat)\<ge>M. \<forall>n\<ge>M. dist (f m x) (f n x) < e)"

proposition uniform_limit_iff:
  "uniform_limit S f l F \<longleftrightarrow> (\<forall>e>0. \<forall>\<^sub>F n in F. \<forall>x\<in>S. dist (f n x) (l x) < e)"
  unfolding filterlim_iff uniformly_on_def
  by (subst eventually_INF_base)
    (fastforce
      simp: eventually_principal uniformly_on_def
      intro: bexI[where x="min a b" for a b]
      elim: eventually_mono)+

lemma uniform_limitD:
  "uniform_limit S f l F \<Longrightarrow> e > 0 \<Longrightarrow> \<forall>\<^sub>F n in F. \<forall>x\<in>S. dist (f n x) (l x) < e"
  by (simp add: uniform_limit_iff)

lemma uniform_limitI:
  "(\<And>e. e > 0 \<Longrightarrow> \<forall>\<^sub>F n in F. \<forall>x\<in>S. dist (f n x) (l x) < e) \<Longrightarrow> uniform_limit S f l F"
  by (simp add: uniform_limit_iff)

lemma uniform_limit_sequentially_iff:
  "uniform_limit S f l sequentially \<longleftrightarrow> (\<forall>e>0. \<exists>N. \<forall>n\<ge>N. \<forall>x \<in> S. dist (f n x) (l x) < e)"
  unfolding uniform_limit_iff eventually_sequentially ..

lemma uniform_limit_at_iff:
  "uniform_limit S f l (at x) \<longleftrightarrow>
    (\<forall>e>0. \<exists>d>0. \<forall>z. 0 < dist z x \<and> dist z x < d \<longrightarrow> (\<forall>x\<in>S. dist (f z x) (l x) < e))"
  unfolding uniform_limit_iff eventually_at by simp

lemma uniform_limit_at_le_iff:
  "uniform_limit S f l (at x) \<longleftrightarrow>
    (\<forall>e>0. \<exists>d>0. \<forall>z. 0 < dist z x \<and> dist z x < d \<longrightarrow> (\<forall>x\<in>S. dist (f z x) (l x) \<le> e))"
  unfolding uniform_limit_iff eventually_at
  by (fastforce dest: spec[where x = "e / 2" for e])

lemma metric_uniform_limit_imp_uniform_limit:
  assumes f: "uniform_limit S f a F"
  assumes le: "eventually (\<lambda>x. \<forall>y\<in>S. dist (g x y) (b y) \<le> dist (f x y) (a y)) F"
  shows "uniform_limit S g b F"
proof (rule uniform_limitI)
  fix e :: real assume "0 < e"
  from uniform_limitD[OF f this] le
  show "\<forall>\<^sub>F x in F. \<forall>y\<in>S. dist (g x y) (b y) < e"
    by eventually_elim force
qed


subsection \<open>Exchange limits\<close>

proposition swap_uniform_limit:
  assumes f: "\<forall>\<^sub>F n in F. (f n \<longlongrightarrow> g n) (at x within S)"
  assumes g: "(g \<longlongrightarrow> l) F"
  assumes uc: "uniform_limit S f h F"
  assumes "\<not>trivial_limit F"
  shows "(h \<longlongrightarrow> l) (at x within S)"
proof (rule tendstoI)
  fix e :: real
  define e' where "e' = e/3"
  assume "0 < e"
  then have "0 < e'" by (simp add: e'_def)
  from uniform_limitD[OF uc \<open>0 < e'\<close>]
  have "\<forall>\<^sub>F n in F. \<forall>x\<in>S. dist (h x) (f n x) < e'"
    by (simp add: dist_commute)
  moreover
  from f
  have "\<forall>\<^sub>F n in F. \<forall>\<^sub>F x in at x within S. dist (g n) (f n x) < e'"
    by eventually_elim (auto dest!: tendstoD[OF _ \<open>0 < e'\<close>] simp: dist_commute)
  moreover
  from tendstoD[OF g \<open>0 < e'\<close>] have "\<forall>\<^sub>F x in F. dist l (g x) < e'"
    by (simp add: dist_commute)
  ultimately
  have "\<forall>\<^sub>F _ in F. \<forall>\<^sub>F x in at x within S. dist (h x) l < e"
  proof eventually_elim
    case (elim n)
    note fh = elim(1)
    note gl = elim(3)
    have "\<forall>\<^sub>F x in at x within S. x \<in> S"
      by (auto simp: eventually_at_filter)
    with elim(2)
    show ?case
    proof eventually_elim
      case (elim x)
      from fh[rule_format, OF \<open>x \<in> S\<close>] elim(1)
      have "dist (h x) (g n) < e' + e'"
        by (rule dist_triangle_lt[OF add_strict_mono])
      from dist_triangle_lt[OF add_strict_mono, OF this gl]
      show ?case by (simp add: e'_def)
    qed
  qed
  thus "\<forall>\<^sub>F x in at x within S. dist (h x) l < e"
    using eventually_happens by (metis \<open>\<not>trivial_limit F\<close>)
qed


subsection \<open>Uniform limit theorem\<close>

lemma tendsto_uniform_limitI:
  assumes "uniform_limit S f l F"
  assumes "x \<in> S"
  shows "((\<lambda>y. f y x) \<longlongrightarrow> l x) F"
  using assms
  by (auto intro!: tendstoI simp: eventually_mono dest!: uniform_limitD)

theorem uniform_limit_theorem:
  assumes c: "\<forall>\<^sub>F n in F. continuous_on A (f n)"
  assumes ul: "uniform_limit A f l F"
  assumes "\<not> trivial_limit F"
  shows "continuous_on A l"
  unfolding continuous_on_def
proof safe
  fix x assume "x \<in> A"
  then have "\<forall>\<^sub>F n in F. (f n \<longlongrightarrow> f n x) (at x within A)" "((\<lambda>n. f n x) \<longlongrightarrow> l x) F"
    using c ul
    by (auto simp: continuous_on_def eventually_mono tendsto_uniform_limitI)
  then show "(l \<longlongrightarrow> l x) (at x within A)"
    by (rule swap_uniform_limit) fact+
qed

lemma uniformly_Cauchy_onI:
  assumes "\<And>e. e > 0 \<Longrightarrow> \<exists>M. \<forall>x\<in>X. \<forall>m\<ge>M. \<forall>n\<ge>M. dist (f m x) (f n x) < e"
  shows   "uniformly_Cauchy_on X f"
  using assms unfolding uniformly_Cauchy_on_def by blast

lemma uniformly_Cauchy_onI':
  assumes "\<And>e. e > 0 \<Longrightarrow> \<exists>M. \<forall>x\<in>X. \<forall>m\<ge>M. \<forall>n>m. dist (f m x) (f n x) < e"
  shows   "uniformly_Cauchy_on X f"
proof (rule uniformly_Cauchy_onI)
  fix e :: real assume e: "e > 0"
  from assms[OF this] obtain M
    where M: "\<And>x m n. x \<in> X \<Longrightarrow> m \<ge> M \<Longrightarrow> n > m \<Longrightarrow> dist (f m x) (f n x) < e" by fast
  {
    fix x m n assume x: "x \<in> X" and m: "m \<ge> M" and n: "n \<ge> M"
    with M[OF this(1,2), of n] M[OF this(1,3), of m] e have "dist (f m x) (f n x) < e"
      by (cases m n rule: linorder_cases) (simp_all add: dist_commute)
  }
  thus "\<exists>M. \<forall>x\<in>X. \<forall>m\<ge>M. \<forall>n\<ge>M. dist (f m x) (f n x) < e" by fast
qed

lemma uniformly_Cauchy_imp_Cauchy:
  "uniformly_Cauchy_on X f \<Longrightarrow> x \<in> X \<Longrightarrow> Cauchy (\<lambda>n. f n x)"
  unfolding Cauchy_def uniformly_Cauchy_on_def by fast

lemma uniform_limit_cong:
  fixes f g :: "'a \<Rightarrow> 'b \<Rightarrow> ('c :: metric_space)" and h i :: "'b \<Rightarrow> 'c"
  assumes "eventually (\<lambda>y. \<forall>x\<in>X. f y x = g y x) F"
  assumes "\<And>x. x \<in> X \<Longrightarrow> h x = i x"
  shows   "uniform_limit X f h F \<longleftrightarrow> uniform_limit X g i F"
proof -
  {
    fix f g :: "'a \<Rightarrow> 'b \<Rightarrow> 'c" and h i :: "'b \<Rightarrow> 'c"
    assume C: "uniform_limit X f h F" and A: "eventually (\<lambda>y. \<forall>x\<in>X. f y x = g y x) F"
       and B: "\<And>x. x \<in> X \<Longrightarrow> h x = i x"
    {
      fix e ::real assume "e > 0"
      with C have "eventually (\<lambda>y. \<forall>x\<in>X. dist (f y x) (h x) < e) F"
        unfolding uniform_limit_iff by blast
      with A have "eventually (\<lambda>y. \<forall>x\<in>X. dist (g y x) (i x) < e) F"
        by eventually_elim (insert B, simp_all)
    }
    hence "uniform_limit X g i F" unfolding uniform_limit_iff by blast
  } note A = this
  show ?thesis by (rule iffI) (erule A; insert assms; simp add: eq_commute)+
qed

lemma uniform_limit_cong':
  fixes f g :: "'a \<Rightarrow> 'b \<Rightarrow> ('c :: metric_space)" and h i :: "'b \<Rightarrow> 'c"
  assumes "\<And>y x. x \<in> X \<Longrightarrow> f y x = g y x"
  assumes "\<And>x. x \<in> X \<Longrightarrow> h x = i x"
  shows   "uniform_limit X f h F \<longleftrightarrow> uniform_limit X g i F"
  using assms by (intro uniform_limit_cong always_eventually) blast+

lemma uniformly_convergent_cong:
  assumes "eventually (\<lambda>x. \<forall>y\<in>A. f x y = g x y) sequentially" "A = B"
  shows "uniformly_convergent_on A f \<longleftrightarrow> uniformly_convergent_on B g"
  unfolding uniformly_convergent_on_def assms(2) [symmetric]
  by (intro iff_exI uniform_limit_cong eventually_mono [OF assms(1)]) auto

lemma uniformly_convergent_uniform_limit_iff:
  "uniformly_convergent_on X f \<longleftrightarrow> uniform_limit X f (\<lambda>x. lim (\<lambda>n. f n x)) sequentially"
proof
  assume "uniformly_convergent_on X f"
  then obtain l where l: "uniform_limit X f l sequentially"
    unfolding uniformly_convergent_on_def by blast
  from l have "uniform_limit X f (\<lambda>x. lim (\<lambda>n. f n x)) sequentially \<longleftrightarrow>
                      uniform_limit X f l sequentially"
    by (intro uniform_limit_cong' limI tendsto_uniform_limitI[of f X l]) simp_all
  also note l
  finally show "uniform_limit X f (\<lambda>x. lim (\<lambda>n. f n x)) sequentially" .
qed (auto simp: uniformly_convergent_on_def)

lemma uniformly_convergentI: "uniform_limit X f l sequentially \<Longrightarrow> uniformly_convergent_on X f"
  unfolding uniformly_convergent_on_def by blast

lemma uniformly_convergent_on_empty [iff]: "uniformly_convergent_on {} f"
  by (simp add: uniformly_convergent_on_def uniform_limit_sequentially_iff)

lemma uniformly_convergent_on_const [simp,intro]:
  "uniformly_convergent_on A (\<lambda>_. c)"
  by (auto simp: uniformly_convergent_on_def uniform_limit_iff intro!: exI[of _ c])

text\<open>Cauchy-type criteria for uniform convergence.\<close>

lemma Cauchy_uniformly_convergent:
  fixes f :: "nat \<Rightarrow> 'a \<Rightarrow> 'b :: complete_space"
  assumes "uniformly_Cauchy_on X f"
  shows   "uniformly_convergent_on X f"
unfolding uniformly_convergent_uniform_limit_iff uniform_limit_iff
proof safe
  let ?f = "\<lambda>x. lim (\<lambda>n. f n x)"
  fix e :: real assume e: "e > 0"
  hence "e/2 > 0" by simp
  with assms obtain N where N: "\<And>x m n. x \<in> X \<Longrightarrow> m \<ge> N \<Longrightarrow> n \<ge> N \<Longrightarrow> dist (f m x) (f n x) < e/2"
    unfolding uniformly_Cauchy_on_def by fast
  show "eventually (\<lambda>n. \<forall>x\<in>X. dist (f n x) (?f x) < e) sequentially"
    using eventually_ge_at_top[of N]
  proof eventually_elim
    fix n assume n: "n \<ge> N"
    show "\<forall>x\<in>X. dist (f n x) (?f x) < e"
    proof
      fix x assume x: "x \<in> X"
      with assms have "(\<lambda>n. f n x) \<longlonglongrightarrow> ?f x"
        by (auto dest!: Cauchy_convergent uniformly_Cauchy_imp_Cauchy simp: convergent_LIMSEQ_iff)
      with \<open>e/2 > 0\<close> have "eventually (\<lambda>m. m \<ge> N \<and> dist (f m x) (?f x) < e/2) sequentially"
        by (intro tendstoD eventually_conj eventually_ge_at_top)
      then obtain m where m: "m \<ge> N" "dist (f m x) (?f x) < e/2"
        unfolding eventually_at_top_linorder by blast
      have "dist (f n x) (?f x) \<le> dist (f n x) (f m x) + dist (f m x) (?f x)"
          by (rule dist_triangle)
      also from x n have "... < e/2 + e/2" by (intro add_strict_mono N m)
      finally show "dist (f n x) (?f x) < e" by simp
    qed
  qed
qed

lemma uniformly_convergent_Cauchy:
  assumes "uniformly_convergent_on X f"
  shows "uniformly_Cauchy_on X f"
proof (rule uniformly_Cauchy_onI)
  fix e::real assume "e > 0"
  then have "0 < e / 2" by simp
  with assms[unfolded uniformly_convergent_on_def uniform_limit_sequentially_iff]
  obtain l N where l:"x \<in> X \<Longrightarrow> n \<ge> N \<Longrightarrow> dist (f n x) (l x) < e / 2" for n x
    by metis
  from l l have "x \<in> X \<Longrightarrow> n \<ge> N \<Longrightarrow> m \<ge> N \<Longrightarrow> dist (f n x) (f m x) < e" for n m x
    by (rule dist_triangle_half_l)
  then show "\<exists>M. \<forall>x\<in>X. \<forall>m\<ge>M. \<forall>n\<ge>M. dist (f m x) (f n x) < e" by blast
qed

lemma uniformly_convergent_eq_Cauchy:
  "uniformly_convergent_on X f = uniformly_Cauchy_on X f" for f::"nat \<Rightarrow> 'b \<Rightarrow> 'a::complete_space"
  using Cauchy_uniformly_convergent uniformly_convergent_Cauchy by blast

lemma uniformly_convergent_eq_cauchy:
  fixes s::"nat \<Rightarrow> 'b \<Rightarrow> 'a::complete_space"
  shows
    "(\<exists>l. \<forall>e>0. \<exists>N. \<forall>n x. N \<le> n \<and> P x \<longrightarrow> dist(s n x)(l x) < e) \<longleftrightarrow>
      (\<forall>e>0. \<exists>N. \<forall>m n x. N \<le> m \<and> N \<le> n \<and> P x  \<longrightarrow> dist (s m x) (s n x) < e)"
proof -
  have *: "(\<forall>n\<ge>N. \<forall>x. Q x \<longrightarrow> R n x) \<longleftrightarrow> (\<forall>n x. N \<le> n \<and> Q x \<longrightarrow> R n x)"
    "(\<forall>x. Q x \<longrightarrow> (\<forall>m\<ge>N. \<forall>n\<ge>N. S n m x)) \<longleftrightarrow> (\<forall>m n x. N \<le> m \<and> N \<le> n \<and> Q x \<longrightarrow> S n m x)"
    for N::nat and Q::"'b \<Rightarrow> bool" and R S
    by blast+
  show ?thesis
    using uniformly_convergent_eq_Cauchy[of "Collect P" s]
    unfolding uniformly_convergent_on_def uniformly_Cauchy_on_def uniform_limit_sequentially_iff
    by (simp add: *)
qed

lemma uniformly_cauchy_imp_uniformly_convergent:
  fixes s :: "nat \<Rightarrow> 'a \<Rightarrow> 'b::complete_space"
  assumes "\<forall>e>0.\<exists>N. \<forall>m (n::nat) x. N \<le> m \<and> N \<le> n \<and> P x --> dist(s m x)(s n x) < e"
    and "\<forall>x. P x --> (\<forall>e>0. \<exists>N. \<forall>n. N \<le> n \<longrightarrow> dist(s n x)(l x) < e)"
  shows "\<forall>e>0. \<exists>N. \<forall>n x. N \<le> n \<and> P x \<longrightarrow> dist(s n x)(l x) < e"
proof -
  obtain l' where l:"\<forall>e>0. \<exists>N. \<forall>n x. N \<le> n \<and> P x \<longrightarrow> dist (s n x) (l' x) < e"
    using assms(1) unfolding uniformly_convergent_eq_cauchy[symmetric] by auto
  moreover
  {
    fix x
    assume "P x"
    then have "l x = l' x"
      using tendsto_unique[OF trivial_limit_sequentially, of "\<lambda>n. s n x" "l x" "l' x"]
      using l and assms(2) unfolding lim_sequentially by blast
  }
  ultimately show ?thesis by auto
qed

text \<open>TODO: remove explicit formulations
  @{thm uniformly_convergent_eq_cauchy uniformly_cauchy_imp_uniformly_convergent}?!\<close>

lemma uniformly_convergent_imp_convergent:
  "uniformly_convergent_on X f \<Longrightarrow> x \<in> X \<Longrightarrow> convergent (\<lambda>n. f n x)"
  unfolding uniformly_convergent_on_def convergent_def
  by (auto dest: tendsto_uniform_limitI)


subsection \<open>Weierstrass M-Test\<close>

proposition Weierstrass_m_test_ev:
fixes f :: "_ \<Rightarrow> _ \<Rightarrow> _ :: banach"
assumes "eventually (\<lambda>n. \<forall>x\<in>A. norm (f n x) \<le> M n) sequentially"
assumes "summable M"
shows "uniform_limit A (\<lambda>n x. \<Sum>i<n. f i x) (\<lambda>x. suminf (\<lambda>i. f i x)) sequentially"
proof (rule uniform_limitI)
  fix e :: real
  assume "0 < e"
  from suminf_exist_split[OF \<open>0 < e\<close> \<open>summable M\<close>]
  have "\<forall>\<^sub>F k in sequentially. norm (\<Sum>i. M (i + k)) < e"
    by (auto simp: eventually_sequentially)
  with eventually_all_ge_at_top[OF assms(1)]
    show "\<forall>\<^sub>F n in sequentially. \<forall>x\<in>A. dist (\<Sum>i<n. f i x) (\<Sum>i. f i x) < e"
  proof eventually_elim
    case (elim k)
    show ?case
    proof safe
      fix x assume "x \<in> A"
      have "\<exists>N. \<forall>n\<ge>N. norm (f n x) \<le> M n"
        using assms(1) \<open>x \<in> A\<close> by (force simp: eventually_at_top_linorder)
      hence summable_norm_f: "summable (\<lambda>n. norm (f n x))"
        by(rule summable_norm_comparison_test[OF _ \<open>summable M\<close>])
      have summable_f: "summable (\<lambda>n. f n x)"
        using summable_norm_cancel[OF summable_norm_f] .
      have summable_norm_f_plus_k: "summable (\<lambda>i. norm (f (i + k) x))"
        using summable_ignore_initial_segment[OF summable_norm_f]
        by auto
      have summable_M_plus_k: "summable (\<lambda>i. M (i + k))"
        using summable_ignore_initial_segment[OF \<open>summable M\<close>]
        by auto

      have "dist (\<Sum>i<k. f i x) (\<Sum>i. f i x) = norm ((\<Sum>i. f i x) - (\<Sum>i<k. f i x))"
        using dist_norm dist_commute by (subst dist_commute)
      also have "... = norm (\<Sum>i. f (i + k) x)"
        using suminf_minus_initial_segment[OF summable_f, where k=k] by simp
      also have "... \<le> (\<Sum>i. norm (f (i + k) x))"
        using summable_norm[OF summable_norm_f_plus_k] .
      also have "... \<le> (\<Sum>i. M (i + k))"
        by (rule suminf_le[OF _ summable_norm_f_plus_k summable_M_plus_k])
           (insert elim(1) \<open>x \<in> A\<close>, simp)
      finally show "dist (\<Sum>i<k. f i x) (\<Sum>i. f i x) < e"
        using elim by auto
    qed
  qed
qed

text\<open>Alternative version, formulated as in HOL Light\<close>
corollary\<^marker>\<open>tag unimportant\<close> series_comparison_uniform:
  fixes f :: "_ \<Rightarrow> nat \<Rightarrow> _ :: banach"
  assumes g: "summable g" and le: "\<And>n x. N \<le> n \<and> x \<in> A \<Longrightarrow> norm(f x n) \<le> g n"
    shows "\<exists>l. \<forall>e. 0 < e \<longrightarrow> (\<exists>N. \<forall>n x. N \<le> n \<and> x \<in> A \<longrightarrow> dist(sum (f x) {..<n}) (l x) < e)"
proof -
  have 1: "\<forall>\<^sub>F n in sequentially. \<forall>x\<in>A. norm (f x n) \<le> g n"
    using le eventually_sequentially by auto
  show ?thesis
    apply (rule_tac x="(\<lambda>x. \<Sum>i. f x i)" in exI)
    apply (metis (no_types, lifting) eventually_sequentially uniform_limitD [OF Weierstrass_m_test_ev [OF 1 g]])
    done
qed

corollary\<^marker>\<open>tag unimportant\<close> Weierstrass_m_test:
  fixes f :: "_ \<Rightarrow> _ \<Rightarrow> _ :: banach"
  assumes "\<And>n x. x \<in> A \<Longrightarrow> norm (f n x) \<le> M n"
  assumes "summable M"
  shows "uniform_limit A (\<lambda>n x. \<Sum>i<n. f i x) (\<lambda>x. suminf (\<lambda>i. f i x)) sequentially"
  using assms by (intro Weierstrass_m_test_ev always_eventually) auto

corollary\<^marker>\<open>tag unimportant\<close> Weierstrass_m_test'_ev:
  fixes f :: "_ \<Rightarrow> _ \<Rightarrow> _ :: banach"
  assumes "eventually (\<lambda>n. \<forall>x\<in>A. norm (f n x) \<le> M n) sequentially" "summable M"
  shows   "uniformly_convergent_on A (\<lambda>n x. \<Sum>i<n. f i x)"
  unfolding uniformly_convergent_on_def by (rule exI, rule Weierstrass_m_test_ev[OF assms])

corollary\<^marker>\<open>tag unimportant\<close> Weierstrass_m_test':
  fixes f :: "_ \<Rightarrow> _ \<Rightarrow> _ :: banach"
  assumes "\<And>n x. x \<in> A \<Longrightarrow> norm (f n x) \<le> M n" "summable M"
  shows   "uniformly_convergent_on A (\<lambda>n x. \<Sum>i<n. f i x)"
  unfolding uniformly_convergent_on_def by (rule exI, rule Weierstrass_m_test[OF assms])

lemma uniform_limit_eq_rhs: "uniform_limit X f l F \<Longrightarrow> l = m \<Longrightarrow> uniform_limit X f m F"
  by simp


subsection\<^marker>\<open>tag unimportant\<close> \<open>Structural introduction rules\<close>

named_theorems uniform_limit_intros "introduction rules for uniform_limit"
setup \<open>
  Global_Theory.add_thms_dynamic (\<^binding>\<open>uniform_limit_eq_intros\<close>,
    fn context =>
      Named_Theorems.get (Context.proof_of context) \<^named_theorems>\<open>uniform_limit_intros\<close>
      |> map_filter (try (fn thm => @{thm uniform_limit_eq_rhs} OF [thm])))
\<close>

lemma (in bounded_linear) uniform_limit[uniform_limit_intros]:
  assumes "uniform_limit X g l F"
  shows "uniform_limit X (\<lambda>a b. f (g a b)) (\<lambda>a. f (l a)) F"
proof (rule uniform_limitI)
  fix e::real
  from pos_bounded obtain K
    where K: "\<And>x y. dist (f x) (f y) \<le> K * dist x y" "K > 0"
    by (auto simp: ac_simps dist_norm diff[symmetric])
  assume "0 < e" with \<open>K > 0\<close> have "e / K > 0" by simp
  from uniform_limitD[OF assms this]
  show "\<forall>\<^sub>F n in F. \<forall>x\<in>X. dist (f (g n x)) (f (l x)) < e"
    by eventually_elim (metis le_less_trans mult.commute pos_less_divide_eq K)
qed

lemma (in bounded_linear) uniformly_convergent_on:
  assumes "uniformly_convergent_on A g"
  shows   "uniformly_convergent_on A (\<lambda>x y. f (g x y))"
proof -
  from assms obtain l where "uniform_limit A g l sequentially"
    unfolding uniformly_convergent_on_def by blast
  hence "uniform_limit A (\<lambda>x y. f (g x y)) (\<lambda>x. f (l x)) sequentially"
    by (rule uniform_limit)
  thus ?thesis unfolding uniformly_convergent_on_def by blast
qed

lemmas bounded_linear_uniform_limit_intros[uniform_limit_intros] =
  bounded_linear.uniform_limit[OF bounded_linear_Im]
  bounded_linear.uniform_limit[OF bounded_linear_Re]
  bounded_linear.uniform_limit[OF bounded_linear_cnj]
  bounded_linear.uniform_limit[OF bounded_linear_fst]
  bounded_linear.uniform_limit[OF bounded_linear_snd]
  bounded_linear.uniform_limit[OF bounded_linear_zero]
  bounded_linear.uniform_limit[OF bounded_linear_of_real]
  bounded_linear.uniform_limit[OF bounded_linear_inner_left]
  bounded_linear.uniform_limit[OF bounded_linear_inner_right]
  bounded_linear.uniform_limit[OF bounded_linear_divide]
  bounded_linear.uniform_limit[OF bounded_linear_scaleR_right]
  bounded_linear.uniform_limit[OF bounded_linear_mult_left]
  bounded_linear.uniform_limit[OF bounded_linear_mult_right]
  bounded_linear.uniform_limit[OF bounded_linear_scaleR_left]


lemmas uniform_limit_uminus[uniform_limit_intros] =
  bounded_linear.uniform_limit[OF bounded_linear_minus[OF bounded_linear_ident]]

lemma uniform_limit_const[uniform_limit_intros]: "uniform_limit S (\<lambda>x. c) c f"
  by (auto intro!: uniform_limitI)

lemma uniform_limit_add[uniform_limit_intros]:
  fixes f g::"'a \<Rightarrow> 'b \<Rightarrow> 'c::real_normed_vector"
  assumes "uniform_limit X f l F"
  assumes "uniform_limit X g m F"
  shows "uniform_limit X (\<lambda>a b. f a b + g a b) (\<lambda>a. l a + m a) F"
proof (rule uniform_limitI)
  fix e::real
  assume "0 < e"
  hence "0 < e / 2" by simp
  from
    uniform_limitD[OF assms(1) this]
    uniform_limitD[OF assms(2) this]
  show "\<forall>\<^sub>F n in F. \<forall>x\<in>X. dist (f n x + g n x) (l x + m x) < e"
    by eventually_elim (simp add: dist_triangle_add_half)
qed

lemma uniform_limit_minus[uniform_limit_intros]:
  fixes f g::"'a \<Rightarrow> 'b \<Rightarrow> 'c::real_normed_vector"
  assumes "uniform_limit X f l F"
  assumes "uniform_limit X g m F"
  shows "uniform_limit X (\<lambda>a b. f a b - g a b) (\<lambda>a. l a - m a) F"
  unfolding diff_conv_add_uminus
  by (rule uniform_limit_intros assms)+

lemma uniform_limit_norm[uniform_limit_intros]:
  assumes "uniform_limit S g l f"
  shows "uniform_limit S (\<lambda>x y. norm (g x y)) (\<lambda>x. norm (l x)) f"
  using assms
  apply (rule metric_uniform_limit_imp_uniform_limit)
  apply (rule eventuallyI)
  by (metis dist_norm norm_triangle_ineq3 real_norm_def)

lemma (in bounded_bilinear) bounded_uniform_limit[uniform_limit_intros]:
  assumes "uniform_limit X f l F"
  assumes "uniform_limit X g m F"
  assumes "bounded (m ` X)"
  assumes "bounded (l ` X)"
  shows "uniform_limit X (\<lambda>a b. prod (f a b) (g a b)) (\<lambda>a. prod (l a) (m a)) F"
proof (rule uniform_limitI)
  fix e::real
  from pos_bounded obtain K where K:
    "0 < K" "\<And>a b. norm (prod a b) \<le> norm a * norm b * K"
    by auto
  hence "sqrt (K*4) > 0" by simp

  from assms obtain Km Kl
  where Km: "Km > 0" "\<And>x. x \<in> X \<Longrightarrow> norm (m x) \<le> Km"
    and Kl: "Kl > 0" "\<And>x. x \<in> X \<Longrightarrow> norm (l x) \<le> Kl"
    by (auto simp: bounded_pos)
  hence "K * Km * 4 > 0" "K * Kl * 4 > 0"
    using \<open>K > 0\<close>
    by simp_all
  assume "0 < e"

  hence "sqrt e > 0" by simp
  from uniform_limitD[OF assms(1) divide_pos_pos[OF this \<open>sqrt (K*4) > 0\<close>]]
    uniform_limitD[OF assms(2) divide_pos_pos[OF this \<open>sqrt (K*4) > 0\<close>]]
    uniform_limitD[OF assms(1) divide_pos_pos[OF \<open>e > 0\<close> \<open>K * Km * 4 > 0\<close>]]
    uniform_limitD[OF assms(2) divide_pos_pos[OF \<open>e > 0\<close> \<open>K * Kl * 4 > 0\<close>]]
  show "\<forall>\<^sub>F n in F. \<forall>x\<in>X. dist (prod (f n x) (g n x)) (prod (l x) (m x)) < e"
  proof eventually_elim
    case (elim n)
    show ?case
    proof safe
      fix x assume "x \<in> X"
      have "dist (prod (f n x) (g n x)) (prod (l x) (m x)) \<le>
        norm (prod (f n x - l x) (g n x - m x)) +
        norm (prod (f n x - l x) (m x)) +
        norm (prod (l x) (g n x - m x))"
        by (auto simp: dist_norm prod_diff_prod intro: order_trans norm_triangle_ineq add_mono)
      also note K(2)[of "f n x - l x" "g n x - m x"]
      also from elim(1)[THEN bspec, OF \<open>_ \<in> X\<close>, unfolded dist_norm]
      have "norm (f n x - l x) \<le> sqrt e / sqrt (K * 4)"
        by simp
      also from elim(2)[THEN bspec, OF \<open>_ \<in> X\<close>, unfolded dist_norm]
      have "norm (g n x - m x) \<le> sqrt e / sqrt (K * 4)"
        by simp
      also have "sqrt e / sqrt (K * 4) * (sqrt e / sqrt (K * 4)) * K = e / 4"
        using \<open>K > 0\<close> \<open>e > 0\<close> by auto
      also note K(2)[of "f n x - l x" "m x"]
      also note K(2)[of "l x" "g n x - m x"]
      also from elim(3)[THEN bspec, OF \<open>_ \<in> X\<close>, unfolded dist_norm]
      have "norm (f n x - l x) \<le> e / (K * Km * 4)"
        by simp
      also from elim(4)[THEN bspec, OF \<open>_ \<in> X\<close>, unfolded dist_norm]
      have "norm (g n x - m x) \<le> e / (K * Kl * 4)"
        by simp
      also note Kl(2)[OF \<open>_ \<in> X\<close>]
      also note Km(2)[OF \<open>_ \<in> X\<close>]
      also have "e / (K * Km * 4) * Km * K = e / 4"
        using \<open>K > 0\<close> \<open>Km > 0\<close> by simp
      also have " Kl * (e / (K * Kl * 4)) * K = e / 4"
        using \<open>K > 0\<close> \<open>Kl > 0\<close> by simp
      also have "e / 4 + e / 4 + e / 4 < e" using \<open>e > 0\<close> by simp
      finally show "dist (prod (f n x) (g n x)) (prod (l x) (m x)) < e"
        using \<open>K > 0\<close> \<open>Kl > 0\<close> \<open>Km > 0\<close> \<open>e > 0\<close>
        by (simp add: algebra_simps mult_right_mono divide_right_mono)
    qed
  qed
qed

lemmas bounded_bilinear_bounded_uniform_limit_intros[uniform_limit_intros] =
  bounded_bilinear.bounded_uniform_limit[OF Inner_Product.bounded_bilinear_inner]
  bounded_bilinear.bounded_uniform_limit[OF Real_Vector_Spaces.bounded_bilinear_mult]
  bounded_bilinear.bounded_uniform_limit[OF Real_Vector_Spaces.bounded_bilinear_scaleR]

lemma uniform_lim_mult:
  fixes f :: "'a \<Rightarrow> 'b \<Rightarrow> 'c::real_normed_algebra"
  assumes f: "uniform_limit S f l F"
      and g: "uniform_limit S g m F"
      and l: "bounded (l ` S)"
      and m: "bounded (m ` S)"
    shows "uniform_limit S (\<lambda>a b. f a b * g a b) (\<lambda>a. l a * m a) F"
  by (intro bounded_bilinear_bounded_uniform_limit_intros assms)

lemma uniform_lim_inverse:
  fixes f :: "'a \<Rightarrow> 'b \<Rightarrow> 'c::real_normed_field"
  assumes f: "uniform_limit S f l F"
      and b: "\<And>x. x \<in> S \<Longrightarrow> b \<le> norm(l x)"
      and "b > 0"
    shows "uniform_limit S (\<lambda>x y. inverse (f x y)) (inverse \<circ> l) F"
proof (rule uniform_limitI)
  fix e::real
  assume "e > 0"
  have lte: "dist (inverse (f x y)) ((inverse \<circ> l) y) < e"
           if "b/2 \<le> norm (f x y)" "norm (f x y - l y) < e * b\<^sup>2 / 2" "y \<in> S"
           for x y
  proof -
    have [simp]: "l y \<noteq> 0" "f x y \<noteq> 0"
      using \<open>b > 0\<close> that b [OF \<open>y \<in> S\<close>] by fastforce+
    have "norm (l y - f x y) <  e * b\<^sup>2 / 2"
      by (metis norm_minus_commute that(2))
    also have "... \<le> e * (norm (f x y) * norm (l y))"
      using \<open>e > 0\<close> that b [OF \<open>y \<in> S\<close>] apply (simp add: power2_eq_square)
      by (metis \<open>b > 0\<close> less_eq_real_def mult.left_commute mult_mono')
    finally show ?thesis
      by (auto simp: dist_norm field_split_simps norm_mult norm_divide)
  qed
  have "\<forall>\<^sub>F n in F. \<forall>x\<in>S. dist (f n x) (l x) < b/2"
    using uniform_limitD [OF f, of "b/2"] by (simp add: \<open>b > 0\<close>)
  then have "\<forall>\<^sub>F x in F. \<forall>y\<in>S. b/2 \<le> norm (f x y)"
    apply (rule eventually_mono)
    using b apply (simp only: dist_norm)
    by (metis (no_types, opaque_lifting) diff_zero dist_commute dist_norm norm_triangle_half_l not_less)
  then have "\<forall>\<^sub>F x in F. \<forall>y\<in>S. b/2 \<le> norm (f x y) \<and> norm (f x y - l y) < e * b\<^sup>2 / 2"
    apply (simp only: ball_conj_distrib dist_norm [symmetric])
    apply (rule eventually_conj, assumption)
      apply (rule uniform_limitD [OF f, of "e * b ^ 2 / 2"])
    using \<open>b > 0\<close> \<open>e > 0\<close> by auto
  then show "\<forall>\<^sub>F x in F. \<forall>y\<in>S. dist (inverse (f x y)) ((inverse \<circ> l) y) < e"
    using lte by (force intro: eventually_mono)
qed

lemma uniform_lim_divide:
  fixes f :: "'a \<Rightarrow> 'b \<Rightarrow> 'c::real_normed_field"
  assumes f: "uniform_limit S f l F"
      and g: "uniform_limit S g m F"
      and l: "bounded (l ` S)"
      and b: "\<And>x. x \<in> S \<Longrightarrow> b \<le> norm(m x)"
      and "b > 0"
    shows "uniform_limit S (\<lambda>a b. f a b / g a b) (\<lambda>a. l a / m a) F"
proof -
  have m: "bounded ((inverse \<circ> m) ` S)"
    using b \<open>b > 0\<close>
    apply (simp add: bounded_iff)
    by (metis le_imp_inverse_le norm_inverse)
  have "uniform_limit S (\<lambda>a b. f a b * inverse (g a b))
         (\<lambda>a. l a * (inverse \<circ> m) a) F"
    by (rule uniform_lim_mult [OF f uniform_lim_inverse [OF g b \<open>b > 0\<close>] l m])
  then show ?thesis
    by (simp add: field_class.field_divide_inverse)
qed

lemma uniform_limit_null_comparison:
  assumes "\<forall>\<^sub>F x in F. \<forall>a\<in>S. norm (f x a) \<le> g x a"
  assumes "uniform_limit S g (\<lambda>_. 0) F"
  shows "uniform_limit S f (\<lambda>_. 0) F"
  using assms(2)
proof (rule metric_uniform_limit_imp_uniform_limit)
  show "\<forall>\<^sub>F x in F. \<forall>y\<in>S. dist (f x y) 0 \<le> dist (g x y) 0"
    using assms(1) by (rule eventually_mono) (force simp add: dist_norm)
qed

lemma uniform_limit_on_Un:
  "uniform_limit I f g F \<Longrightarrow> uniform_limit J f g F \<Longrightarrow> uniform_limit (I \<union> J) f g F"
  by (auto intro!: uniform_limitI dest!: uniform_limitD elim: eventually_elim2)

lemma uniform_limit_on_empty [iff]:
  "uniform_limit {} f g F"
  by (auto intro!: uniform_limitI)

lemma uniform_limit_on_UNION:
  assumes "finite S"
  assumes "\<And>s. s \<in> S \<Longrightarrow> uniform_limit (h s) f g F"
  shows "uniform_limit (\<Union>(h ` S)) f g F"
  using assms
  by induct (auto intro: uniform_limit_on_empty uniform_limit_on_Un)

lemma uniform_limit_on_Union:
  assumes "finite I"
  assumes "\<And>J. J \<in> I \<Longrightarrow> uniform_limit J f g F"
  shows "uniform_limit (Union I) f g F"
  by (metis SUP_identity_eq assms uniform_limit_on_UNION)

lemma uniform_limit_on_subset:
  "uniform_limit J f g F \<Longrightarrow> I \<subseteq> J \<Longrightarrow> uniform_limit I f g F"
  by (auto intro!: uniform_limitI dest!: uniform_limitD intro: eventually_mono)

lemma uniform_limit_bounded:
  fixes f::"'i \<Rightarrow> 'a::topological_space \<Rightarrow> 'b::metric_space"
  assumes l: "uniform_limit S f l F"
  assumes bnd: "\<forall>\<^sub>F i in F. bounded (f i ` S)"
  assumes "F \<noteq> bot"
  shows "bounded (l ` S)"
proof -
  from l have "\<forall>\<^sub>F n in F. \<forall>x\<in>S. dist (l x) (f n x) < 1"
    by (auto simp: uniform_limit_iff dist_commute dest!: spec[where x=1])
  with bnd
  have "\<forall>\<^sub>F n in F. \<exists>M. \<forall>x\<in>S. dist undefined (l x) \<le> M + 1"
    by eventually_elim
      (auto intro!: order_trans[OF dist_triangle2 add_mono] intro: less_imp_le
        simp: bounded_any_center[where a=undefined])
  then show ?thesis using assms
    by (auto simp: bounded_any_center[where a=undefined] dest!: eventually_happens)
qed

lemma uniformly_convergent_add:
  "uniformly_convergent_on A f \<Longrightarrow> uniformly_convergent_on A g\<Longrightarrow>
      uniformly_convergent_on A (\<lambda>k x. f k x + g k x :: 'a :: {real_normed_algebra})"
  unfolding uniformly_convergent_on_def by (blast dest: uniform_limit_add)

lemma uniformly_convergent_minus:
  "uniformly_convergent_on A f \<Longrightarrow> uniformly_convergent_on A g\<Longrightarrow>
      uniformly_convergent_on A (\<lambda>k x. f k x - g k x :: 'a :: {real_normed_algebra})"
  unfolding uniformly_convergent_on_def by (blast dest: uniform_limit_minus)

lemma uniformly_convergent_mult:
  "uniformly_convergent_on A f \<Longrightarrow>
      uniformly_convergent_on A (\<lambda>k x. c * f k x :: 'a :: {real_normed_algebra})"
  unfolding uniformly_convergent_on_def
  by (blast dest: bounded_linear_uniform_limit_intros(13))

subsection\<open>Power series and uniform convergence\<close>

proposition powser_uniformly_convergent:
  fixes a :: "nat \<Rightarrow> 'a::{real_normed_div_algebra,banach}"
  assumes "r < conv_radius a"
  shows "uniformly_convergent_on (cball \<xi> r) (\<lambda>n x. \<Sum>i<n. a i * (x - \<xi>) ^ i)"
proof (cases "0 \<le> r")
  case True
  then have *: "summable (\<lambda>n. norm (a n) * r ^ n)"
    using abs_summable_in_conv_radius [of "of_real r" a] assms
    by (simp add: norm_mult norm_power)
  show ?thesis
    by (simp add: Weierstrass_m_test'_ev [OF _ *] norm_mult norm_power
              mult_left_mono power_mono dist_norm norm_minus_commute)
next
  case False then show ?thesis by (simp add: not_le)
qed

lemma powser_uniform_limit:
  fixes a :: "nat \<Rightarrow> 'a::{real_normed_div_algebra,banach}"
  assumes "r < conv_radius a"
  shows "uniform_limit (cball \<xi> r) (\<lambda>n x. \<Sum>i<n. a i * (x - \<xi>) ^ i) (\<lambda>x. suminf (\<lambda>i. a i * (x - \<xi>) ^ i)) sequentially"
using powser_uniformly_convergent [OF assms]
by (simp add: Uniform_Limit.uniformly_convergent_uniform_limit_iff Series.suminf_eq_lim)

lemma powser_continuous_suminf:
  fixes a :: "nat \<Rightarrow> 'a::{real_normed_div_algebra,banach}"
  assumes "r < conv_radius a"
  shows "continuous_on (cball \<xi> r) (\<lambda>x. suminf (\<lambda>i. a i * (x - \<xi>) ^ i))"
apply (rule uniform_limit_theorem [OF _ powser_uniform_limit])
apply (rule eventuallyI continuous_intros assms)+
apply (simp add:)
done

lemma powser_continuous_sums:
  fixes a :: "nat \<Rightarrow> 'a::{real_normed_div_algebra,banach}"
  assumes r: "r < conv_radius a"
      and sm: "\<And>x. x \<in> cball \<xi> r \<Longrightarrow> (\<lambda>n. a n * (x - \<xi>) ^ n) sums (f x)"
  shows "continuous_on (cball \<xi> r) f"
apply (rule continuous_on_cong [THEN iffD1, OF refl _ powser_continuous_suminf [OF r]])
using sm sums_unique by fastforce

lemmas uniform_limit_subset_union = uniform_limit_on_subset[OF uniform_limit_on_Union]

end

