(*  Title:     HOL/Probability/Helly_Selection.thy
    Authors:   Jeremy Avigad (CMU), Luke Serafin (CMU)
    Authors:   Johannes Hölzl, TU München
*)

section \<open>Helly's selection theorem\<close>

text \<open>The set of bounded, monotone, right continuous functions is sequentially compact\<close>

theory Helly_Selection
  imports "HOL-Library.Diagonal_Subsequence" Weak_Convergence
begin

lemma minus_one_less: "x - 1 < (x::real)"
  by simp

theorem Helly_selection:
  fixes f :: "nat \<Rightarrow> real \<Rightarrow> real"
  assumes rcont: "\<And>n x. continuous (at_right x) (f n)"
  assumes mono: "\<And>n. mono (f n)"
  assumes bdd: "\<And>n x. \<bar>f n x\<bar> \<le> M"
  shows "\<exists>s. strict_mono (s::nat \<Rightarrow> nat) \<and> (\<exists>F. (\<forall>x. continuous (at_right x) F) \<and> mono F \<and> (\<forall>x. \<bar>F x\<bar> \<le> M) \<and>
    (\<forall>x. continuous (at x) F \<longrightarrow> (\<lambda>n. f (s n) x) \<longlonglongrightarrow> F x))"
proof -
  obtain m :: "real \<Rightarrow> nat" where "bij_betw m \<rat> UNIV"
    using countable_rat Rats_infinite by (erule countableE_infinite)
  then obtain r :: "nat \<Rightarrow> real" where bij: "bij_betw r UNIV \<rat>"
    using bij_betw_inv by blast

  have dense_r: "\<And>x y. x < y \<Longrightarrow> \<exists>n. x < r n \<and> r n < y"
    by (metis Rats_dense_in_real bij f_the_inv_into_f bij_betw_def)

  let ?P = "\<lambda>n. \<lambda>s. convergent (\<lambda>k. f (s k) (r n))"
  interpret nat: subseqs ?P
  proof (unfold convergent_def, unfold subseqs_def, auto)
    fix n :: nat and s :: "nat \<Rightarrow> nat" assume s: "strict_mono s"
    have "bounded {-M..M}"
      using bounded_closed_interval by auto
    moreover have "\<And>k. f (s k) (r n) \<in> {-M..M}"
      using bdd by (simp add: abs_le_iff minus_le_iff)
    ultimately have "\<exists>l s'. strict_mono s' \<and> ((\<lambda>k. f (s k) (r n)) \<circ> s') \<longlonglongrightarrow> l"
      using compact_Icc compact_imp_seq_compact seq_compactE by metis
    thus "\<exists>s'. strict_mono (s'::nat\<Rightarrow>nat) \<and> (\<exists>l. (\<lambda>k. f (s (s' k)) (r n)) \<longlonglongrightarrow> l)"
      by (auto simp: comp_def)
  qed
  define d where "d = nat.diagseq"
  have subseq: "strict_mono d"
    unfolding d_def using nat.subseq_diagseq by auto
  have rat_cnv: "?P n d" for n
  proof -
    have Pn_seqseq: "?P n (nat.seqseq (Suc n))"
      by (rule nat.seqseq_holds)
    have 1: "(\<lambda>k. f ((nat.seqseq (Suc n) \<circ> (\<lambda>k. nat.fold_reduce (Suc n) k
      (Suc n + k))) k) (r n)) = (\<lambda>k. f (nat.seqseq (Suc n) k) (r n)) \<circ>
      (\<lambda>k. nat.fold_reduce (Suc n) k (Suc n + k))"
      by auto
    have 2: "?P n (d \<circ> ((+) (Suc n)))"
      unfolding d_def nat.diagseq_seqseq 1
      by (intro convergent_subseq_convergent Pn_seqseq nat.subseq_diagonal_rest)
    then obtain L where 3: "(\<lambda>na. f (d (na + Suc n)) (r n)) \<longlonglongrightarrow> L"
      by (auto simp: add.commute dest: convergentD)
    then have "(\<lambda>k. f (d k) (r n)) \<longlonglongrightarrow> L"
      by (rule LIMSEQ_offset)
    then show ?thesis
      by (auto simp: convergent_def)
  qed
  let ?f = "\<lambda>n. \<lambda>k. f (d k) (r n)"
  have lim_f: "?f n \<longlonglongrightarrow> lim (?f n)" for n
    using rat_cnv convergent_LIMSEQ_iff by auto
  have lim_bdd: "lim (?f n) \<in> {-M..M}" for n
  proof -
    have "closed {-M..M}" using closed_real_atLeastAtMost by auto
    hence "(\<forall>i. ?f n i \<in> {-M..M}) \<and> ?f n \<longlonglongrightarrow> lim (?f n) \<longrightarrow> lim (?f n) \<in> {-M..M}"
      unfolding closed_sequential_limits by (drule_tac x = "\<lambda>k. f (d k) (r n)" in spec) blast
    moreover have "\<forall>i. ?f n i \<in> {-M..M}"
      using bdd by (simp add: abs_le_iff minus_le_iff)
    ultimately show "lim (?f n) \<in> {-M..M}"
      using lim_f by auto
  qed
  then have limset_bdd: "\<And>x. {lim (?f n) |n. x < r n} \<subseteq> {-M..M}"
    by auto
  then have bdd_below: "bdd_below {lim (?f n) |n. x < r n}" for x
    by (metis (mono_tags) bdd_below_Icc bdd_below_mono)
  have r_unbdd: "\<exists>n. x < r n" for x
    using dense_r[OF less_add_one, of x] by auto
  then have nonempty: "{lim (?f n) |n. x < r n} \<noteq> {}" for x
    by auto

  define F where "F x = Inf {lim (?f n) |n. x < r n}" for x
  have F_eq: "ereal (F x) = (INF n\<in>{n. x < r n}. ereal (lim (?f n)))" for x
    unfolding F_def by (subst ereal_Inf'[OF bdd_below nonempty]) (simp add: setcompr_eq_image image_comp)
  have mono_F: "mono F"
    using nonempty by (auto intro!: cInf_superset_mono simp: F_def bdd_below mono_def)
  moreover have "\<And>x. continuous (at_right x) F"
    unfolding continuous_within order_tendsto_iff eventually_at_right[OF less_add_one]
  proof safe
    show "F x < u \<Longrightarrow> \<exists>b>x. \<forall>y>x. y < b \<longrightarrow> F y < u" for x u
      unfolding F_def cInf_less_iff[OF nonempty bdd_below] by auto
  next
    show "\<exists>b>x. \<forall>y>x. y < b \<longrightarrow> l < F y" if l: "l < F x" for x l
      using less_le_trans[OF l mono_F[THEN monoD, of x]] by (auto intro: less_add_one)
  qed
  moreover
  { fix x
    have "F x \<in> {-M..M}"
      unfolding F_def using limset_bdd bdd_below r_unbdd by (intro closed_subset_contains_Inf) auto
    then have "\<bar>F x\<bar> \<le> M" by auto }
  moreover have "(\<lambda>n. f (d n) x) \<longlonglongrightarrow> F x" if cts: "continuous (at x) F" for x
  proof (rule limsup_le_liminf_real)
    show "limsup (\<lambda>n. f (d n) x) \<le> F x"
    proof (rule tendsto_lowerbound)
      show "(F \<longlongrightarrow> ereal (F x)) (at_right x)"
        using cts unfolding continuous_at_split by (auto simp: continuous_within)
      show "\<forall>\<^sub>F i in at_right x. limsup (\<lambda>n. f (d n) x) \<le> F i"
        unfolding eventually_at_right[OF less_add_one]
      proof (rule, rule, rule less_add_one, safe)
        fix y assume y: "x < y"
        with dense_r obtain N where "x < r N" "r N < y" by auto
        have *: "y < r n' \<Longrightarrow> lim (?f N) \<le> lim (?f n')" for n'
          using \<open>r N < y\<close> by (intro LIMSEQ_le[OF lim_f lim_f]) (auto intro!: mono[THEN monoD])
        have "limsup (\<lambda>n. f (d n) x) \<le> limsup (?f N)"
          using \<open>x < r N\<close> by (auto intro!: Limsup_mono always_eventually mono[THEN monoD])
        also have "\<dots> = lim (\<lambda>n. ereal (?f N n))"
          using rat_cnv[of N] by (force intro!: convergent_limsup_cl simp: convergent_def)
        also have "\<dots> \<le> F y"
          by (auto intro!: INF_greatest * simp: convergent_real_imp_convergent_ereal rat_cnv F_eq)
        finally show "limsup (\<lambda>n. f (d n) x) \<le> F y" .
      qed
    qed simp
    show "F x \<le> liminf (\<lambda>n. f (d n) x)"
    proof (rule tendsto_upperbound)
      show "(F \<longlongrightarrow> ereal (F x)) (at_left x)"
        using cts unfolding continuous_at_split by (auto simp: continuous_within)
      show "\<forall>\<^sub>F i in at_left x. F i \<le> liminf (\<lambda>n. f (d n) x)"
        unfolding eventually_at_left[OF minus_one_less]
      proof (rule, rule, rule minus_one_less, safe)
        fix y assume y: "y < x"
        with dense_r obtain N where "y < r N" "r N < x" by auto
        have "F y \<le> liminf (?f N)"
          using \<open>y < r N\<close> by (auto simp: F_eq convergent_real_imp_convergent_ereal
            rat_cnv convergent_liminf_cl intro!: INF_lower2)
        also have "\<dots> \<le> liminf (\<lambda>n. f (d n) x)"
          using \<open>r N < x\<close> by (auto intro!: Liminf_mono monoD[OF mono] always_eventually)
        finally show "F y \<le> liminf (\<lambda>n. f (d n) x)" .
      qed
    qed simp
  qed
  ultimately show ?thesis using subseq by auto
qed

(** Weak convergence corollaries to Helly's theorem. **)

definition
  tight :: "(nat \<Rightarrow> real measure) \<Rightarrow> bool"
where
  "tight \<mu> \<equiv> (\<forall>n. real_distribution (\<mu> n)) \<and> (\<forall>(\<epsilon>::real)>0. \<exists>a b::real. a < b \<and> (\<forall>n. measure (\<mu> n) {a<..b} > 1 - \<epsilon>))"

(* Can strengthen to equivalence. *)
theorem tight_imp_convergent_subsubsequence:
  assumes \<mu>: "tight \<mu>" "strict_mono s"
  shows "\<exists>r M. strict_mono (r :: nat \<Rightarrow> nat) \<and> real_distribution M \<and> weak_conv_m (\<mu> \<circ> s \<circ> r) M"
proof -
  define f where "f k = cdf (\<mu> (s k))" for k
  interpret \<mu>: real_distribution "\<mu> k" for k
    using \<mu> unfolding tight_def by auto

  have rcont: "\<And>x. continuous (at_right x) (f k)"
    and mono: "mono (f k)"
    and top: "(f k \<longlongrightarrow> 1) at_top"
    and bot: "(f k \<longlongrightarrow> 0) at_bot" for k
    unfolding f_def mono_def
    using \<mu>.cdf_nondecreasing \<mu>.cdf_is_right_cont \<mu>.cdf_lim_at_top_prob \<mu>.cdf_lim_at_bot by auto
  have bdd: "\<bar>f k x\<bar> \<le> 1" for k x
    by (auto simp add: abs_le_iff minus_le_iff f_def \<mu>.cdf_nonneg \<mu>.cdf_bounded_prob)

  from Helly_selection[OF rcont mono bdd, of "\<lambda>x. x"] obtain r F
    where F: "strict_mono r" "\<And>x. continuous (at_right x) F" "mono F" "\<And>x. \<bar>F x\<bar> \<le> 1"
    and lim_F: "\<And>x. continuous (at x) F \<Longrightarrow> (\<lambda>n. f (r n) x) \<longlonglongrightarrow> F x"
    by blast

  have "0 \<le> f n x" for n x
    unfolding f_def by (rule \<mu>.cdf_nonneg)
  have F_nonneg: "0 \<le> F x" for x
  proof -
    obtain y where "y < x" "isCont F y"
      using open_minus_countable[OF mono_ctble_discont[OF \<open>mono F\<close>], of "{..< x}"] by auto
    then have "0 \<le> F y"
      by (intro LIMSEQ_le_const[OF lim_F]) (auto simp: f_def \<mu>.cdf_nonneg)
    also have "\<dots> \<le> F x"
      using \<open>y < x\<close> by (auto intro!: monoD[OF \<open>mono F\<close>])
    finally show "0 \<le> F x" .
  qed

  have Fab: "\<exists>a b. (\<forall>x\<ge>b. F x \<ge> 1 - \<epsilon>) \<and> (\<forall>x\<le>a. F x \<le> \<epsilon>)" if \<epsilon>: "0 < \<epsilon>" for \<epsilon>
  proof auto
    obtain a' b' where a'b': "a' < b'" "\<And>k. measure (\<mu> k) {a'<..b'} > 1 - \<epsilon>"
      using \<epsilon> \<mu> by (auto simp: tight_def)
    obtain a where a: "a < a'" "isCont F a"
      using open_minus_countable[OF mono_ctble_discont[OF \<open>mono F\<close>], of "{..< a'}"] by auto
    obtain b where b: "b' < b" "isCont F b"
      using open_minus_countable[OF mono_ctble_discont[OF \<open>mono F\<close>], of "{b' <..}"] by auto
    have "a < b"
      using a b a'b' by simp

    let ?\<mu> = "\<lambda>k. measure (\<mu> (s (r k)))"
    have ab: "?\<mu> k {a<..b} > 1 - \<epsilon>" for k
    proof -
      have "?\<mu> k {a'<..b'} \<le> ?\<mu> k {a<..b}"
        using a b by (intro \<mu>.finite_measure_mono) auto
      then show ?thesis
        using a'b'(2) by (metis less_eq_real_def less_trans)
    qed

    have "(\<lambda>k. ?\<mu> k {..b}) \<longlonglongrightarrow> F b"
      using b(2) lim_F unfolding f_def cdf_def o_def by auto
    then have "1 - \<epsilon> \<le> F b"
    proof (rule tendsto_lowerbound, intro always_eventually allI)
      fix k
      have "1 - \<epsilon> < ?\<mu> k {a<..b}"
        using ab by auto
      also have "\<dots> \<le> ?\<mu> k {..b}"
        by (auto intro!: \<mu>.finite_measure_mono)
      finally show "1 - \<epsilon> \<le> ?\<mu> k {..b}"
        by (rule less_imp_le)
    qed (rule sequentially_bot)
    then show "\<exists>b. \<forall>x\<ge>b. 1 - \<epsilon> \<le> F x"
      using F unfolding mono_def by (metis order.trans)

    have "(\<lambda>k. ?\<mu> k {..a}) \<longlonglongrightarrow> F a"
      using a(2) lim_F unfolding f_def cdf_def o_def by auto
    then have Fa: "F a \<le> \<epsilon>"
    proof (rule tendsto_upperbound, intro always_eventually allI)
      fix k
      have "?\<mu> k {..a} + ?\<mu> k {a<..b} \<le> 1"
        by (subst \<mu>.finite_measure_Union[symmetric]) auto
      then show "?\<mu> k {..a} \<le> \<epsilon>"
        using ab[of k] by simp
    qed (rule sequentially_bot)
    then show "\<exists>a. \<forall>x\<le>a. F x \<le> \<epsilon>"
      using F unfolding mono_def by (metis order.trans)
  qed

  have "(F \<longlongrightarrow> 1) at_top"
  proof (rule order_tendstoI)
    show "1 < y \<Longrightarrow> \<forall>\<^sub>F x in at_top. F x < y" for y
      using \<open>\<And>x. \<bar>F x\<bar> \<le> 1\<close> \<open>\<And>x. 0 \<le> F x\<close> by (auto intro: le_less_trans always_eventually)
    fix y :: real assume "y < 1"
    then obtain z where "y < z" "z < 1"
      using dense[of y 1] by auto
    with Fab[of "1 - z"] show "\<forall>\<^sub>F x in at_top. y < F x"
      by (auto simp: eventually_at_top_linorder intro: less_le_trans)
  qed
  moreover
  have "(F \<longlongrightarrow> 0) at_bot"
  proof (rule order_tendstoI)
    show "y < 0 \<Longrightarrow> \<forall>\<^sub>F x in at_bot. y < F x" for y
      using \<open>\<And>x. 0 \<le> F x\<close> by (auto intro: less_le_trans always_eventually)
    fix y :: real assume "0 < y"
    then obtain z where "0 < z" "z < y"
      using dense[of 0 y] by auto
    with Fab[of z] show "\<forall>\<^sub>F x in at_bot. F x < y"
      by (auto simp: eventually_at_bot_linorder intro: le_less_trans)
  qed
  ultimately have M: "real_distribution (interval_measure F)" "cdf (interval_measure F) = F"
    using F by (auto intro!: real_distribution_interval_measure cdf_interval_measure simp: mono_def)
  with lim_F LIMSEQ_subseq_LIMSEQ M have "weak_conv_m (\<mu> \<circ> s \<circ> r) (interval_measure F)"
    by (auto simp: weak_conv_def weak_conv_m_def f_def comp_def)
  then show "\<exists>r M. strict_mono (r :: nat \<Rightarrow> nat) \<and> (real_distribution M \<and> weak_conv_m (\<mu> \<circ> s \<circ> r) M)"
    using F M by auto
qed

corollary tight_subseq_weak_converge:
  fixes \<mu> :: "nat \<Rightarrow> real measure" and M :: "real measure"
  assumes "\<And>n. real_distribution (\<mu> n)" "real_distribution M" and tight: "tight \<mu>" and
    subseq: "\<And>s \<nu>. strict_mono s \<Longrightarrow> real_distribution \<nu> \<Longrightarrow> weak_conv_m (\<mu> \<circ> s) \<nu> \<Longrightarrow> weak_conv_m (\<mu> \<circ> s) M"
  shows "weak_conv_m \<mu> M"
proof (rule ccontr)
  define f where "f n = cdf (\<mu> n)" for n
  define F where "F = cdf M"

  assume "\<not> weak_conv_m \<mu> M"
  then obtain x where x: "isCont F x" "\<not> (\<lambda>n. f n x) \<longlonglongrightarrow> F x"
    by (auto simp: weak_conv_m_def weak_conv_def f_def F_def)
  then obtain \<epsilon> where "\<epsilon> > 0" and "infinite {n. \<not> dist (f n x) (F x) < \<epsilon>}"
    by (auto simp: tendsto_iff not_eventually INFM_iff_infinite cofinite_eq_sequentially[symmetric])
  then obtain s :: "nat \<Rightarrow> nat" where s: "\<And>n. \<not> dist (f (s n) x) (F x) < \<epsilon>" and "strict_mono s"
    using enumerate_in_set enumerate_mono by (fastforce simp: strict_mono_def)
  then obtain r \<nu> where r: "strict_mono r" "real_distribution \<nu>" "weak_conv_m (\<mu> \<circ> s \<circ> r) \<nu>"
    using tight_imp_convergent_subsubsequence[OF tight] by blast
  then have "weak_conv_m (\<mu> \<circ> (s \<circ> r)) M"
    using \<open>strict_mono s\<close> r by (intro subseq strict_mono_o) (auto simp: comp_assoc)
  then have "(\<lambda>n. f (s (r n)) x) \<longlonglongrightarrow> F x"
    using x by (auto simp: weak_conv_m_def weak_conv_def F_def f_def)
  then show False
    using s \<open>\<epsilon> > 0\<close> by (auto dest: tendstoD)
qed

end
