(*  Title:      HOL/Analysis/Equivalence_Lebesgue_Henstock_Integration.thy
    Author:     Johannes Hölzl, TU München
    Author:     Robert Himmelmann, TU München
    Huge cleanup by LCP
*)

theory Equivalence_Lebesgue_Henstock_Integration
  imports Lebesgue_Measure Henstock_Kurzweil_Integration Complete_Measure Set_Integral
begin

lemma le_left_mono: "x \<le> y \<Longrightarrow> y \<le> a \<longrightarrow> x \<le> (a::'a::preorder)"
  by (auto intro: order_trans)

lemma ball_trans:
  assumes "y \<in> ball z q" "r + q \<le> s" shows "ball y r \<subseteq> ball z s"
proof safe
  fix x assume x: "x \<in> ball y r"
  have "dist z x \<le> dist z y + dist y x"
    by (rule dist_triangle)
  also have "\<dots> < s"
    using assms x by auto
  finally show "x \<in> ball z s"
    by simp
qed

lemma has_integral_implies_lebesgue_measurable_cbox:
  fixes f :: "'a :: euclidean_space \<Rightarrow> real"
  assumes f: "(f has_integral I) (cbox x y)"
  shows "f \<in> lebesgue_on (cbox x y) \<rightarrow>\<^sub>M borel"
proof (rule cld_measure.borel_measurable_cld)
  let ?L = "lebesgue_on (cbox x y)"
  let ?\<mu> = "emeasure ?L"
  let ?\<mu>' = "outer_measure_of ?L"
  interpret L: finite_measure ?L
  proof
    show "?\<mu> (space ?L) \<noteq> \<infinity>"
      by (simp add: emeasure_restrict_space space_restrict_space emeasure_lborel_cbox_eq)
  qed

  show "cld_measure ?L"
  proof
    fix B A assume "B \<subseteq> A" "A \<in> null_sets ?L"
    then show "B \<in> sets ?L"
      using null_sets_completion_subset[OF \<open>B \<subseteq> A\<close>, of lborel]
      by (auto simp add: null_sets_restrict_space sets_restrict_space_iff intro: )
  next
    fix A assume "A \<subseteq> space ?L" "\<And>B. B \<in> sets ?L \<Longrightarrow> ?\<mu> B < \<infinity> \<Longrightarrow> A \<inter> B \<in> sets ?L"
    from this(1) this(2)[of "space ?L"] show "A \<in> sets ?L"
      by (auto simp: Int_absorb2 less_top[symmetric])
  qed auto
  then interpret cld_measure ?L
    .

  have content_eq_L: "A \<in> sets borel \<Longrightarrow> A \<subseteq> cbox x y \<Longrightarrow> content A = measure ?L A" for A
    by (subst measure_restrict_space) (auto simp: measure_def)

  fix E and a b :: real assume "E \<in> sets ?L" "a < b" "0 < ?\<mu> E" "?\<mu> E < \<infinity>"
  then obtain M :: real where "?\<mu> E = M" "0 < M"
    by (cases "?\<mu> E") auto
  define e where "e = M / (4 + 2 / (b - a))"
  from \<open>a < b\<close> \<open>0<M\<close> have "0 < e"
    by (auto intro!: divide_pos_pos simp: field_simps e_def)

  have "e < M / (3 + 2 / (b - a))"
    using \<open>a < b\<close> \<open>0 < M\<close>
    unfolding e_def by (intro divide_strict_left_mono add_strict_right_mono mult_pos_pos) (auto simp: field_simps)
  then have "2 * e < (b - a) * (M - e * 3)"
    using \<open>0<M\<close> \<open>0 < e\<close> \<open>a < b\<close> by (simp add: field_simps)

  have e_less_M: "e < M / 1"
    unfolding e_def using \<open>a < b\<close> \<open>0<M\<close> by (intro divide_strict_left_mono) (auto simp: field_simps)

  obtain d
    where "gauge d"
      and integral_f: "\<forall>p. p tagged_division_of cbox x y \<and> d fine p \<longrightarrow>
        norm ((\<Sum>(x,k) \<in> p. content k *\<^sub>R f x) - I) < e"
    using \<open>0<e\<close> f unfolding has_integral by auto

  define C where "C X m = X \<inter> {x. ball x (1/Suc m) \<subseteq> d x}" for X m
  have "incseq (C X)" for X
    unfolding C_def [abs_def]
    by (intro monoI Collect_mono conj_mono imp_refl le_left_mono subset_ball divide_left_mono Int_mono) auto

  { fix X assume "X \<subseteq> space ?L" and eq: "?\<mu>' X = ?\<mu> E"
    have "(SUP m. outer_measure_of ?L (C X m)) = outer_measure_of ?L (\<Union>m. C X m)"
      using \<open>X \<subseteq> space ?L\<close> by (intro SUP_outer_measure_of_incseq \<open>incseq (C X)\<close>) (auto simp: C_def)
    also have "(\<Union>m. C X m) = X"
    proof -
      { fix x
        obtain e where "0 < e" "ball x e \<subseteq> d x"
          using gaugeD[OF \<open>gauge d\<close>, of x] unfolding open_contains_ball by auto
        moreover
        obtain n where "1 / (1 + real n) < e"
          using reals_Archimedean[OF \<open>0<e\<close>] by (auto simp: inverse_eq_divide)
        then have "ball x (1 / (1 + real n)) \<subseteq> ball x e"
          by (intro subset_ball) auto
        ultimately have "\<exists>n. ball x (1 / (1 + real n)) \<subseteq> d x"
          by blast }
      then show ?thesis
        by (auto simp: C_def)
    qed
    finally have "(SUP m. outer_measure_of ?L (C X m)) = ?\<mu> E"
      using eq by auto
    also have "\<dots> > M - e"
      using \<open>0 < M\<close> \<open>?\<mu> E = M\<close> \<open>0<e\<close> by (auto intro!: ennreal_lessI)
    finally have "\<exists>m. M - e < outer_measure_of ?L (C X m)"
      unfolding less_SUP_iff by auto }
  note C = this

  let ?E = "{x\<in>E. f x \<le> a}" and ?F = "{x\<in>E. b \<le> f x}"

  have "\<not> (?\<mu>' ?E = ?\<mu> E \<and> ?\<mu>' ?F = ?\<mu> E)"
  proof
    assume eq: "?\<mu>' ?E = ?\<mu> E \<and> ?\<mu>' ?F = ?\<mu> E"
    with C[of ?E] C[of ?F] \<open>E \<in> sets ?L\<close>[THEN sets.sets_into_space] obtain ma mb
      where "M - e < outer_measure_of ?L (C ?E ma)" "M - e < outer_measure_of ?L (C ?F mb)"
      by auto
    moreover define m where "m = max ma mb"
    ultimately have M_minus_e: "M - e < outer_measure_of ?L (C ?E m)" "M - e < outer_measure_of ?L (C ?F m)"
      using
        incseqD[OF \<open>incseq (C ?E)\<close>, of ma m, THEN outer_measure_of_mono]
        incseqD[OF \<open>incseq (C ?F)\<close>, of mb m, THEN outer_measure_of_mono]
      by (auto intro: less_le_trans)
    define d' where "d' x = d x \<inter> ball x (1 / (3 * Suc m))" for x
    have "gauge d'"
      unfolding d'_def by (intro gauge_Int \<open>gauge d\<close> gauge_ball) auto
    then obtain p where p: "p tagged_division_of cbox x y" "d' fine p"
      by (rule fine_division_exists)
    then have "d fine p"
      unfolding d'_def[abs_def] fine_def by auto

    define s where "s = {(x::'a, k). k \<inter> (C ?E m) \<noteq> {} \<and> k \<inter> (C ?F m) \<noteq> {}}"
    define T where "T E k = (SOME x. x \<in> k \<inter> C E m)" for E k
    let ?A = "(\<lambda>(x, k). (T ?E k, k)) ` (p \<inter> s) \<union> (p - s)"
    let ?B = "(\<lambda>(x, k). (T ?F k, k)) ` (p \<inter> s) \<union> (p - s)"

    { fix X assume X_eq: "X = ?E \<or> X = ?F"
      let ?T = "(\<lambda>(x, k). (T X k, k))"
      let ?p = "?T ` (p \<inter> s) \<union> (p - s)"

      have in_s: "(x, k) \<in> s \<Longrightarrow> T X k \<in> k \<inter> C X m" for x k
        using someI_ex[of "\<lambda>x. x \<in> k \<inter> C X m"] X_eq unfolding ex_in_conv by (auto simp: T_def s_def)

      { fix x k assume "(x, k) \<in> p" "(x, k) \<in> s"
        have k: "k \<subseteq> ball x (1 / (3 * Suc m))"
          using \<open>d' fine p\<close>[THEN fineD, OF \<open>(x, k) \<in> p\<close>] by (auto simp: d'_def)
        then have "x \<in> ball (T X k) (1 / (3 * Suc m))"
          using in_s[OF \<open>(x, k) \<in> s\<close>] by (auto simp: C_def subset_eq dist_commute)
        then have "ball x (1 / (3 * Suc m)) \<subseteq> ball (T X k) (1 / Suc m)"
          by (rule ball_trans) (auto simp: divide_simps)
        with k in_s[OF \<open>(x, k) \<in> s\<close>] have "k \<subseteq> d (T X k)"
          by (auto simp: C_def) }
      then have "d fine ?p"
        using \<open>d fine p\<close> by (auto intro!: fineI)
      moreover
      have "?p tagged_division_of cbox x y"
      proof (rule tagged_division_ofI)
        show "finite ?p"
          using p(1) by auto
      next
        fix z k assume *: "(z, k) \<in> ?p"
        then consider "(z, k) \<in> p" "(z, k) \<notin> s"
          | x' where "(x', k) \<in> p" "(x', k) \<in> s" "z = T X k"
          by (auto simp: T_def)
        then have "z \<in> k \<and> k \<subseteq> cbox x y \<and> (\<exists>a b. k = cbox a b)"
          using p(1) by cases (auto dest: in_s)
        then show "z \<in> k" "k \<subseteq> cbox x y" "\<exists>a b. k = cbox a b"
          by auto
      next
        fix z k z' k' assume "(z, k) \<in> ?p" "(z', k') \<in> ?p" "(z, k) \<noteq> (z', k')"
        with tagged_division_ofD(5)[OF p(1), of _ k _ k']
        show "interior k \<inter> interior k' = {}"
          by (auto simp: T_def dest: in_s)
      next
        have "{k. \<exists>x. (x, k) \<in> ?p} = {k. \<exists>x. (x, k) \<in> p}"
          by (auto simp: T_def image_iff Bex_def)
        then show "\<Union>{k. \<exists>x. (x, k) \<in> ?p} = cbox x y"
          using p(1) by auto
      qed
      ultimately have I: "norm ((\<Sum>(x,k) \<in> ?p. content k *\<^sub>R f x) - I) < e"
        using integral_f by auto

      have "(\<Sum>(x,k) \<in> ?p. content k *\<^sub>R f x) =
        (\<Sum>(x,k) \<in> ?T ` (p \<inter> s). content k *\<^sub>R f x) + (\<Sum>(x,k) \<in> p - s. content k *\<^sub>R f x)"
        using p(1)[THEN tagged_division_ofD(1)]
        by (safe intro!: sum.union_inter_neutral) (auto simp: s_def T_def)
      also have "(\<Sum>(x,k) \<in> ?T ` (p \<inter> s). content k *\<^sub>R f x) = (\<Sum>(x,k) \<in> p \<inter> s. content k *\<^sub>R f (T X k))"
      proof (subst sum.reindex_nontrivial, safe)
        fix x1 x2 k assume 1: "(x1, k) \<in> p" "(x1, k) \<in> s" and 2: "(x2, k) \<in> p" "(x2, k) \<in> s"
          and eq: "content k *\<^sub>R f (T X k) \<noteq> 0"
        with tagged_division_ofD(5)[OF p(1), of x1 k x2 k] tagged_division_ofD(4)[OF p(1), of x1 k]
        show "x1 = x2"
          by (auto simp: content_eq_0_interior)
      qed (use p in \<open>auto intro!: sum.cong\<close>)
      finally have eq: "(\<Sum>(x,k) \<in> ?p. content k *\<^sub>R f x) =
        (\<Sum>(x,k) \<in> p \<inter> s. content k *\<^sub>R f (T X k)) + (\<Sum>(x,k) \<in> p - s. content k *\<^sub>R f x)" .

      have in_T: "(x, k) \<in> s \<Longrightarrow> T X k \<in> X" for x k
        using in_s[of x k] by (auto simp: C_def)

      note I eq in_T }
    note parts = this

    have p_in_L: "(x, k) \<in> p \<Longrightarrow> k \<in> sets ?L" for x k
      using tagged_division_ofD(3, 4)[OF p(1), of x k] by (auto simp: sets_restrict_space)

    have [simp]: "finite p"
      using tagged_division_ofD(1)[OF p(1)] .

    have "(M - 3*e) * (b - a) \<le> (\<Sum>(x,k) \<in> p \<inter> s. content k) * (b - a)"
    proof (intro mult_right_mono)
      have fin: "?\<mu> (E \<inter> \<Union>{k\<in>snd`p. k \<inter> C X m = {}}) < \<infinity>" for X
        using \<open>?\<mu> E < \<infinity>\<close> by (rule le_less_trans[rotated]) (auto intro!: emeasure_mono \<open>E \<in> sets ?L\<close>)
      have sets: "(E \<inter> \<Union>{k\<in>snd`p. k \<inter> C X m = {}}) \<in> sets ?L" for X
        using tagged_division_ofD(1)[OF p(1)] by (intro sets.Diff \<open>E \<in> sets ?L\<close> sets.finite_Union sets.Int) (auto intro: p_in_L)
      { fix X assume "X \<subseteq> E" "M - e < ?\<mu>' (C X m)"
        have "M - e \<le> ?\<mu>' (C X m)"
          by (rule less_imp_le) fact
        also have "\<dots> \<le> ?\<mu>' (E - (E \<inter> \<Union>{k\<in>snd`p. k \<inter> C X m = {}}))"
        proof (intro outer_measure_of_mono subsetI)
          fix v assume "v \<in> C X m"
          then have "v \<in> cbox x y" "v \<in> E"
            using \<open>E \<subseteq> space ?L\<close> \<open>X \<subseteq> E\<close> by (auto simp: space_restrict_space C_def)
          then obtain z k where "(z, k) \<in> p" "v \<in> k"
            using tagged_division_ofD(6)[OF p(1), symmetric] by auto
          then show "v \<in> E - E \<inter> (\<Union>{k\<in>snd`p. k \<inter> C X m = {}})"
            using \<open>v \<in> C X m\<close> \<open>v \<in> E\<close> by auto
        qed
        also have "\<dots> = ?\<mu> E - ?\<mu> (E \<inter> \<Union>{k\<in>snd`p. k \<inter> C X m = {}})"
          using \<open>E \<in> sets ?L\<close> fin[of X] sets[of X] by (auto intro!: emeasure_Diff)
        finally have "?\<mu> (E \<inter> \<Union>{k\<in>snd`p. k \<inter> C X m = {}}) \<le> e"
          using \<open>0 < e\<close> e_less_M apply (cases "?\<mu> (E \<inter> \<Union>{k\<in>snd`p. k \<inter> C X m = {}})")
          by (auto simp add: \<open>?\<mu> E = M\<close> ennreal_minus ennreal_le_iff2)
        note this }
      note upper_bound = this

      have "?\<mu> (E \<inter> \<Union>(snd`(p - s))) =
        ?\<mu> ((E \<inter> \<Union>{k\<in>snd`p. k \<inter> C ?E m = {}}) \<union> (E \<inter> \<Union>{k\<in>snd`p. k \<inter> C ?F m = {}}))"
        by (intro arg_cong[where f="?\<mu>"]) (auto simp: s_def image_def Bex_def)
      also have "\<dots> \<le> ?\<mu> (E \<inter> \<Union>{k\<in>snd`p. k \<inter> C ?E m = {}}) + ?\<mu> (E \<inter> \<Union>{k\<in>snd`p. k \<inter> C ?F m = {}})"
        using sets[of ?E] sets[of ?F] M_minus_e by (intro emeasure_subadditive) auto
      also have "\<dots> \<le> e + ennreal e"
        using upper_bound[of ?E] upper_bound[of ?F] M_minus_e by (intro add_mono) auto
      finally have "?\<mu> E - 2*e \<le> ?\<mu> (E - (E \<inter> \<Union>(snd`(p - s))))"
        using \<open>0 < e\<close> \<open>E \<in> sets ?L\<close> tagged_division_ofD(1)[OF p(1)]
        by (subst emeasure_Diff)
           (auto simp: top_unique simp flip: ennreal_plus
                 intro!: sets.Int sets.finite_UN ennreal_mono_minus intro: p_in_L)
      also have "\<dots> \<le> ?\<mu> (\<Union>x\<in>p \<inter> s. snd x)"
      proof (safe intro!: emeasure_mono subsetI)
        fix v assume "v \<in> E" and not: "v \<notin> (\<Union>x\<in>p \<inter> s. snd x)"
        then have "v \<in> cbox x y"
          using \<open>E \<subseteq> space ?L\<close> by (auto simp: space_restrict_space)
        then obtain z k where "(z, k) \<in> p" "v \<in> k"
          using tagged_division_ofD(6)[OF p(1), symmetric] by auto
        with not show "v \<in> UNION (p - s) snd"
          by (auto intro!: bexI[of _ "(z, k)"] elim: ballE[of _ _ "(z, k)"])
      qed (auto intro!: sets.Int sets.finite_UN ennreal_mono_minus intro: p_in_L)
      also have "\<dots> = measure ?L (\<Union>x\<in>p \<inter> s. snd x)"
        by (auto intro!: emeasure_eq_ennreal_measure)
      finally have "M - 2 * e \<le> measure ?L (\<Union>x\<in>p \<inter> s. snd x)"
        unfolding \<open>?\<mu> E = M\<close> using \<open>0 < e\<close> by (simp add: ennreal_minus)
      also have "measure ?L (\<Union>x\<in>p \<inter> s. snd x) = content (\<Union>x\<in>p \<inter> s. snd x)"
        using tagged_division_ofD(1,3,4) [OF p(1)]
        by (intro content_eq_L[symmetric])
           (fastforce intro!: sets.finite_UN UN_least del: subsetI)+
      also have "content (\<Union>x\<in>p \<inter> s. snd x) \<le> (\<Sum>k\<in>p \<inter> s. content (snd k))"
        using p(1) by (auto simp: emeasure_lborel_cbox_eq intro!: measure_subadditive_finite
                            dest!: p(1)[THEN tagged_division_ofD(4)])
      finally show "M - 3 * e \<le> (\<Sum>(x, y)\<in>p \<inter> s. content y)"
        using \<open>0 < e\<close> by (simp add: split_beta)
    qed (use \<open>a < b\<close> in auto)
    also have "\<dots> = (\<Sum>(x,k) \<in> p \<inter> s. content k * (b - a))"
      by (simp add: sum_distrib_right split_beta')
    also have "\<dots> \<le> (\<Sum>(x,k) \<in> p \<inter> s. content k * (f (T ?F k) - f (T ?E k)))"
      using parts(3) by (auto intro!: sum_mono mult_left_mono diff_mono)
    also have "\<dots> = (\<Sum>(x,k) \<in> p \<inter> s. content k * f (T ?F k)) - (\<Sum>(x,k) \<in> p \<inter> s. content k * f (T ?E k))"
      by (auto intro!: sum.cong simp: field_simps sum_subtractf[symmetric])
    also have "\<dots> = (\<Sum>(x,k) \<in> ?B. content k *\<^sub>R f x) - (\<Sum>(x,k) \<in> ?A. content k *\<^sub>R f x)"
      by (subst (1 2) parts) auto
    also have "\<dots> \<le> norm ((\<Sum>(x,k) \<in> ?B. content k *\<^sub>R f x) - (\<Sum>(x,k) \<in> ?A. content k *\<^sub>R f x))"
      by auto
    also have "\<dots> \<le> e + e"
      using parts(1)[of ?E] parts(1)[of ?F] by (intro norm_diff_triangle_le[of _ I]) auto
    finally show False
      using \<open>2 * e < (b - a) * (M - e * 3)\<close> by (auto simp: field_simps)
  qed
  moreover have "?\<mu>' ?E \<le> ?\<mu> E" "?\<mu>' ?F \<le> ?\<mu> E"
    unfolding outer_measure_of_eq[OF \<open>E \<in> sets ?L\<close>, symmetric] by (auto intro!: outer_measure_of_mono)
  ultimately show "min (?\<mu>' ?E) (?\<mu>' ?F) < ?\<mu> E"
    unfolding min_less_iff_disj by (auto simp: less_le)
qed

lemma has_integral_implies_lebesgue_measurable_real:
  fixes f :: "'a :: euclidean_space \<Rightarrow> real"
  assumes f: "(f has_integral I) \<Omega>"
  shows "(\<lambda>x. f x * indicator \<Omega> x) \<in> lebesgue \<rightarrow>\<^sub>M borel"
proof -
  define B :: "nat \<Rightarrow> 'a set" where "B n = cbox (- real n *\<^sub>R One) (real n *\<^sub>R One)" for n
  show "(\<lambda>x. f x * indicator \<Omega> x) \<in> lebesgue \<rightarrow>\<^sub>M borel"
  proof (rule measurable_piecewise_restrict)
    have "(\<Union>n. box (- real n *\<^sub>R One) (real n *\<^sub>R One)) \<subseteq> UNION UNIV B"
      unfolding B_def by (intro UN_mono box_subset_cbox order_refl)
    then show "countable (range B)" "space lebesgue \<subseteq> UNION UNIV B"
      by (auto simp: B_def UN_box_eq_UNIV)
  next
    fix \<Omega>' assume "\<Omega>' \<in> range B"
    then obtain n where \<Omega>': "\<Omega>' = B n" by auto
    then show "\<Omega>' \<inter> space lebesgue \<in> sets lebesgue"
      by (auto simp: B_def)

    have "f integrable_on \<Omega>"
      using f by auto
    then have "(\<lambda>x. f x * indicator \<Omega> x) integrable_on \<Omega>"
      by (auto simp: integrable_on_def cong: has_integral_cong)
    then have "(\<lambda>x. f x * indicator \<Omega> x) integrable_on (\<Omega> \<union> B n)"
      by (rule integrable_on_superset) auto
    then have "(\<lambda>x. f x * indicator \<Omega> x) integrable_on B n"
      unfolding B_def by (rule integrable_on_subcbox) auto
    then show "(\<lambda>x. f x * indicator \<Omega> x) \<in> lebesgue_on \<Omega>' \<rightarrow>\<^sub>M borel"
      unfolding B_def \<Omega>' by (auto intro: has_integral_implies_lebesgue_measurable_cbox simp: integrable_on_def)
  qed
qed

lemma has_integral_implies_lebesgue_measurable:
  fixes f :: "'a :: euclidean_space \<Rightarrow> 'b :: euclidean_space"
  assumes f: "(f has_integral I) \<Omega>"
  shows "(\<lambda>x. indicator \<Omega> x *\<^sub>R f x) \<in> lebesgue \<rightarrow>\<^sub>M borel"
proof (intro borel_measurable_euclidean_space[where 'c='b, THEN iffD2] ballI)
  fix i :: "'b" assume "i \<in> Basis"
  have "(\<lambda>x. (f x \<bullet> i) * indicator \<Omega> x) \<in> borel_measurable (completion lborel)"
    using has_integral_linear[OF f bounded_linear_inner_left, of i]
    by (intro has_integral_implies_lebesgue_measurable_real) (auto simp: comp_def)
  then show "(\<lambda>x. indicator \<Omega> x *\<^sub>R f x \<bullet> i) \<in> borel_measurable (completion lborel)"
    by (simp add: ac_simps)
qed

subsection \<open>Equivalence Lebesgue integral on @{const lborel} and HK-integral\<close>

lemma has_integral_measure_lborel:
  fixes A :: "'a::euclidean_space set"
  assumes A[measurable]: "A \<in> sets borel" and finite: "emeasure lborel A < \<infinity>"
  shows "((\<lambda>x. 1) has_integral measure lborel A) A"
proof -
  { fix l u :: 'a
    have "((\<lambda>x. 1) has_integral measure lborel (box l u)) (box l u)"
    proof cases
      assume "\<forall>b\<in>Basis. l \<bullet> b \<le> u \<bullet> b"
      then show ?thesis
        apply simp
        apply (subst has_integral_restrict[symmetric, OF box_subset_cbox])
        apply (subst has_integral_spike_interior_eq[where g="\<lambda>_. 1"])
        using has_integral_const[of "1::real" l u]
        apply (simp_all add: inner_diff_left[symmetric] content_cbox_cases)
        done
    next
      assume "\<not> (\<forall>b\<in>Basis. l \<bullet> b \<le> u \<bullet> b)"
      then have "box l u = {}"
        unfolding box_eq_empty by (auto simp: not_le intro: less_imp_le)
      then show ?thesis
        by simp
    qed }
  note has_integral_box = this

  { fix a b :: 'a let ?M = "\<lambda>A. measure lborel (A \<inter> box a b)"
    have "Int_stable  (range (\<lambda>(a, b). box a b))"
      by (auto simp: Int_stable_def box_Int_box)
    moreover have "(range (\<lambda>(a, b). box a b)) \<subseteq> Pow UNIV"
      by auto
    moreover have "A \<in> sigma_sets UNIV (range (\<lambda>(a, b). box a b))"
       using A unfolding borel_eq_box by simp
    ultimately have "((\<lambda>x. 1) has_integral ?M A) (A \<inter> box a b)"
    proof (induction rule: sigma_sets_induct_disjoint)
      case (basic A) then show ?case
        by (auto simp: box_Int_box has_integral_box)
    next
      case empty then show ?case
        by simp
    next
      case (compl A)
      then have [measurable]: "A \<in> sets borel"
        by (simp add: borel_eq_box)

      have "((\<lambda>x. 1) has_integral ?M (box a b)) (box a b)"
        by (simp add: has_integral_box)
      moreover have "((\<lambda>x. if x \<in> A \<inter> box a b then 1 else 0) has_integral ?M A) (box a b)"
        by (subst has_integral_restrict) (auto intro: compl)
      ultimately have "((\<lambda>x. 1 - (if x \<in> A \<inter> box a b then 1 else 0)) has_integral ?M (box a b) - ?M A) (box a b)"
        by (rule has_integral_diff)
      then have "((\<lambda>x. (if x \<in> (UNIV - A) \<inter> box a b then 1 else 0)) has_integral ?M (box a b) - ?M A) (box a b)"
        by (rule has_integral_cong[THEN iffD1, rotated 1]) auto
      then have "((\<lambda>x. 1) has_integral ?M (box a b) - ?M A) ((UNIV - A) \<inter> box a b)"
        by (subst (asm) has_integral_restrict) auto
      also have "?M (box a b) - ?M A = ?M (UNIV - A)"
        by (subst measure_Diff[symmetric]) (auto simp: emeasure_lborel_box_eq Diff_Int_distrib2)
      finally show ?case .
    next
      case (union F)
      then have [measurable]: "\<And>i. F i \<in> sets borel"
        by (simp add: borel_eq_box subset_eq)
      have "((\<lambda>x. if x \<in> UNION UNIV F \<inter> box a b then 1 else 0) has_integral ?M (\<Union>i. F i)) (box a b)"
      proof (rule has_integral_monotone_convergence_increasing)
        let ?f = "\<lambda>k x. \<Sum>i<k. if x \<in> F i \<inter> box a b then 1 else 0 :: real"
        show "\<And>k. (?f k has_integral (\<Sum>i<k. ?M (F i))) (box a b)"
          using union.IH by (auto intro!: has_integral_sum simp del: Int_iff)
        show "\<And>k x. ?f k x \<le> ?f (Suc k) x"
          by (intro sum_mono2) auto
        from union(1) have *: "\<And>x i j. x \<in> F i \<Longrightarrow> x \<in> F j \<longleftrightarrow> j = i"
          by (auto simp add: disjoint_family_on_def)
        show "\<And>x. (\<lambda>k. ?f k x) \<longlonglongrightarrow> (if x \<in> UNION UNIV F \<inter> box a b then 1 else 0)"
          apply (auto simp: * sum.If_cases Iio_Int_singleton)
          apply (rule_tac k="Suc xa" in LIMSEQ_offset)
          apply simp
          done
        have *: "emeasure lborel ((\<Union>x. F x) \<inter> box a b) \<le> emeasure lborel (box a b)"
          by (intro emeasure_mono) auto

        with union(1) show "(\<lambda>k. \<Sum>i<k. ?M (F i)) \<longlonglongrightarrow> ?M (\<Union>i. F i)"
          unfolding sums_def[symmetric] UN_extend_simps
          by (intro measure_UNION) (auto simp: disjoint_family_on_def emeasure_lborel_box_eq top_unique)
      qed
      then show ?case
        by (subst (asm) has_integral_restrict) auto
    qed }
  note * = this

  show ?thesis
  proof (rule has_integral_monotone_convergence_increasing)
    let ?B = "\<lambda>n::nat. box (- real n *\<^sub>R One) (real n *\<^sub>R One) :: 'a set"
    let ?f = "\<lambda>n::nat. \<lambda>x. if x \<in> A \<inter> ?B n then 1 else 0 :: real"
    let ?M = "\<lambda>n. measure lborel (A \<inter> ?B n)"

    show "\<And>n::nat. (?f n has_integral ?M n) A"
      using * by (subst has_integral_restrict) simp_all
    show "\<And>k x. ?f k x \<le> ?f (Suc k) x"
      by (auto simp: box_def)
    { fix x assume "x \<in> A"
      moreover have "(\<lambda>k. indicator (A \<inter> ?B k) x :: real) \<longlonglongrightarrow> indicator (\<Union>k::nat. A \<inter> ?B k) x"
        by (intro LIMSEQ_indicator_incseq) (auto simp: incseq_def box_def)
      ultimately show "(\<lambda>k. if x \<in> A \<inter> ?B k then 1 else 0::real) \<longlonglongrightarrow> 1"
        by (simp add: indicator_def UN_box_eq_UNIV) }

    have "(\<lambda>n. emeasure lborel (A \<inter> ?B n)) \<longlonglongrightarrow> emeasure lborel (\<Union>n::nat. A \<inter> ?B n)"
      by (intro Lim_emeasure_incseq) (auto simp: incseq_def box_def)
    also have "(\<lambda>n. emeasure lborel (A \<inter> ?B n)) = (\<lambda>n. measure lborel (A \<inter> ?B n))"
    proof (intro ext emeasure_eq_ennreal_measure)
      fix n have "emeasure lborel (A \<inter> ?B n) \<le> emeasure lborel (?B n)"
        by (intro emeasure_mono) auto
      then show "emeasure lborel (A \<inter> ?B n) \<noteq> top"
        by (auto simp: top_unique)
    qed
    finally show "(\<lambda>n. measure lborel (A \<inter> ?B n)) \<longlonglongrightarrow> measure lborel A"
      using emeasure_eq_ennreal_measure[of lborel A] finite
      by (simp add: UN_box_eq_UNIV less_top)
  qed
qed

lemma nn_integral_has_integral:
  fixes f::"'a::euclidean_space \<Rightarrow> real"
  assumes f: "f \<in> borel_measurable borel" "\<And>x. 0 \<le> f x" "(\<integral>\<^sup>+x. f x \<partial>lborel) = ennreal r" "0 \<le> r"
  shows "(f has_integral r) UNIV"
using f proof (induct f arbitrary: r rule: borel_measurable_induct_real)
  case (set A)
  then have "((\<lambda>x. 1) has_integral measure lborel A) A"
    by (intro has_integral_measure_lborel) (auto simp: ennreal_indicator)
  with set show ?case
    by (simp add: ennreal_indicator measure_def) (simp add: indicator_def)
next
  case (mult g c)
  then have "ennreal c * (\<integral>\<^sup>+ x. g x \<partial>lborel) = ennreal r"
    by (subst nn_integral_cmult[symmetric]) (auto simp: ennreal_mult)
  with \<open>0 \<le> r\<close> \<open>0 \<le> c\<close>
  obtain r' where "(c = 0 \<and> r = 0) \<or> (0 \<le> r' \<and> (\<integral>\<^sup>+ x. ennreal (g x) \<partial>lborel) = ennreal r' \<and> r = c * r')"
    by (cases "\<integral>\<^sup>+ x. ennreal (g x) \<partial>lborel" rule: ennreal_cases)
       (auto split: if_split_asm simp: ennreal_mult_top ennreal_mult[symmetric])
  with mult show ?case
    by (auto intro!: has_integral_cmult_real)
next
  case (add g h)
  then have "(\<integral>\<^sup>+ x. h x + g x \<partial>lborel) = (\<integral>\<^sup>+ x. h x \<partial>lborel) + (\<integral>\<^sup>+ x. g x \<partial>lborel)"
    by (simp add: nn_integral_add)
  with add obtain a b where "0 \<le> a" "0 \<le> b" "(\<integral>\<^sup>+ x. h x \<partial>lborel) = ennreal a" "(\<integral>\<^sup>+ x. g x \<partial>lborel) = ennreal b" "r = a + b"
    by (cases "\<integral>\<^sup>+ x. h x \<partial>lborel" "\<integral>\<^sup>+ x. g x \<partial>lborel" rule: ennreal2_cases)
       (auto simp: add_top nn_integral_add top_add simp flip: ennreal_plus)
  with add show ?case
    by (auto intro!: has_integral_add)
next
  case (seq U)
  note seq(1)[measurable] and f[measurable]

  { fix i x
    have "U i x \<le> f x"
      using seq(5)
      apply (rule LIMSEQ_le_const)
      using seq(4)
      apply (auto intro!: exI[of _ i] simp: incseq_def le_fun_def)
      done }
  note U_le_f = this

  { fix i
    have "(\<integral>\<^sup>+x. U i x \<partial>lborel) \<le> (\<integral>\<^sup>+x. f x \<partial>lborel)"
      using seq(2) f(2) U_le_f by (intro nn_integral_mono) simp
    then obtain p where "(\<integral>\<^sup>+x. U i x \<partial>lborel) = ennreal p" "p \<le> r" "0 \<le> p"
      using seq(6) \<open>0\<le>r\<close> by (cases "\<integral>\<^sup>+x. U i x \<partial>lborel" rule: ennreal_cases) (auto simp: top_unique)
    moreover note seq
    ultimately have "\<exists>p. (\<integral>\<^sup>+x. U i x \<partial>lborel) = ennreal p \<and> 0 \<le> p \<and> p \<le> r \<and> (U i has_integral p) UNIV"
      by auto }
  then obtain p where p: "\<And>i. (\<integral>\<^sup>+x. ennreal (U i x) \<partial>lborel) = ennreal (p i)"
    and bnd: "\<And>i. p i \<le> r" "\<And>i. 0 \<le> p i"
    and U_int: "\<And>i.(U i has_integral (p i)) UNIV" by metis

  have int_eq: "\<And>i. integral UNIV (U i) = p i" using U_int by (rule integral_unique)

  have *: "f integrable_on UNIV \<and> (\<lambda>k. integral UNIV (U k)) \<longlonglongrightarrow> integral UNIV f"
  proof (rule monotone_convergence_increasing)
    show "\<And>k. U k integrable_on UNIV" using U_int by auto
    show "\<And>k x. x\<in>UNIV \<Longrightarrow> U k x \<le> U (Suc k) x" using \<open>incseq U\<close> by (auto simp: incseq_def le_fun_def)
    then show "bounded (range (\<lambda>k. integral UNIV (U k)))"
      using bnd int_eq by (auto simp: bounded_real intro!: exI[of _ r])
    show "\<And>x. x\<in>UNIV \<Longrightarrow> (\<lambda>k. U k x) \<longlonglongrightarrow> f x"
      using seq by auto
  qed
  moreover have "(\<lambda>i. (\<integral>\<^sup>+x. U i x \<partial>lborel)) \<longlonglongrightarrow> (\<integral>\<^sup>+x. f x \<partial>lborel)"
    using seq f(2) U_le_f by (intro nn_integral_dominated_convergence[where w=f]) auto
  ultimately have "integral UNIV f = r"
    by (auto simp add: bnd int_eq p seq intro: LIMSEQ_unique)
  with * show ?case
    by (simp add: has_integral_integral)
qed

lemma nn_integral_lborel_eq_integral:
  fixes f::"'a::euclidean_space \<Rightarrow> real"
  assumes f: "f \<in> borel_measurable borel" "\<And>x. 0 \<le> f x" "(\<integral>\<^sup>+x. f x \<partial>lborel) < \<infinity>"
  shows "(\<integral>\<^sup>+x. f x \<partial>lborel) = integral UNIV f"
proof -
  from f(3) obtain r where r: "(\<integral>\<^sup>+x. f x \<partial>lborel) = ennreal r" "0 \<le> r"
    by (cases "\<integral>\<^sup>+x. f x \<partial>lborel" rule: ennreal_cases) auto
  then show ?thesis
    using nn_integral_has_integral[OF f(1,2) r] by (simp add: integral_unique)
qed

lemma nn_integral_integrable_on:
  fixes f::"'a::euclidean_space \<Rightarrow> real"
  assumes f: "f \<in> borel_measurable borel" "\<And>x. 0 \<le> f x" "(\<integral>\<^sup>+x. f x \<partial>lborel) < \<infinity>"
  shows "f integrable_on UNIV"
proof -
  from f(3) obtain r where r: "(\<integral>\<^sup>+x. f x \<partial>lborel) = ennreal r" "0 \<le> r"
    by (cases "\<integral>\<^sup>+x. f x \<partial>lborel" rule: ennreal_cases) auto
  then show ?thesis
    by (intro has_integral_integrable[where i=r] nn_integral_has_integral[where r=r] f)
qed

lemma nn_integral_has_integral_lborel:
  fixes f :: "'a::euclidean_space \<Rightarrow> real"
  assumes f_borel: "f \<in> borel_measurable borel" and nonneg: "\<And>x. 0 \<le> f x"
  assumes I: "(f has_integral I) UNIV"
  shows "integral\<^sup>N lborel f = I"
proof -
  from f_borel have "(\<lambda>x. ennreal (f x)) \<in> borel_measurable lborel" by auto
  from borel_measurable_implies_simple_function_sequence'[OF this] 
  obtain F where F: "\<And>i. simple_function lborel (F i)" "incseq F" 
                 "\<And>i x. F i x < top" "\<And>x. (SUP i. F i x) = ennreal (f x)"
    by blast
  then have [measurable]: "\<And>i. F i \<in> borel_measurable lborel"
    by (metis borel_measurable_simple_function)
  let ?B = "\<lambda>i::nat. box (- (real i *\<^sub>R One)) (real i *\<^sub>R One) :: 'a set"

  have "0 \<le> I"
    using I by (rule has_integral_nonneg) (simp add: nonneg)

  have F_le_f: "enn2real (F i x) \<le> f x" for i x
    using F(3,4)[where x=x] nonneg SUP_upper[of i UNIV "\<lambda>i. F i x"]
    by (cases "F i x" rule: ennreal_cases) auto
  let ?F = "\<lambda>i x. F i x * indicator (?B i) x"
  have "(\<integral>\<^sup>+ x. ennreal (f x) \<partial>lborel) = (SUP i. integral\<^sup>N lborel (\<lambda>x. ?F i x))"
  proof (subst nn_integral_monotone_convergence_SUP[symmetric])
    { fix x
      obtain j where j: "x \<in> ?B j"
        using UN_box_eq_UNIV by auto

      have "ennreal (f x) = (SUP i. F i x)"
        using F(4)[of x] nonneg[of x] by (simp add: max_def)
      also have "\<dots> = (SUP i. ?F i x)"
      proof (rule SUP_eq)
        fix i show "\<exists>j\<in>UNIV. F i x \<le> ?F j x"
          using j F(2)
          by (intro bexI[of _ "max i j"])
             (auto split: split_max split_indicator simp: incseq_def le_fun_def box_def)
      qed (auto intro!: F split: split_indicator)
      finally have "ennreal (f x) =  (SUP i. ?F i x)" . }
    then show "(\<integral>\<^sup>+ x. ennreal (f x) \<partial>lborel) = (\<integral>\<^sup>+ x. (SUP i. ?F i x) \<partial>lborel)"
      by simp
  qed (insert F, auto simp: incseq_def le_fun_def box_def split: split_indicator)
  also have "\<dots> \<le> ennreal I"
  proof (rule SUP_least)
    fix i :: nat
    have finite_F: "(\<integral>\<^sup>+ x. ennreal (enn2real (F i x) * indicator (?B i) x) \<partial>lborel) < \<infinity>"
    proof (rule nn_integral_bound_simple_function)
      have "emeasure lborel {x \<in> space lborel. ennreal (enn2real (F i x) * indicator (?B i) x) \<noteq> 0} \<le>
        emeasure lborel (?B i)"
        by (intro emeasure_mono)  (auto split: split_indicator)
      then show "emeasure lborel {x \<in> space lborel. ennreal (enn2real (F i x) * indicator (?B i) x) \<noteq> 0} < \<infinity>"
        by (auto simp: less_top[symmetric] top_unique)
    qed (auto split: split_indicator
              intro!: F simple_function_compose1[where g="enn2real"] simple_function_ennreal)

    have int_F: "(\<lambda>x. enn2real (F i x) * indicator (?B i) x) integrable_on UNIV"
      using F(4) finite_F
      by (intro nn_integral_integrable_on) (auto split: split_indicator simp: enn2real_nonneg)

    have "(\<integral>\<^sup>+ x. F i x * indicator (?B i) x \<partial>lborel) =
      (\<integral>\<^sup>+ x. ennreal (enn2real (F i x) * indicator (?B i) x) \<partial>lborel)"
      using F(3,4)
      by (intro nn_integral_cong) (auto simp: image_iff eq_commute split: split_indicator)
    also have "\<dots> = ennreal (integral UNIV (\<lambda>x. enn2real (F i x) * indicator (?B i) x))"
      using F
      by (intro nn_integral_lborel_eq_integral[OF _ _ finite_F])
         (auto split: split_indicator intro: enn2real_nonneg)
    also have "\<dots> \<le> ennreal I"
      by (auto intro!: has_integral_le[OF integrable_integral[OF int_F] I] nonneg F_le_f
               simp: \<open>0 \<le> I\<close> split: split_indicator )
    finally show "(\<integral>\<^sup>+ x. F i x * indicator (?B i) x \<partial>lborel) \<le> ennreal I" .
  qed
  finally have "(\<integral>\<^sup>+ x. ennreal (f x) \<partial>lborel) < \<infinity>"
    by (auto simp: less_top[symmetric] top_unique)
  from nn_integral_lborel_eq_integral[OF assms(1,2) this] I show ?thesis
    by (simp add: integral_unique)
qed

lemma has_integral_iff_emeasure_lborel:
  fixes A :: "'a::euclidean_space set"
  assumes A[measurable]: "A \<in> sets borel" and [simp]: "0 \<le> r"
  shows "((\<lambda>x. 1) has_integral r) A \<longleftrightarrow> emeasure lborel A = ennreal r"
proof (cases "emeasure lborel A = \<infinity>")
  case emeasure_A: True
  have "\<not> (\<lambda>x. 1::real) integrable_on A"
  proof
    assume int: "(\<lambda>x. 1::real) integrable_on A"
    then have "(indicator A::'a \<Rightarrow> real) integrable_on UNIV"
      unfolding indicator_def[abs_def] integrable_restrict_UNIV .
    then obtain r where "((indicator A::'a\<Rightarrow>real) has_integral r) UNIV"
      by auto
    from nn_integral_has_integral_lborel[OF _ _ this] emeasure_A show False
      by (simp add: ennreal_indicator)
  qed
  with emeasure_A show ?thesis
    by auto
next
  case False
  then have "((\<lambda>x. 1) has_integral measure lborel A) A"
    by (simp add: has_integral_measure_lborel less_top)
  with False show ?thesis
    by (auto simp: emeasure_eq_ennreal_measure has_integral_unique)
qed

lemma ennreal_max_0: "ennreal (max 0 x) = ennreal x"
  by (auto simp: max_def ennreal_neg)

lemma has_integral_integral_real:
  fixes f::"'a::euclidean_space \<Rightarrow> real"
  assumes f: "integrable lborel f"
  shows "(f has_integral (integral\<^sup>L lborel f)) UNIV"
proof -
  from integrableE[OF f] obtain r q
    where "0 \<le> r" "0 \<le> q"
      and r: "(\<integral>\<^sup>+ x. ennreal (max 0 (f x)) \<partial>lborel) = ennreal r"
      and q: "(\<integral>\<^sup>+ x. ennreal (max 0 (- f x)) \<partial>lborel) = ennreal q"
      and f: "f \<in> borel_measurable lborel" and eq: "integral\<^sup>L lborel f = r - q"
    unfolding ennreal_max_0 by auto
  then have "((\<lambda>x. max 0 (f x)) has_integral r) UNIV" "((\<lambda>x. max 0 (- f x)) has_integral q) UNIV"
    using nn_integral_has_integral[OF _ _ r] nn_integral_has_integral[OF _ _ q] by auto
  note has_integral_diff[OF this]
  moreover have "(\<lambda>x. max 0 (f x) - max 0 (- f x)) = f"
    by auto
  ultimately show ?thesis
    by (simp add: eq)
qed

lemma has_integral_AE:
  assumes ae: "AE x in lborel. x \<in> \<Omega> \<longrightarrow> f x = g x"
  shows "(f has_integral x) \<Omega> = (g has_integral x) \<Omega>"
proof -
  from ae obtain N
    where N: "N \<in> sets borel" "emeasure lborel N = 0" "{x. \<not> (x \<in> \<Omega> \<longrightarrow> f x = g x)} \<subseteq> N"
    by (auto elim!: AE_E)
  then have not_N: "AE x in lborel. x \<notin> N"
    by (simp add: AE_iff_measurable)
  show ?thesis
  proof (rule has_integral_spike_eq[symmetric])
    show "\<And>x. x\<in>\<Omega> - N \<Longrightarrow> f x = g x" using N(3) by auto
    show "negligible N"
      unfolding negligible_def
    proof (intro allI)
      fix a b :: "'a"
      let ?F = "\<lambda>x::'a. if x \<in> cbox a b then indicator N x else 0 :: real"
      have "integrable lborel ?F = integrable lborel (\<lambda>x::'a. 0::real)"
        using not_N N(1) by (intro integrable_cong_AE) auto
      moreover have "(LINT x|lborel. ?F x) = (LINT x::'a|lborel. 0::real)"
        using not_N N(1) by (intro integral_cong_AE) auto
      ultimately have "(?F has_integral 0) UNIV"
        using has_integral_integral_real[of ?F] by simp
      then show "(indicator N has_integral (0::real)) (cbox a b)"
        unfolding has_integral_restrict_UNIV .
    qed
  qed
qed

lemma nn_integral_has_integral_lebesgue:
  fixes f :: "'a::euclidean_space \<Rightarrow> real"
  assumes nonneg: "\<And>x. 0 \<le> f x" and I: "(f has_integral I) \<Omega>"
  shows "integral\<^sup>N lborel (\<lambda>x. indicator \<Omega> x * f x) = I"
proof -
  from I have "(\<lambda>x. indicator \<Omega> x *\<^sub>R f x) \<in> lebesgue \<rightarrow>\<^sub>M borel"
    by (rule has_integral_implies_lebesgue_measurable)
  then obtain f' :: "'a \<Rightarrow> real"
    where [measurable]: "f' \<in> borel \<rightarrow>\<^sub>M borel" and eq: "AE x in lborel. indicator \<Omega> x * f x = f' x"
    by (auto dest: completion_ex_borel_measurable_real)

  from I have "((\<lambda>x. abs (indicator \<Omega> x * f x)) has_integral I) UNIV"
    using nonneg by (simp add: indicator_def if_distrib[of "\<lambda>x. x * f y" for y] cong: if_cong)
  also have "((\<lambda>x. abs (indicator \<Omega> x * f x)) has_integral I) UNIV \<longleftrightarrow> ((\<lambda>x. abs (f' x)) has_integral I) UNIV"
    using eq by (intro has_integral_AE) auto
  finally have "integral\<^sup>N lborel (\<lambda>x. abs (f' x)) = I"
    by (rule nn_integral_has_integral_lborel[rotated 2]) auto
  also have "integral\<^sup>N lborel (\<lambda>x. abs (f' x)) = integral\<^sup>N lborel (\<lambda>x. abs (indicator \<Omega> x * f x))"
    using eq by (intro nn_integral_cong_AE) auto
  finally show ?thesis
    using nonneg by auto
qed

lemma has_integral_iff_nn_integral_lebesgue:
  assumes f: "\<And>x. 0 \<le> f x"
  shows "(f has_integral r) UNIV \<longleftrightarrow> (f \<in> lebesgue \<rightarrow>\<^sub>M borel \<and> integral\<^sup>N lebesgue f = r \<and> 0 \<le> r)" (is "?I = ?N")
proof
  assume ?I
  have "0 \<le> r"
    using has_integral_nonneg[OF \<open>?I\<close>] f by auto
  then show ?N
    using nn_integral_has_integral_lebesgue[OF f \<open>?I\<close>]
      has_integral_implies_lebesgue_measurable[OF \<open>?I\<close>]
    by (auto simp: nn_integral_completion)
next
  assume ?N
  then obtain f' where f': "f' \<in> borel \<rightarrow>\<^sub>M borel" "AE x in lborel. f x = f' x"
    by (auto dest: completion_ex_borel_measurable_real)
  moreover have "(\<integral>\<^sup>+ x. ennreal \<bar>f' x\<bar> \<partial>lborel) = (\<integral>\<^sup>+ x. ennreal \<bar>f x\<bar> \<partial>lborel)"
    using f' by (intro nn_integral_cong_AE) auto
  moreover have "((\<lambda>x. \<bar>f' x\<bar>) has_integral r) UNIV \<longleftrightarrow> ((\<lambda>x. \<bar>f x\<bar>) has_integral r) UNIV"
    using f' by (intro has_integral_AE) auto
  moreover note nn_integral_has_integral[of "\<lambda>x. \<bar>f' x\<bar>" r] \<open>?N\<close>
  ultimately show ?I
    using f by (auto simp: nn_integral_completion)
qed

context
  fixes f::"'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
begin

lemma has_integral_integral_lborel:
  assumes f: "integrable lborel f"
  shows "(f has_integral (integral\<^sup>L lborel f)) UNIV"
proof -
  have "((\<lambda>x. \<Sum>b\<in>Basis. (f x \<bullet> b) *\<^sub>R b) has_integral (\<Sum>b\<in>Basis. integral\<^sup>L lborel (\<lambda>x. f x \<bullet> b) *\<^sub>R b)) UNIV"
    using f by (intro has_integral_sum finite_Basis ballI has_integral_scaleR_left has_integral_integral_real) auto
  also have eq_f: "(\<lambda>x. \<Sum>b\<in>Basis. (f x \<bullet> b) *\<^sub>R b) = f"
    by (simp add: fun_eq_iff euclidean_representation)
  also have "(\<Sum>b\<in>Basis. integral\<^sup>L lborel (\<lambda>x. f x \<bullet> b) *\<^sub>R b) = integral\<^sup>L lborel f"
    using f by (subst (2) eq_f[symmetric]) simp
  finally show ?thesis .
qed

lemma integrable_on_lborel: "integrable lborel f \<Longrightarrow> f integrable_on UNIV"
  using has_integral_integral_lborel by auto

lemma integral_lborel: "integrable lborel f \<Longrightarrow> integral UNIV f = (\<integral>x. f x \<partial>lborel)"
  using has_integral_integral_lborel by auto

end

context
begin

private lemma has_integral_integral_lebesgue_real:
  fixes f :: "'a::euclidean_space \<Rightarrow> real"
  assumes f: "integrable lebesgue f"
  shows "(f has_integral (integral\<^sup>L lebesgue f)) UNIV"
proof -
  obtain f' where f': "f' \<in> borel \<rightarrow>\<^sub>M borel" "AE x in lborel. f x = f' x"
    using completion_ex_borel_measurable_real[OF borel_measurable_integrable[OF f]] by auto
  moreover have "(\<integral>\<^sup>+ x. ennreal (norm (f x)) \<partial>lborel) = (\<integral>\<^sup>+ x. ennreal (norm (f' x)) \<partial>lborel)"
    using f' by (intro nn_integral_cong_AE) auto
  ultimately have "integrable lborel f'"
    using f by (auto simp: integrable_iff_bounded nn_integral_completion cong: nn_integral_cong_AE)
  note has_integral_integral_real[OF this]
  moreover have "integral\<^sup>L lebesgue f = integral\<^sup>L lebesgue f'"
    using f' f by (intro integral_cong_AE) (auto intro: AE_completion measurable_completion)
  moreover have "integral\<^sup>L lebesgue f' = integral\<^sup>L lborel f'"
    using f' by (simp add: integral_completion)
  moreover have "(f' has_integral integral\<^sup>L lborel f') UNIV \<longleftrightarrow> (f has_integral integral\<^sup>L lborel f') UNIV"
    using f' by (intro has_integral_AE) auto
  ultimately show ?thesis
    by auto
qed

lemma has_integral_integral_lebesgue:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  assumes f: "integrable lebesgue f"
  shows "(f has_integral (integral\<^sup>L lebesgue f)) UNIV"
proof -
  have "((\<lambda>x. \<Sum>b\<in>Basis. (f x \<bullet> b) *\<^sub>R b) has_integral (\<Sum>b\<in>Basis. integral\<^sup>L lebesgue (\<lambda>x. f x \<bullet> b) *\<^sub>R b)) UNIV"
    using f by (intro has_integral_sum finite_Basis ballI has_integral_scaleR_left has_integral_integral_lebesgue_real) auto
  also have eq_f: "(\<lambda>x. \<Sum>b\<in>Basis. (f x \<bullet> b) *\<^sub>R b) = f"
    by (simp add: fun_eq_iff euclidean_representation)
  also have "(\<Sum>b\<in>Basis. integral\<^sup>L lebesgue (\<lambda>x. f x \<bullet> b) *\<^sub>R b) = integral\<^sup>L lebesgue f"
    using f by (subst (2) eq_f[symmetric]) simp
  finally show ?thesis .
qed

lemma integrable_on_lebesgue:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  shows "integrable lebesgue f \<Longrightarrow> f integrable_on UNIV"
  using has_integral_integral_lebesgue by auto

lemma integral_lebesgue:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  shows "integrable lebesgue f \<Longrightarrow> integral UNIV f = (\<integral>x. f x \<partial>lebesgue)"
  using has_integral_integral_lebesgue by auto

end

subsection \<open>Absolute integrability (this is the same as Lebesgue integrability)\<close>

translations
"LBINT x. f" == "CONST lebesgue_integral CONST lborel (\<lambda>x. f)"

translations
"LBINT x:A. f" == "CONST set_lebesgue_integral CONST lborel A (\<lambda>x. f)"

lemma set_integral_reflect:
  fixes S and f :: "real \<Rightarrow> 'a :: {banach, second_countable_topology}"
  shows "(LBINT x : S. f x) = (LBINT x : {x. - x \<in> S}. f (- x))"
  unfolding set_lebesgue_integral_def
  by (subst lborel_integral_real_affine[where c="-1" and t=0])
     (auto intro!: Bochner_Integration.integral_cong split: split_indicator)

lemma borel_integrable_atLeastAtMost':
  fixes f :: "real \<Rightarrow> 'a::{banach, second_countable_topology}"
  assumes f: "continuous_on {a..b} f"
  shows "set_integrable lborel {a..b} f" 
  unfolding set_integrable_def
  by (intro borel_integrable_compact compact_Icc f)

lemma integral_FTC_atLeastAtMost:
  fixes f :: "real \<Rightarrow> 'a :: euclidean_space"
  assumes "a \<le> b"
    and F: "\<And>x. a \<le> x \<Longrightarrow> x \<le> b \<Longrightarrow> (F has_vector_derivative f x) (at x within {a .. b})"
    and f: "continuous_on {a .. b} f"
  shows "integral\<^sup>L lborel (\<lambda>x. indicator {a .. b} x *\<^sub>R f x) = F b - F a"
proof -
  let ?f = "\<lambda>x. indicator {a .. b} x *\<^sub>R f x"
  have "(?f has_integral (\<integral>x. ?f x \<partial>lborel)) UNIV"
    using borel_integrable_atLeastAtMost'[OF f]
    unfolding set_integrable_def by (rule has_integral_integral_lborel)
  moreover
  have "(f has_integral F b - F a) {a .. b}"
    by (intro fundamental_theorem_of_calculus ballI assms) auto
  then have "(?f has_integral F b - F a) {a .. b}"
    by (subst has_integral_cong[where g=f]) auto
  then have "(?f has_integral F b - F a) UNIV"
    by (intro has_integral_on_superset[where T=UNIV and S="{a..b}"]) auto
  ultimately show "integral\<^sup>L lborel ?f = F b - F a"
    by (rule has_integral_unique)
qed

lemma set_borel_integral_eq_integral:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  assumes "set_integrable lborel S f"
  shows "f integrable_on S" "LINT x : S | lborel. f x = integral S f"
proof -
  let ?f = "\<lambda>x. indicator S x *\<^sub>R f x"
  have "(?f has_integral LINT x : S | lborel. f x) UNIV"
    using assms has_integral_integral_lborel 
    unfolding set_integrable_def set_lebesgue_integral_def by blast
  hence 1: "(f has_integral (set_lebesgue_integral lborel S f)) S"
    apply (subst has_integral_restrict_UNIV [symmetric])
    apply (rule has_integral_eq)
    by auto
  thus "f integrable_on S"
    by (auto simp add: integrable_on_def)
  with 1 have "(f has_integral (integral S f)) S"
    by (intro integrable_integral, auto simp add: integrable_on_def)
  thus "LINT x : S | lborel. f x = integral S f"
    by (intro has_integral_unique [OF 1])
qed

lemma has_integral_set_lebesgue:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  assumes f: "set_integrable lebesgue S f"
  shows "(f has_integral (LINT x:S|lebesgue. f x)) S"
  using has_integral_integral_lebesgue f 
  by (fastforce simp add: set_integrable_def set_lebesgue_integral_def indicator_def if_distrib[of "\<lambda>x. x *\<^sub>R f _"] cong: if_cong)

lemma set_lebesgue_integral_eq_integral:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  assumes f: "set_integrable lebesgue S f"
  shows "f integrable_on S" "LINT x:S | lebesgue. f x = integral S f"
  using has_integral_set_lebesgue[OF f] by (auto simp: integral_unique integrable_on_def)

lemma lmeasurable_iff_has_integral:
  "S \<in> lmeasurable \<longleftrightarrow> ((indicator S) has_integral measure lebesgue S) UNIV"
  by (subst has_integral_iff_nn_integral_lebesgue)
     (auto simp: ennreal_indicator emeasure_eq_measure2 borel_measurable_indicator_iff intro!: fmeasurableI)

abbreviation
  absolutely_integrable_on :: "('a::euclidean_space \<Rightarrow> 'b::{banach, second_countable_topology}) \<Rightarrow> 'a set \<Rightarrow> bool"
  (infixr "absolutely'_integrable'_on" 46)
  where "f absolutely_integrable_on s \<equiv> set_integrable lebesgue s f"


lemma absolutely_integrable_zero [simp]: "(\<lambda>x. 0) absolutely_integrable_on S"
    by (simp add: set_integrable_def)

lemma absolutely_integrable_on_def:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  shows "f absolutely_integrable_on S \<longleftrightarrow> f integrable_on S \<and> (\<lambda>x. norm (f x)) integrable_on S"
proof safe
  assume f: "f absolutely_integrable_on S"
  then have nf: "integrable lebesgue (\<lambda>x. norm (indicator S x *\<^sub>R f x))"
    using integrable_norm set_integrable_def by blast
  show "f integrable_on S"
    by (rule set_lebesgue_integral_eq_integral[OF f])
  have "(\<lambda>x. norm (indicator S x *\<^sub>R f x)) = (\<lambda>x. if x \<in> S then norm (f x) else 0)"
    by auto
  with integrable_on_lebesgue[OF nf] show "(\<lambda>x. norm (f x)) integrable_on S"
    by (simp add: integrable_restrict_UNIV)
next
  assume f: "f integrable_on S" and nf: "(\<lambda>x. norm (f x)) integrable_on S"
  show "f absolutely_integrable_on S"
    unfolding set_integrable_def
  proof (rule integrableI_bounded)
    show "(\<lambda>x. indicator S x *\<^sub>R f x) \<in> borel_measurable lebesgue"
      using f has_integral_implies_lebesgue_measurable[of f _ S] by (auto simp: integrable_on_def)
    show "(\<integral>\<^sup>+ x. ennreal (norm (indicator S x *\<^sub>R f x)) \<partial>lebesgue) < \<infinity>"
      using nf nn_integral_has_integral_lebesgue[of "\<lambda>x. norm (f x)" _ S]
      by (auto simp: integrable_on_def nn_integral_completion)
  qed
qed

lemma integrable_on_lebesgue_on:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  assumes f: "integrable (lebesgue_on S) f" and S: "S \<in> sets lebesgue"
  shows "f integrable_on S"
proof -
  have "integrable lebesgue (\<lambda>x. indicator S x *\<^sub>R f x)"
    using S f inf_top.comm_neutral integrable_restrict_space by blast
  then show ?thesis
    using absolutely_integrable_on_def set_integrable_def by blast
qed

lemma absolutely_integrable_on_null [intro]:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  shows "content (cbox a b) = 0 \<Longrightarrow> f absolutely_integrable_on (cbox a b)"
  by (auto simp: absolutely_integrable_on_def)

lemma absolutely_integrable_on_open_interval:
  fixes f :: "'a :: euclidean_space \<Rightarrow> 'b :: euclidean_space"
  shows "f absolutely_integrable_on box a b \<longleftrightarrow>
         f absolutely_integrable_on cbox a b"
  by (auto simp: integrable_on_open_interval absolutely_integrable_on_def)

lemma absolutely_integrable_restrict_UNIV:
  "(\<lambda>x. if x \<in> S then f x else 0) absolutely_integrable_on UNIV \<longleftrightarrow> f absolutely_integrable_on S"
    unfolding set_integrable_def
  by (intro arg_cong2[where f=integrable]) auto

lemma absolutely_integrable_onI:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  shows "f integrable_on S \<Longrightarrow> (\<lambda>x. norm (f x)) integrable_on S \<Longrightarrow> f absolutely_integrable_on S"
  unfolding absolutely_integrable_on_def by auto

lemma nonnegative_absolutely_integrable_1:
  fixes f :: "'a :: euclidean_space \<Rightarrow> real"
  assumes f: "f integrable_on A" and "\<And>x. x \<in> A \<Longrightarrow> 0 \<le> f x"
  shows "f absolutely_integrable_on A"
  by (rule absolutely_integrable_onI [OF f]) (use assms in \<open>simp add: integrable_eq\<close>)

lemma absolutely_integrable_on_iff_nonneg:
  fixes f :: "'a :: euclidean_space \<Rightarrow> real"
  assumes "\<And>x. x \<in> S \<Longrightarrow> 0 \<le> f x" shows "f absolutely_integrable_on S \<longleftrightarrow> f integrable_on S"
proof -
  { assume "f integrable_on S"
    then have "(\<lambda>x. if x \<in> S then f x else 0) integrable_on UNIV"
      by (simp add: integrable_restrict_UNIV)
    then have "(\<lambda>x. if x \<in> S then f x else 0) absolutely_integrable_on UNIV"
      using \<open>f integrable_on S\<close> absolutely_integrable_restrict_UNIV assms nonnegative_absolutely_integrable_1 by blast
    then have "f absolutely_integrable_on S"
      using absolutely_integrable_restrict_UNIV by blast
  }
  then show ?thesis        
    unfolding absolutely_integrable_on_def by auto
qed

lemma absolutely_integrable_on_scaleR_iff:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  shows
   "(\<lambda>x. c *\<^sub>R f x) absolutely_integrable_on S \<longleftrightarrow>
      c = 0 \<or> f absolutely_integrable_on S"
proof (cases "c=0")
  case False
  then show ?thesis
  unfolding absolutely_integrable_on_def 
  by (simp add: norm_mult)
qed auto

lemma absolutely_integrable_spike:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  assumes "f absolutely_integrable_on T" and S: "negligible S" "\<And>x. x \<in> T - S \<Longrightarrow> g x = f x"
  shows "g absolutely_integrable_on T"
  using assms integrable_spike
  unfolding absolutely_integrable_on_def by metis

lemma absolutely_integrable_negligible:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  assumes "negligible S"
  shows "f absolutely_integrable_on S"
  using assms by (simp add: absolutely_integrable_on_def integrable_negligible)

lemma absolutely_integrable_spike_eq:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  assumes "negligible S" "\<And>x. x \<in> T - S \<Longrightarrow> g x = f x"
  shows "(f absolutely_integrable_on T \<longleftrightarrow> g absolutely_integrable_on T)"
  using assms by (blast intro: absolutely_integrable_spike sym)

lemma absolutely_integrable_spike_set_eq:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  assumes "negligible {x \<in> S - T. f x \<noteq> 0}" "negligible {x \<in> T - S. f x \<noteq> 0}"
  shows "(f absolutely_integrable_on S \<longleftrightarrow> f absolutely_integrable_on T)"
proof -
  have "(\<lambda>x. if x \<in> S then f x else 0) absolutely_integrable_on UNIV \<longleftrightarrow>
        (\<lambda>x. if x \<in> T then f x else 0) absolutely_integrable_on UNIV"
  proof (rule absolutely_integrable_spike_eq)
    show "negligible ({x \<in> S - T. f x \<noteq> 0} \<union> {x \<in> T - S. f x \<noteq> 0})"
      by (rule negligible_Un [OF assms])
  qed auto
  with absolutely_integrable_restrict_UNIV show ?thesis
    by blast
qed

lemma absolutely_integrable_spike_set:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  assumes f: "f absolutely_integrable_on S" and neg: "negligible {x \<in> S - T. f x \<noteq> 0}" "negligible {x \<in> T - S. f x \<noteq> 0}"
  shows "f absolutely_integrable_on T"
  using absolutely_integrable_spike_set_eq f neg by blast

lemma lmeasurable_iff_integrable_on: "S \<in> lmeasurable \<longleftrightarrow> (\<lambda>x. 1::real) integrable_on S"
  by (subst absolutely_integrable_on_iff_nonneg[symmetric])
     (simp_all add: lmeasurable_iff_integrable set_integrable_def)

lemma lmeasure_integral_UNIV: "S \<in> lmeasurable \<Longrightarrow> measure lebesgue S = integral UNIV (indicator S)"
  by (simp add: lmeasurable_iff_has_integral integral_unique)

lemma lmeasure_integral: "S \<in> lmeasurable \<Longrightarrow> measure lebesgue S = integral S (\<lambda>x. 1::real)"
  by (fastforce simp add: lmeasure_integral_UNIV indicator_def[abs_def] lmeasurable_iff_integrable_on)

lemma integrable_on_const: "S \<in> lmeasurable \<Longrightarrow> (\<lambda>x. c) integrable_on S"
  unfolding lmeasurable_iff_integrable
  by (metis (mono_tags, lifting) integrable_eq integrable_on_scaleR_left lmeasurable_iff_integrable lmeasurable_iff_integrable_on scaleR_one)

lemma integral_indicator:
  assumes "(S \<inter> T) \<in> lmeasurable"
  shows "integral T (indicator S) = measure lebesgue (S \<inter> T)"
proof -
  have "integral UNIV (indicator (S \<inter> T)) = integral UNIV (\<lambda>a. if a \<in> S \<inter> T then 1::real else 0)"
    by (meson indicator_def)
  moreover
  have "(indicator (S \<inter> T) has_integral measure lebesgue (S \<inter> T)) UNIV"
    using assms by (simp add: lmeasurable_iff_has_integral)
  ultimately have "integral UNIV (\<lambda>x. if x \<in> S \<inter> T then 1 else 0) = measure lebesgue (S \<inter> T)"
    by (metis (no_types) integral_unique)
  then show ?thesis
    using integral_restrict_Int [of UNIV "S \<inter> T" "\<lambda>x. 1::real"]
    apply (simp add: integral_restrict_Int [symmetric])
    by (meson indicator_def)
qed

lemma measurable_integrable:
  fixes S :: "'a::euclidean_space set"
  shows "S \<in> lmeasurable \<longleftrightarrow> (indicat_real S) integrable_on UNIV"
  by (auto simp: lmeasurable_iff_integrable absolutely_integrable_on_iff_nonneg [symmetric] set_integrable_def)

lemma integrable_on_indicator:
  fixes S :: "'a::euclidean_space set"
  shows "indicat_real S integrable_on T \<longleftrightarrow> (S \<inter> T) \<in> lmeasurable"
  unfolding measurable_integrable
  unfolding integrable_restrict_UNIV [of T, symmetric]
  by (fastforce simp add: indicator_def elim: integrable_eq)

lemma
  assumes \<D>: "\<D> division_of S"
  shows lmeasurable_division: "S \<in> lmeasurable" (is ?l)
    and content_division: "(\<Sum>k\<in>\<D>. measure lebesgue k) = measure lebesgue S" (is ?m)
proof -
  { fix d1 d2 assume *: "d1 \<in> \<D>" "d2 \<in> \<D>" "d1 \<noteq> d2"
    then obtain a b c d where "d1 = cbox a b" "d2 = cbox c d"
      using division_ofD(4)[OF \<D>] by blast
    with division_ofD(5)[OF \<D> *]
    have "d1 \<in> sets lborel" "d2 \<in> sets lborel" "d1 \<inter> d2 \<subseteq> (cbox a b - box a b) \<union> (cbox c d - box c d)"
      by auto
    moreover have "(cbox a b - box a b) \<union> (cbox c d - box c d) \<in> null_sets lborel"
      by (intro null_sets.Un null_sets_cbox_Diff_box)
    ultimately have "d1 \<inter> d2 \<in> null_sets lborel"
      by (blast intro: null_sets_subset) }
  then show ?l ?m
    unfolding division_ofD(6)[OF \<D>, symmetric]
    using division_ofD(1,4)[OF \<D>]
    by (auto intro!: measure_Union_AE[symmetric] simp: completion.AE_iff_null_sets Int_def[symmetric] pairwise_def null_sets_def)
qed

lemma has_measure_limit:
  assumes "S \<in> lmeasurable" "e > 0"
  obtains B where "B > 0"
    "\<And>a b. ball 0 B \<subseteq> cbox a b \<Longrightarrow> \<bar>measure lebesgue (S \<inter> cbox a b) - measure lebesgue S\<bar> < e"
  using assms unfolding lmeasurable_iff_has_integral has_integral_alt'
  by (force simp: integral_indicator integrable_on_indicator)

lemma lmeasurable_iff_indicator_has_integral:
  fixes S :: "'a::euclidean_space set"
  shows "S \<in> lmeasurable \<and> m = measure lebesgue S \<longleftrightarrow> (indicat_real S has_integral m) UNIV"
  by (metis has_integral_iff lmeasurable_iff_has_integral measurable_integrable)

lemma has_measure_limit_iff:
  fixes f :: "'n::euclidean_space \<Rightarrow> 'a::banach"
  shows "S \<in> lmeasurable \<and> m = measure lebesgue S \<longleftrightarrow>
          (\<forall>e>0. \<exists>B>0. \<forall>a b. ball 0 B \<subseteq> cbox a b \<longrightarrow>
            (S \<inter> cbox a b) \<in> lmeasurable \<and> \<bar>measure lebesgue (S \<inter> cbox a b) - m\<bar> < e)" (is "?lhs = ?rhs")
proof
  assume ?lhs then show ?rhs
    by (meson has_measure_limit fmeasurable.Int lmeasurable_cbox)
next
  assume RHS [rule_format]: ?rhs
  show ?lhs
    apply (simp add: lmeasurable_iff_indicator_has_integral has_integral' [where i=m])
    using RHS
    by (metis (full_types) integral_indicator integrable_integral integrable_on_indicator)
qed

subsection\<open>Applications to Negligibility\<close>

lemma negligible_iff_null_sets: "negligible S \<longleftrightarrow> S \<in> null_sets lebesgue"
proof
  assume "negligible S"
  then have "(indicator S has_integral (0::real)) UNIV"
    by (auto simp: negligible)
  then show "S \<in> null_sets lebesgue"
    by (subst (asm) has_integral_iff_nn_integral_lebesgue)
        (auto simp: borel_measurable_indicator_iff nn_integral_0_iff_AE AE_iff_null_sets indicator_eq_0_iff)
next
  assume S: "S \<in> null_sets lebesgue"
  show "negligible S"
    unfolding negligible_def
  proof (safe intro!: has_integral_iff_nn_integral_lebesgue[THEN iffD2]
                      has_integral_restrict_UNIV[where s="cbox _ _", THEN iffD1])
    fix a b
    show "(\<lambda>x. if x \<in> cbox a b then indicator S x else 0) \<in> lebesgue \<rightarrow>\<^sub>M borel"
      using S by (auto intro!: measurable_If)
    then show "(\<integral>\<^sup>+ x. ennreal (if x \<in> cbox a b then indicator S x else 0) \<partial>lebesgue) = ennreal 0"
      using S[THEN AE_not_in] by (auto intro!: nn_integral_0_iff_AE[THEN iffD2])
  qed auto
qed

lemma starlike_negligible:
  assumes "closed S"
      and eq1: "\<And>c x. \<lbrakk>(a + c *\<^sub>R x) \<in> S; 0 \<le> c; a + x \<in> S\<rbrakk> \<Longrightarrow> c = 1"
    shows "negligible S"
proof -
  have "negligible ((+) (-a) ` S)"
  proof (subst negligible_on_intervals, intro allI)
    fix u v
    show "negligible ((+) (- a) ` S \<inter> cbox u v)"
      unfolding negligible_iff_null_sets
      apply (rule starlike_negligible_compact)
       apply (simp add: assms closed_translation closed_Int_compact, clarify)
      by (metis eq1 minus_add_cancel)
  qed
  then show ?thesis
    by (rule negligible_translation_rev)
qed

lemma starlike_negligible_strong:
  assumes "closed S"
      and star: "\<And>c x. \<lbrakk>0 \<le> c; c < 1; a+x \<in> S\<rbrakk> \<Longrightarrow> a + c *\<^sub>R x \<notin> S"
    shows "negligible S"
proof -
  show ?thesis
  proof (rule starlike_negligible [OF \<open>closed S\<close>, of a])
    fix c x
    assume cx: "a + c *\<^sub>R x \<in> S" "0 \<le> c" "a + x \<in> S"
    with star have "~ (c < 1)" by auto
    moreover have "~ (c > 1)"
      using star [of "1/c" "c *\<^sub>R x"] cx by force
    ultimately show "c = 1" by arith
  qed
qed

lemma negligible_hyperplane:
  assumes "a \<noteq> 0 \<or> b \<noteq> 0" shows "negligible {x. a \<bullet> x = b}"
proof -
  obtain x where x: "a \<bullet> x \<noteq> b"
    using assms
    apply auto
     apply (metis inner_eq_zero_iff inner_zero_right)
    using inner_zero_right by fastforce
  show ?thesis
    apply (rule starlike_negligible [OF closed_hyperplane, of x])
    using x apply (auto simp: algebra_simps)
    done
qed

lemma negligible_lowdim:
  fixes S :: "'N :: euclidean_space set"
  assumes "dim S < DIM('N)"
    shows "negligible S"
proof -
  obtain a where "a \<noteq> 0" and a: "span S \<subseteq> {x. a \<bullet> x = 0}"
    using lowdim_subset_hyperplane [OF assms] by blast
  have "negligible (span S)"
    using \<open>a \<noteq> 0\<close> a negligible_hyperplane by (blast intro: negligible_subset)
  then show ?thesis
    using span_base by (blast intro: negligible_subset)
qed

proposition negligible_convex_frontier:
  fixes S :: "'N :: euclidean_space set"
  assumes "convex S"
    shows "negligible(frontier S)"
proof -
  have nf: "negligible(frontier S)" if "convex S" "0 \<in> S" for S :: "'N set"
  proof -
    obtain B where "B \<subseteq> S" and indB: "independent B"
               and spanB: "S \<subseteq> span B" and cardB: "card B = dim S"
      by (metis basis_exists)
    consider "dim S < DIM('N)" | "dim S = DIM('N)"
      using dim_subset_UNIV le_eq_less_or_eq by auto
    then show ?thesis
    proof cases
      case 1
      show ?thesis
        by (rule negligible_subset [of "closure S"])
           (simp_all add: Diff_subset frontier_def negligible_lowdim 1)
    next
      case 2
      obtain a where a: "a \<in> interior S"
        apply (rule interior_simplex_nonempty [OF indB])
          apply (simp add: indB independent_finite)
         apply (simp add: cardB 2)
        apply (metis \<open>B \<subseteq> S\<close> \<open>0 \<in> S\<close> \<open>convex S\<close> insert_absorb insert_subset interior_mono subset_hull)
        done
      show ?thesis
      proof (rule starlike_negligible_strong [where a=a])
        fix c::real and x
        have eq: "a + c *\<^sub>R x = (a + x) - (1 - c) *\<^sub>R ((a + x) - a)"
          by (simp add: algebra_simps)
        assume "0 \<le> c" "c < 1" "a + x \<in> frontier S"
        then show "a + c *\<^sub>R x \<notin> frontier S"
          apply (clarsimp simp: frontier_def)
          apply (subst eq)
          apply (rule mem_interior_closure_convex_shrink [OF \<open>convex S\<close> a, of _ "1-c"], auto)
          done
      qed auto
    qed
  qed
  show ?thesis
  proof (cases "S = {}")
    case True then show ?thesis by auto
  next
    case False
    then obtain a where "a \<in> S" by auto
    show ?thesis
      using nf [of "(\<lambda>x. -a + x) ` S"]
      by (metis \<open>a \<in> S\<close> add.left_inverse assms convex_translation_eq frontier_translation
                image_eqI negligible_translation_rev)
  qed
qed

corollary negligible_sphere: "negligible (sphere a e)"
  using frontier_cball negligible_convex_frontier convex_cball
  by (blast intro: negligible_subset)

lemma non_negligible_UNIV [simp]: "\<not> negligible UNIV"
  unfolding negligible_iff_null_sets by (auto simp: null_sets_def)

lemma negligible_interval:
  "negligible (cbox a b) \<longleftrightarrow> box a b = {}" "negligible (box a b) \<longleftrightarrow> box a b = {}"
   by (auto simp: negligible_iff_null_sets null_sets_def prod_nonneg inner_diff_left box_eq_empty
                  not_le emeasure_lborel_cbox_eq emeasure_lborel_box_eq
            intro: eq_refl antisym less_imp_le)

proposition open_not_negligible:
  assumes "open S" "S \<noteq> {}"
  shows "\<not> negligible S"
proof
  assume neg: "negligible S"
  obtain a where "a \<in> S"
    using \<open>S \<noteq> {}\<close> by blast
  then obtain e where "e > 0" "cball a e \<subseteq> S"
    using \<open>open S\<close> open_contains_cball_eq by blast
  let ?p = "a - (e / DIM('a)) *\<^sub>R One" let ?q = "a + (e / DIM('a)) *\<^sub>R One"
  have "cbox ?p ?q \<subseteq> cball a e"
  proof (clarsimp simp: mem_box dist_norm)
    fix x
    assume "\<forall>i\<in>Basis. ?p \<bullet> i \<le> x \<bullet> i \<and> x \<bullet> i \<le> ?q \<bullet> i"
    then have ax: "\<bar>(a - x) \<bullet> i\<bar> \<le> e / real DIM('a)" if "i \<in> Basis" for i
      using that by (auto simp: algebra_simps)
    have "norm (a - x) \<le> (\<Sum>i\<in>Basis. \<bar>(a - x) \<bullet> i\<bar>)"
      by (rule norm_le_l1)
    also have "\<dots> \<le> DIM('a) * (e / real DIM('a))"
      by (intro sum_bounded_above ax)
    also have "\<dots> = e"
      by simp
    finally show "norm (a - x) \<le> e" .
  qed
  then have "negligible (cbox ?p ?q)"
    by (meson \<open>cball a e \<subseteq> S\<close> neg negligible_subset)
  with \<open>e > 0\<close> show False
    by (simp add: negligible_interval box_eq_empty algebra_simps divide_simps mult_le_0_iff)
qed

lemma negligible_convex_interior:
   "convex S \<Longrightarrow> (negligible S \<longleftrightarrow> interior S = {})"
  apply safe
  apply (metis interior_subset negligible_subset open_interior open_not_negligible)
   apply (metis Diff_empty closure_subset frontier_def negligible_convex_frontier negligible_subset)
  done

lemma measure_eq_0_null_sets: "S \<in> null_sets M \<Longrightarrow> measure M S = 0"
  by (auto simp: measure_def null_sets_def)

lemma negligible_imp_measure0: "negligible S \<Longrightarrow> measure lebesgue S = 0"
  by (simp add: measure_eq_0_null_sets negligible_iff_null_sets)

lemma negligible_iff_emeasure0: "S \<in> sets lebesgue \<Longrightarrow> (negligible S \<longleftrightarrow> emeasure lebesgue S = 0)"
  by (auto simp: measure_eq_0_null_sets negligible_iff_null_sets)

lemma negligible_iff_measure0: "S \<in> lmeasurable \<Longrightarrow> (negligible S \<longleftrightarrow> measure lebesgue S = 0)"
  apply (auto simp: measure_eq_0_null_sets negligible_iff_null_sets)
  by (metis completion.null_sets_outer subsetI)

lemma negligible_imp_sets: "negligible S \<Longrightarrow> S \<in> sets lebesgue"
  by (simp add: negligible_iff_null_sets null_setsD2)

lemma negligible_imp_measurable: "negligible S \<Longrightarrow> S \<in> lmeasurable"
  by (simp add: fmeasurableI_null_sets negligible_iff_null_sets)

lemma negligible_iff_measure: "negligible S \<longleftrightarrow> S \<in> lmeasurable \<and> measure lebesgue S = 0"
  by (fastforce simp: negligible_iff_measure0 negligible_imp_measurable dest: negligible_imp_measure0)

lemma negligible_outer:
  "negligible S \<longleftrightarrow> (\<forall>e>0. \<exists>T. S \<subseteq> T \<and> T \<in> lmeasurable \<and> measure lebesgue T < e)" (is "_ = ?rhs")
proof
  assume "negligible S" then show ?rhs
    by (metis negligible_iff_measure order_refl)
next
  assume ?rhs then show "negligible S"
  by (meson completion.null_sets_outer negligible_iff_null_sets)
qed

lemma negligible_outer_le:
     "negligible S \<longleftrightarrow> (\<forall>e>0. \<exists>T. S \<subseteq> T \<and> T \<in> lmeasurable \<and> measure lebesgue T \<le> e)" (is "_ = ?rhs")
proof
  assume "negligible S" then show ?rhs
    by (metis dual_order.strict_implies_order negligible_imp_measurable negligible_imp_measure0 order_refl)
next
  assume ?rhs then show "negligible S"
    by (metis le_less_trans negligible_outer field_lbound_gt_zero)
qed

lemma negligible_UNIV: "negligible S \<longleftrightarrow> (indicat_real S has_integral 0) UNIV" (is "_=?rhs")
proof
  assume ?rhs
  then show "negligible S"
    apply (auto simp: negligible_def has_integral_iff integrable_on_indicator)
    by (metis negligible integral_unique lmeasure_integral_UNIV negligible_iff_measure0)
qed (simp add: negligible)

lemma sets_negligible_symdiff:
   "\<lbrakk>S \<in> sets lebesgue; negligible((S - T) \<union> (T - S))\<rbrakk> \<Longrightarrow> T \<in> sets lebesgue"
  by (metis Diff_Diff_Int Int_Diff_Un inf_commute negligible_Un_eq negligible_imp_sets sets.Diff sets.Un)

lemma lmeasurable_negligible_symdiff:
   "\<lbrakk>S \<in> lmeasurable; negligible((S - T) \<union> (T - S))\<rbrakk> \<Longrightarrow> T \<in> lmeasurable"
  using integrable_spike_set_eq lmeasurable_iff_integrable_on by blast


lemma measure_Un3_negligible:
  assumes meas: "S \<in> lmeasurable" "T \<in> lmeasurable" "U \<in> lmeasurable"
  and neg: "negligible(S \<inter> T)" "negligible(S \<inter> U)" "negligible(T \<inter> U)" and V: "S \<union> T \<union> U = V"
shows "measure lebesgue V = measure lebesgue S + measure lebesgue T + measure lebesgue U"
proof -
  have [simp]: "measure lebesgue (S \<inter> T) = 0"
    using neg(1) negligible_imp_measure0 by blast
  have [simp]: "measure lebesgue (S \<inter> U \<union> T \<inter> U) = 0"
    using neg(2) neg(3) negligible_Un negligible_imp_measure0 by blast
  have "measure lebesgue V = measure lebesgue (S \<union> T \<union> U)"
    using V by simp
  also have "\<dots> = measure lebesgue S + measure lebesgue T + measure lebesgue U"
    by (simp add: measure_Un3 meas fmeasurable.Un Int_Un_distrib2)
  finally show ?thesis .
qed

lemma measure_translate_add:
  assumes meas: "S \<in> lmeasurable" "T \<in> lmeasurable"
    and U: "S \<union> ((+)a ` T) = U" and neg: "negligible(S \<inter> ((+)a ` T))"
  shows "measure lebesgue S + measure lebesgue T = measure lebesgue U"
proof -
  have [simp]: "measure lebesgue (S \<inter> (+) a ` T) = 0"
    using neg negligible_imp_measure0 by blast
  have "measure lebesgue (S \<union> ((+)a ` T)) = measure lebesgue S + measure lebesgue T"
    by (simp add: measure_Un3 meas measurable_translation measure_translation fmeasurable.Un)
  then show ?thesis
    using U by auto
qed

lemma measure_negligible_symdiff:
  assumes S: "S \<in> lmeasurable"
    and neg: "negligible (S - T \<union> (T - S))"
  shows "measure lebesgue T = measure lebesgue S"
proof -
  have "measure lebesgue (S - T) = 0"
    using neg negligible_Un_eq negligible_imp_measure0 by blast
  then show ?thesis
    by (metis S Un_commute add.right_neutral lmeasurable_negligible_symdiff measure_Un2 neg negligible_Un_eq negligible_imp_measure0)
qed

lemma measure_closure:
  assumes "bounded S" and neg: "negligible (frontier S)"
  shows "measure lebesgue (closure S) = measure lebesgue S"
proof -
  have "measure lebesgue (frontier S) = 0"
    by (metis neg negligible_imp_measure0)
  then show ?thesis
    by (metis assms lmeasurable_iff_integrable_on eq_iff_diff_eq_0 has_integral_interior integrable_on_def integral_unique lmeasurable_interior lmeasure_integral measure_frontier)
qed

lemma measure_interior:
   "\<lbrakk>bounded S; negligible(frontier S)\<rbrakk> \<Longrightarrow> measure lebesgue (interior S) = measure lebesgue S"
  using measure_closure measure_frontier negligible_imp_measure0 by fastforce

lemma measurable_Jordan:
  assumes "bounded S" and neg: "negligible (frontier S)"
  shows "S \<in> lmeasurable"
proof -
  have "closure S \<in> lmeasurable"
    by (metis lmeasurable_closure \<open>bounded S\<close>)
  moreover have "interior S \<in> lmeasurable"
    by (simp add: lmeasurable_interior \<open>bounded S\<close>)
  moreover have "interior S \<subseteq> S"
    by (simp add: interior_subset)
  ultimately show ?thesis
    using assms by (metis (full_types) closure_subset completion.complete_sets_sandwich_fmeasurable measure_closure measure_interior)
qed

lemma measurable_convex: "\<lbrakk>convex S; bounded S\<rbrakk> \<Longrightarrow> S \<in> lmeasurable"
  by (simp add: measurable_Jordan negligible_convex_frontier)

subsection\<open>Negligibility of image under non-injective linear map\<close>

lemma negligible_Union_nat:
  assumes "\<And>n::nat. negligible(S n)"
  shows "negligible(\<Union>n. S n)"
proof -
  have "negligible (\<Union>m\<le>k. S m)" for k
    using assms by blast
  then have 0:  "integral UNIV (indicat_real (\<Union>m\<le>k. S m)) = 0"
    and 1: "(indicat_real (\<Union>m\<le>k. S m)) integrable_on UNIV" for k
    by (auto simp: negligible has_integral_iff)
  have 2: "\<And>k x. indicat_real (\<Union>m\<le>k. S m) x \<le> (indicat_real (\<Union>m\<le>Suc k. S m) x)"
    by (simp add: indicator_def)
  have 3: "\<And>x. (\<lambda>k. indicat_real (\<Union>m\<le>k. S m) x) \<longlonglongrightarrow> (indicat_real (\<Union>n. S n) x)"
    by (force simp: indicator_def eventually_sequentially intro: Lim_eventually)
  have 4: "bounded (range (\<lambda>k. integral UNIV (indicat_real (\<Union>m\<le>k. S m))))"
    by (simp add: 0 image_def)
  have *: "indicat_real (\<Union>n. S n) integrable_on UNIV \<and>
        (\<lambda>k. integral UNIV (indicat_real (\<Union>m\<le>k. S m))) \<longlonglongrightarrow> (integral UNIV (indicat_real (\<Union>n. S n)))"
    by (intro monotone_convergence_increasing 1 2 3 4)
  then have "integral UNIV (indicat_real (\<Union>n. S n)) = (0::real)"
    using LIMSEQ_unique by (auto simp: 0)
  then show ?thesis
    using * by (simp add: negligible_UNIV has_integral_iff)
qed


lemma negligible_linear_singular_image:
  fixes f :: "'n::euclidean_space \<Rightarrow> 'n"
  assumes "linear f" "\<not> inj f"
  shows "negligible (f ` S)"
proof -
  obtain a where "a \<noteq> 0" "\<And>S. f ` S \<subseteq> {x. a \<bullet> x = 0}"
    using assms linear_singular_image_hyperplane by blast
  then show "negligible (f ` S)"
    by (metis negligible_hyperplane negligible_subset)
qed

lemma measure_negligible_finite_Union:
  assumes "finite \<F>"
    and meas: "\<And>S. S \<in> \<F> \<Longrightarrow> S \<in> lmeasurable"
    and djointish: "pairwise (\<lambda>S T. negligible (S \<inter> T)) \<F>"
  shows "measure lebesgue (\<Union>\<F>) = (\<Sum>S\<in>\<F>. measure lebesgue S)"
  using assms
proof (induction)
  case empty
  then show ?case
    by auto
next
  case (insert S \<F>)
  then have "S \<in> lmeasurable" "\<Union>\<F> \<in> lmeasurable" "pairwise (\<lambda>S T. negligible (S \<inter> T)) \<F>"
    by (simp_all add: fmeasurable.finite_Union insert.hyps(1) insert.prems(1) pairwise_insert subsetI)
  then show ?case
  proof (simp add: measure_Un3 insert)
    have *: "\<And>T. T \<in> (\<inter>) S ` \<F> \<Longrightarrow> negligible T"
      using insert by (force simp: pairwise_def)
    have "negligible(S \<inter> \<Union>\<F>)"
      unfolding Int_Union
      by (rule negligible_Union) (simp_all add: * insert.hyps(1))
    then show "measure lebesgue (S \<inter> \<Union>\<F>) = 0"
      using negligible_imp_measure0 by blast
  qed
qed

lemma measure_negligible_finite_Union_image:
  assumes "finite S"
    and meas: "\<And>x. x \<in> S \<Longrightarrow> f x \<in> lmeasurable"
    and djointish: "pairwise (\<lambda>x y. negligible (f x \<inter> f y)) S"
  shows "measure lebesgue (\<Union>(f ` S)) = (\<Sum>x\<in>S. measure lebesgue (f x))"
proof -
  have "measure lebesgue (\<Union>(f ` S)) = sum (measure lebesgue) (f ` S)"
    using assms by (auto simp: pairwise_mono pairwise_image intro: measure_negligible_finite_Union)
  also have "\<dots> = sum (measure lebesgue \<circ> f) S"
    using djointish [unfolded pairwise_def] by (metis inf.idem negligible_imp_measure0 sum.reindex_nontrivial [OF \<open>finite S\<close>])
  also have "\<dots> = (\<Sum>x\<in>S. measure lebesgue (f x))"
    by simp
  finally show ?thesis .
qed

subsection \<open>Negligibility of a Lipschitz image of a negligible set\<close>

text\<open>The bound will be eliminated by a sort of onion argument\<close>
lemma locally_Lipschitz_negl_bounded:
  fixes f :: "'M::euclidean_space \<Rightarrow> 'N::euclidean_space"
  assumes MleN: "DIM('M) \<le> DIM('N)" "0 < B" "bounded S" "negligible S"
      and lips: "\<And>x. x \<in> S
                      \<Longrightarrow> \<exists>T. open T \<and> x \<in> T \<and>
                              (\<forall>y \<in> S \<inter> T. norm(f y - f x) \<le> B * norm(y - x))"
  shows "negligible (f ` S)"
  unfolding negligible_iff_null_sets
proof (clarsimp simp: completion.null_sets_outer)
  fix e::real
  assume "0 < e"
  have "S \<in> lmeasurable"
    using \<open>negligible S\<close> by (simp add: negligible_iff_null_sets fmeasurableI_null_sets)
  then have "S \<in> sets lebesgue"
    by blast
  have e22: "0 < e/2 / (2 * B * real DIM('M)) ^ DIM('N)"
    using \<open>0 < e\<close> \<open>0 < B\<close> by (simp add: divide_simps)
  obtain T where "open T" "S \<subseteq> T" "(T - S) \<in> lmeasurable" 
                 "measure lebesgue (T - S) < e/2 / (2 * B * DIM('M)) ^ DIM('N)"
    by (rule lmeasurable_outer_open [OF \<open>S \<in> sets lebesgue\<close> e22])
  then have T: "measure lebesgue T \<le> e/2 / (2 * B * DIM('M)) ^ DIM('N)"
    using \<open>negligible S\<close> by (simp add: measure_Diff_null_set negligible_iff_null_sets)
  have "\<exists>r. 0 < r \<and> r \<le> 1/2 \<and>
            (x \<in> S \<longrightarrow> (\<forall>y. norm(y - x) < r
                       \<longrightarrow> y \<in> T \<and> (y \<in> S \<longrightarrow> norm(f y - f x) \<le> B * norm(y - x))))"
        for x
  proof (cases "x \<in> S")
    case True
    obtain U where "open U" "x \<in> U" and U: "\<And>y. y \<in> S \<inter> U \<Longrightarrow> norm(f y - f x) \<le> B * norm(y - x)"
      using lips [OF \<open>x \<in> S\<close>] by auto
    have "x \<in> T \<inter> U"
      using \<open>S \<subseteq> T\<close> \<open>x \<in> U\<close> \<open>x \<in> S\<close> by auto
    then obtain \<epsilon> where "0 < \<epsilon>" "ball x \<epsilon> \<subseteq> T \<inter> U"
      by (metis \<open>open T\<close> \<open>open U\<close> openE open_Int)
    then show ?thesis
      apply (rule_tac x="min (1/2) \<epsilon>" in exI)
      apply (simp del: divide_const_simps)
      apply (intro allI impI conjI)
       apply (metis dist_commute dist_norm mem_ball subsetCE)
      by (metis Int_iff subsetCE U dist_norm mem_ball norm_minus_commute)
  next
    case False
    then show ?thesis
      by (rule_tac x="1/4" in exI) auto
  qed
  then obtain R where R12: "\<And>x. 0 < R x \<and> R x \<le> 1/2"
                and RT: "\<And>x y. \<lbrakk>x \<in> S; norm(y - x) < R x\<rbrakk> \<Longrightarrow> y \<in> T"
                and RB: "\<And>x y. \<lbrakk>x \<in> S; y \<in> S; norm(y - x) < R x\<rbrakk> \<Longrightarrow> norm(f y - f x) \<le> B * norm(y - x)"
    by metis+
  then have gaugeR: "gauge (\<lambda>x. ball x (R x))"
    by (simp add: gauge_def)
  obtain c where c: "S \<subseteq> cbox (-c *\<^sub>R One) (c *\<^sub>R One)" "box (-c *\<^sub>R One:: 'M) (c *\<^sub>R One) \<noteq> {}"
  proof -
    obtain B where B: "\<And>x. x \<in> S \<Longrightarrow> norm x \<le> B"
      using \<open>bounded S\<close> bounded_iff by blast
    show ?thesis
      apply (rule_tac c = "abs B + 1" in that)
      using norm_bound_Basis_le Basis_le_norm
       apply (fastforce simp: box_eq_empty mem_box dest!: B intro: order_trans)+
      done
  qed
  obtain \<D> where "countable \<D>"
     and Dsub: "\<Union>\<D> \<subseteq> cbox (-c *\<^sub>R One) (c *\<^sub>R One)"
     and cbox: "\<And>K. K \<in> \<D> \<Longrightarrow> interior K \<noteq> {} \<and> (\<exists>c d. K = cbox c d)"
     and pw:   "pairwise (\<lambda>A B. interior A \<inter> interior B = {}) \<D>"
     and Ksub: "\<And>K. K \<in> \<D> \<Longrightarrow> \<exists>x \<in> S \<inter> K. K \<subseteq> (\<lambda>x. ball x (R x)) x"
     and exN:  "\<And>u v. cbox u v \<in> \<D> \<Longrightarrow> \<exists>n. \<forall>i \<in> Basis. v \<bullet> i - u \<bullet> i = (2*c) / 2^n"
     and "S \<subseteq> \<Union>\<D>"
    using covering_lemma [OF c gaugeR]  by force
  have "\<exists>u v z. K = cbox u v \<and> box u v \<noteq> {} \<and> z \<in> S \<and> z \<in> cbox u v \<and>
                cbox u v \<subseteq> ball z (R z)" if "K \<in> \<D>" for K
  proof -
    obtain u v where "K = cbox u v"
      using \<open>K \<in> \<D>\<close> cbox by blast
    with that show ?thesis
      apply (rule_tac x=u in exI)
      apply (rule_tac x=v in exI)
      apply (metis Int_iff interior_cbox cbox Ksub)
      done
  qed
  then obtain uf vf zf
    where uvz: "\<And>K. K \<in> \<D> \<Longrightarrow>
                K = cbox (uf K) (vf K) \<and> box (uf K) (vf K) \<noteq> {} \<and> zf K \<in> S \<and>
                zf K \<in> cbox (uf K) (vf K) \<and> cbox (uf K) (vf K) \<subseteq> ball (zf K) (R (zf K))"
    by metis
  define prj1 where "prj1 \<equiv> \<lambda>x::'M. x \<bullet> (SOME i. i \<in> Basis)"
  define fbx where "fbx \<equiv> \<lambda>D. cbox (f(zf D) - (B * DIM('M) * (prj1(vf D - uf D))) *\<^sub>R One::'N)
                                    (f(zf D) + (B * DIM('M) * prj1(vf D - uf D)) *\<^sub>R One)"
  have vu_pos: "0 < prj1 (vf X - uf X)" if "X \<in> \<D>" for X
    using uvz [OF that] by (simp add: prj1_def box_ne_empty SOME_Basis inner_diff_left)
  have prj1_idem: "prj1 (vf X - uf X) = (vf X - uf X) \<bullet> i" if  "X \<in> \<D>" "i \<in> Basis" for X i
  proof -
    have "cbox (uf X) (vf X) \<in> \<D>"
      using uvz \<open>X \<in> \<D>\<close> by auto
    with exN obtain n where "\<And>i. i \<in> Basis \<Longrightarrow> vf X \<bullet> i - uf X \<bullet> i = (2*c) / 2^n"
      by blast
    then show ?thesis
      by (simp add: \<open>i \<in> Basis\<close> SOME_Basis inner_diff prj1_def)
  qed
  have countbl: "countable (fbx ` \<D>)"
    using \<open>countable \<D>\<close> by blast
  have "(\<Sum>k\<in>fbx`\<D>'. measure lebesgue k) \<le> e/2" if "\<D>' \<subseteq> \<D>" "finite \<D>'" for \<D>'
  proof -
    have BM_ge0: "0 \<le> B * (DIM('M) * prj1 (vf X - uf X))" if "X \<in> \<D>'" for X
      using \<open>0 < B\<close> \<open>\<D>' \<subseteq> \<D>\<close> that vu_pos by fastforce
    have "{} \<notin> \<D>'"
      using cbox \<open>\<D>' \<subseteq> \<D>\<close> interior_empty by blast
    have "(\<Sum>k\<in>fbx`\<D>'. measure lebesgue k) \<le> sum (measure lebesgue o fbx) \<D>'"
      by (rule sum_image_le [OF \<open>finite \<D>'\<close>]) (force simp: fbx_def)
    also have "\<dots> \<le> (\<Sum>X\<in>\<D>'. (2 * B * DIM('M)) ^ DIM('N) * measure lebesgue X)"
    proof (rule sum_mono)
      fix X assume "X \<in> \<D>'"
      then have "X \<in> \<D>" using \<open>\<D>' \<subseteq> \<D>\<close> by blast
      then have ufvf: "cbox (uf X) (vf X) = X"
        using uvz by blast
      have "prj1 (vf X - uf X) ^ DIM('M) = (\<Prod>i::'M \<in> Basis. prj1 (vf X - uf X))"
        by (rule prod_constant [symmetric])
      also have "\<dots> = (\<Prod>i\<in>Basis. vf X \<bullet> i - uf X \<bullet> i)"
        apply (rule prod.cong [OF refl])
        by (simp add: \<open>X \<in> \<D>\<close> inner_diff_left prj1_idem)
      finally have prj1_eq: "prj1 (vf X - uf X) ^ DIM('M) = (\<Prod>i\<in>Basis. vf X \<bullet> i - uf X \<bullet> i)" .
      have "uf X \<in> cbox (uf X) (vf X)" "vf X \<in> cbox (uf X) (vf X)"
        using uvz [OF \<open>X \<in> \<D>\<close>] by (force simp: mem_box)+
      moreover have "cbox (uf X) (vf X) \<subseteq> ball (zf X) (1/2)"
        by (meson R12 order_trans subset_ball uvz [OF \<open>X \<in> \<D>\<close>])
      ultimately have "uf X \<in> ball (zf X) (1/2)"  "vf X \<in> ball (zf X) (1/2)"
        by auto
      then have "dist (vf X) (uf X) \<le> 1"
        unfolding mem_ball
        by (metis dist_commute dist_triangle_half_l dual_order.order_iff_strict)
      then have 1: "prj1 (vf X - uf X) \<le> 1"
        unfolding prj1_def dist_norm using Basis_le_norm SOME_Basis order_trans by fastforce
      have 0: "0 \<le> prj1 (vf X - uf X)"
        using \<open>X \<in> \<D>\<close> prj1_def vu_pos by fastforce
      have "(measure lebesgue \<circ> fbx) X \<le> (2 * B * DIM('M)) ^ DIM('N) * content (cbox (uf X) (vf X))"
        apply (simp add: fbx_def content_cbox_cases algebra_simps BM_ge0 \<open>X \<in> \<D>'\<close> prod_constant)
        apply (simp add: power_mult_distrib \<open>0 < B\<close> prj1_eq [symmetric])
        using MleN 0 1 uvz \<open>X \<in> \<D>\<close>
        apply (fastforce simp add: box_ne_empty power_decreasing)
        done
      also have "\<dots> = (2 * B * DIM('M)) ^ DIM('N) * measure lebesgue X"
        by (subst (3) ufvf[symmetric]) simp
      finally show "(measure lebesgue \<circ> fbx) X \<le> (2 * B * DIM('M)) ^ DIM('N) * measure lebesgue X" .
    qed
    also have "\<dots> = (2 * B * DIM('M)) ^ DIM('N) * sum (measure lebesgue) \<D>'"
      by (simp add: sum_distrib_left)
    also have "\<dots> \<le> e/2"
    proof -
      have div: "\<D>' division_of \<Union>\<D>'"
        apply (auto simp: \<open>finite \<D>'\<close> \<open>{} \<notin> \<D>'\<close> division_of_def)
        using cbox that apply blast
        using pairwise_subset [OF pw \<open>\<D>' \<subseteq> \<D>\<close>] unfolding pairwise_def apply force+
        done
      have le_meaT: "measure lebesgue (\<Union>\<D>') \<le> measure lebesgue T"
      proof (rule measure_mono_fmeasurable)
        show "(\<Union>\<D>') \<in> sets lebesgue"
          using div lmeasurable_division by auto
        have "\<Union>\<D>' \<subseteq> \<Union>\<D>"
          using \<open>\<D>' \<subseteq> \<D>\<close> by blast
        also have "... \<subseteq> T"
        proof (clarify)
          fix x D
          assume "x \<in> D" "D \<in> \<D>"
          show "x \<in> T"
            using Ksub [OF \<open>D \<in> \<D>\<close>]
            by (metis \<open>x \<in> D\<close> Int_iff dist_norm mem_ball norm_minus_commute subsetD RT)
        qed
        finally show "\<Union>\<D>' \<subseteq> T" .
        show "T \<in> lmeasurable"
          using \<open>S \<in> lmeasurable\<close> \<open>S \<subseteq> T\<close> \<open>T - S \<in> lmeasurable\<close> fmeasurable_Diff_D by blast
      qed 
      have "sum (measure lebesgue) \<D>' = sum content \<D>'"
        using  \<open>\<D>' \<subseteq> \<D>\<close> cbox by (force intro: sum.cong)
      then have "(2 * B * DIM('M)) ^ DIM('N) * sum (measure lebesgue) \<D>' =
                 (2 * B * real DIM('M)) ^ DIM('N) * measure lebesgue (\<Union>\<D>')"
        using content_division [OF div] by auto
      also have "\<dots> \<le> (2 * B * real DIM('M)) ^ DIM('N) * measure lebesgue T"
        apply (rule mult_left_mono [OF le_meaT])
        using \<open>0 < B\<close>
        apply (simp add: algebra_simps)
        done
      also have "\<dots> \<le> e/2"
        using T \<open>0 < B\<close> by (simp add: field_simps)
      finally show ?thesis .
    qed
    finally show ?thesis .
  qed
  then have e2: "sum (measure lebesgue) \<G> \<le> e/2" if "\<G> \<subseteq> fbx ` \<D>" "finite \<G>" for \<G>
    by (metis finite_subset_image that)
  show "\<exists>W\<in>lmeasurable. f ` S \<subseteq> W \<and> measure lebesgue W < e"
  proof (intro bexI conjI)
    have "\<exists>X\<in>\<D>. f y \<in> fbx X" if "y \<in> S" for y
    proof -
      obtain X where "y \<in> X" "X \<in> \<D>"
        using \<open>S \<subseteq> \<Union>\<D>\<close> \<open>y \<in> S\<close> by auto
      then have y: "y \<in> ball(zf X) (R(zf X))"
        using uvz by fastforce
      have conj_le_eq: "z - b \<le> y \<and> y \<le> z + b \<longleftrightarrow> abs(y - z) \<le> b" for z y b::real
        by auto
      have yin: "y \<in> cbox (uf X) (vf X)" and zin: "(zf X) \<in> cbox (uf X) (vf X)"
        using uvz \<open>X \<in> \<D>\<close> \<open>y \<in> X\<close> by auto
      have "norm (y - zf X) \<le> (\<Sum>i\<in>Basis. \<bar>(y - zf X) \<bullet> i\<bar>)"
        by (rule norm_le_l1)
      also have "\<dots> \<le> real DIM('M) * prj1 (vf X - uf X)"
      proof (rule sum_bounded_above)
        fix j::'M assume j: "j \<in> Basis"
        show "\<bar>(y - zf X) \<bullet> j\<bar> \<le> prj1 (vf X - uf X)"
          using yin zin j
          by (fastforce simp add: mem_box prj1_idem [OF \<open>X \<in> \<D>\<close> j] inner_diff_left)
      qed
      finally have nole: "norm (y - zf X) \<le> DIM('M) * prj1 (vf X - uf X)"
        by simp
      have fle: "\<bar>f y \<bullet> i - f(zf X) \<bullet> i\<bar> \<le> B * DIM('M) * prj1 (vf X - uf X)" if "i \<in> Basis" for i
      proof -
        have "\<bar>f y \<bullet> i - f (zf X) \<bullet> i\<bar> = \<bar>(f y - f (zf X)) \<bullet> i\<bar>"
          by (simp add: algebra_simps)
        also have "\<dots> \<le> norm (f y - f (zf X))"
          by (simp add: Basis_le_norm that)
        also have "\<dots> \<le> B * norm(y - zf X)"
          by (metis uvz RB \<open>X \<in> \<D>\<close> dist_commute dist_norm mem_ball \<open>y \<in> S\<close> y)
        also have "\<dots> \<le> B * real DIM('M) * prj1 (vf X - uf X)"
          using \<open>0 < B\<close> by (simp add: nole)
        finally show ?thesis .
      qed
      show ?thesis
        by (rule_tac x=X in bexI)
           (auto simp: fbx_def prj1_idem mem_box conj_le_eq inner_add inner_diff fle \<open>X \<in> \<D>\<close>)
    qed
    then show "f ` S \<subseteq> (\<Union>D\<in>\<D>. fbx D)" by auto
  next
    have 1: "\<And>D. D \<in> \<D> \<Longrightarrow> fbx D \<in> lmeasurable"
      by (auto simp: fbx_def)
    have 2: "I' \<subseteq> \<D> \<Longrightarrow> finite I' \<Longrightarrow> measure lebesgue (\<Union>D\<in>I'. fbx D) \<le> e/2" for I'
      by (rule order_trans[OF measure_Union_le e2]) (auto simp: fbx_def)
    show "(\<Union>D\<in>\<D>. fbx D) \<in> lmeasurable"
      by (intro fmeasurable_UN_bound[OF \<open>countable \<D>\<close> 1 2])
    have "measure lebesgue (\<Union>D\<in>\<D>. fbx D) \<le> e/2"
      by (intro measure_UN_bound[OF \<open>countable \<D>\<close> 1 2])
    then show "measure lebesgue (\<Union>D\<in>\<D>. fbx D) < e"
      using \<open>0 < e\<close> by linarith
  qed
qed

proposition negligible_locally_Lipschitz_image:
  fixes f :: "'M::euclidean_space \<Rightarrow> 'N::euclidean_space"
  assumes MleN: "DIM('M) \<le> DIM('N)" "negligible S"
      and lips: "\<And>x. x \<in> S
                      \<Longrightarrow> \<exists>T B. open T \<and> x \<in> T \<and>
                              (\<forall>y \<in> S \<inter> T. norm(f y - f x) \<le> B * norm(y - x))"
    shows "negligible (f ` S)"
proof -
  let ?S = "\<lambda>n. ({x \<in> S. norm x \<le> n \<and>
                          (\<exists>T. open T \<and> x \<in> T \<and>
                               (\<forall>y\<in>S \<inter> T. norm (f y - f x) \<le> (real n + 1) * norm (y - x)))})"
  have negfn: "f ` ?S n \<in> null_sets lebesgue" for n::nat
    unfolding negligible_iff_null_sets[symmetric]
    apply (rule_tac B = "real n + 1" in locally_Lipschitz_negl_bounded)
    by (auto simp: MleN bounded_iff intro: negligible_subset [OF \<open>negligible S\<close>])
  have "S = (\<Union>n. ?S n)"
  proof (intro set_eqI iffI)
    fix x assume "x \<in> S"
    with lips obtain T B where T: "open T" "x \<in> T"
                           and B: "\<And>y. y \<in> S \<inter> T \<Longrightarrow> norm(f y - f x) \<le> B * norm(y - x)"
      by metis+
    have no: "norm (f y - f x) \<le> (nat \<lceil>max B (norm x)\<rceil> + 1) * norm (y - x)" if "y \<in> S \<inter> T" for y
    proof -
      have "B * norm(y - x) \<le> (nat \<lceil>max B (norm x)\<rceil> + 1) * norm (y - x)"
        by (meson max.cobounded1 mult_right_mono nat_ceiling_le_eq nat_le_iff_add norm_ge_zero order_trans)
      then show ?thesis
        using B order_trans that by blast
    qed
    have "x \<in> ?S (nat (ceiling (max B (norm x))))"
      apply (simp add: \<open>x \<in> S \<close>, rule)
      using real_nat_ceiling_ge max.bounded_iff apply blast
      using T no
      apply (force simp: algebra_simps)
      done
    then show "x \<in> (\<Union>n. ?S n)" by force
  qed auto
  then show ?thesis
    by (rule ssubst) (auto simp: image_Union negligible_iff_null_sets intro: negfn)
qed

corollary negligible_differentiable_image_negligible:
  fixes f :: "'M::euclidean_space \<Rightarrow> 'N::euclidean_space"
  assumes MleN: "DIM('M) \<le> DIM('N)" "negligible S"
      and diff_f: "f differentiable_on S"
    shows "negligible (f ` S)"
proof -
  have "\<exists>T B. open T \<and> x \<in> T \<and> (\<forall>y \<in> S \<inter> T. norm(f y - f x) \<le> B * norm(y - x))"
        if "x \<in> S" for x
  proof -
    obtain f' where "linear f'"
      and f': "\<And>e. e>0 \<Longrightarrow>
                  \<exists>d>0. \<forall>y\<in>S. norm (y - x) < d \<longrightarrow>
                              norm (f y - f x - f' (y - x)) \<le> e * norm (y - x)"
      using diff_f \<open>x \<in> S\<close>
      by (auto simp: linear_linear differentiable_on_def differentiable_def has_derivative_within_alt)
    obtain B where "B > 0" and B: "\<forall>x. norm (f' x) \<le> B * norm x"
      using linear_bounded_pos \<open>linear f'\<close> by blast
    obtain d where "d>0"
              and d: "\<And>y. \<lbrakk>y \<in> S; norm (y - x) < d\<rbrakk> \<Longrightarrow>
                          norm (f y - f x - f' (y - x)) \<le> norm (y - x)"
      using f' [of 1] by (force simp:)
    have *: "norm (f y - f x) \<le> (B + 1) * norm (y - x)"
              if "y \<in> S" "norm (y - x) < d" for y
    proof -
      have "norm (f y - f x) -B *  norm (y - x) \<le> norm (f y - f x) - norm (f' (y - x))"
        by (simp add: B)
      also have "\<dots> \<le> norm (f y - f x - f' (y - x))"
        by (rule norm_triangle_ineq2)
      also have "... \<le> norm (y - x)"
        by (rule d [OF that])
      finally show ?thesis
        by (simp add: algebra_simps)
    qed
    show ?thesis
      apply (rule_tac x="ball x d" in exI)
      apply (rule_tac x="B+1" in exI)
      using \<open>d>0\<close>
      apply (auto simp: dist_norm norm_minus_commute intro!: *)
      done
  qed
  with negligible_locally_Lipschitz_image assms show ?thesis by metis
qed

corollary negligible_differentiable_image_lowdim:
  fixes f :: "'M::euclidean_space \<Rightarrow> 'N::euclidean_space"
  assumes MlessN: "DIM('M) < DIM('N)" and diff_f: "f differentiable_on S"
    shows "negligible (f ` S)"
proof -
  have "x \<le> DIM('M) \<Longrightarrow> x \<le> DIM('N)" for x
    using MlessN by linarith
  obtain lift :: "'M * real \<Rightarrow> 'N" and drop :: "'N \<Rightarrow> 'M * real" and j :: 'N
    where "linear lift" "linear drop" and dropl [simp]: "\<And>z. drop (lift z) = z"
      and "j \<in> Basis" and j: "\<And>x. lift(x,0) \<bullet> j = 0"
    using lowerdim_embeddings [OF MlessN] by metis
  have "negligible {x. x\<bullet>j = 0}"
    by (metis \<open>j \<in> Basis\<close> negligible_standard_hyperplane)
  then have neg0S: "negligible ((\<lambda>x. lift (x, 0)) ` S)"
    apply (rule negligible_subset)
    by (simp add: image_subsetI j)
  have diff_f': "f \<circ> fst \<circ> drop differentiable_on (\<lambda>x. lift (x, 0)) ` S"
    using diff_f
    apply (clarsimp simp add: differentiable_on_def)
    apply (intro differentiable_chain_within linear_imp_differentiable [OF \<open>linear drop\<close>]
             linear_imp_differentiable [OF fst_linear])
    apply (force simp: image_comp o_def)
    done
  have "f = (f o fst o drop o (\<lambda>x. lift (x, 0)))"
    by (simp add: o_def)
  then show ?thesis
    apply (rule ssubst)
    apply (subst image_comp [symmetric])
    apply (metis negligible_differentiable_image_negligible order_refl diff_f' neg0S)
    done
qed

subsection\<open>Measurability of countable unions and intersections of various kinds.\<close>

lemma
  assumes S: "\<And>n. S n \<in> lmeasurable"
    and leB: "\<And>n. measure lebesgue (S n) \<le> B"
    and nest: "\<And>n. S n \<subseteq> S(Suc n)"
  shows measurable_nested_Union: "(\<Union>n. S n) \<in> lmeasurable"
  and measure_nested_Union:  "(\<lambda>n. measure lebesgue (S n)) \<longlonglongrightarrow> measure lebesgue (\<Union>n. S n)" (is ?Lim)
proof -
  have 1: "\<And>n. (indicat_real (S n)) integrable_on UNIV"
    using S measurable_integrable by blast
  have 2: "\<And>n x::'a. indicat_real (S n) x \<le> (indicat_real (S (Suc n)) x)"
    by (simp add: indicator_leI nest rev_subsetD)
  have 3: "\<And>x. (\<lambda>n. indicat_real (S n) x) \<longlonglongrightarrow> (indicat_real (UNION UNIV S) x)"
    apply (rule Lim_eventually)
    apply (simp add: indicator_def)
    by (metis eventually_sequentiallyI lift_Suc_mono_le nest subsetCE)
  have 4: "bounded (range (\<lambda>n. integral UNIV (indicat_real (S n))))"
    using leB by (auto simp: lmeasure_integral_UNIV [symmetric] S bounded_iff)
  have "(\<Union>n. S n) \<in> lmeasurable \<and> ?Lim"
    apply (simp add: lmeasure_integral_UNIV S cong: conj_cong)
    apply (simp add: measurable_integrable)
    apply (rule monotone_convergence_increasing [OF 1 2 3 4])
    done
  then show "(\<Union>n. S n) \<in> lmeasurable" "?Lim"
    by auto
qed

lemma
  assumes S: "\<And>n. S n \<in> lmeasurable"
    and djointish: "pairwise (\<lambda>m n. negligible (S m \<inter> S n)) UNIV"
    and leB: "\<And>n. (\<Sum>k\<le>n. measure lebesgue (S k)) \<le> B"
  shows measurable_countable_negligible_Union: "(\<Union>n. S n) \<in> lmeasurable"
  and   measure_countable_negligible_Union:    "(\<lambda>n. (measure lebesgue (S n))) sums measure lebesgue (\<Union>n. S n)" (is ?Sums)
proof -
  have 1: "UNION {..n} S \<in> lmeasurable" for n
    using S by blast
  have 2: "measure lebesgue (UNION {..n} S) \<le> B" for n
  proof -
    have "measure lebesgue (UNION {..n} S) \<le> (\<Sum>k\<le>n. measure lebesgue (S k))"
      by (simp add: S fmeasurableD measure_UNION_le)
    with leB show ?thesis
      using order_trans by blast
  qed
  have 3: "\<And>n. UNION {..n} S \<subseteq> UNION {..Suc n} S"
    by (simp add: SUP_subset_mono)
  have eqS: "(\<Union>n. S n) = (\<Union>n. UNION {..n} S)"
    using atLeastAtMost_iff by blast
  also have "(\<Union>n. UNION {..n} S) \<in> lmeasurable"
    by (intro measurable_nested_Union [OF 1 2] 3)
  finally show "(\<Union>n. S n) \<in> lmeasurable" .
  have eqm: "(\<Sum>i\<le>n. measure lebesgue (S i)) = measure lebesgue (UNION {..n} S)" for n
    using assms by (simp add: measure_negligible_finite_Union_image pairwise_mono)
  have "(\<lambda>n. (measure lebesgue (S n))) sums measure lebesgue (\<Union>n. UNION {..n} S)"
    by (simp add: sums_def' eqm atLeast0AtMost) (intro measure_nested_Union [OF 1 2] 3)
  then show ?Sums
    by (simp add: eqS)
qed

lemma negligible_countable_Union [intro]:
  assumes "countable \<F>" and meas: "\<And>S. S \<in> \<F> \<Longrightarrow> negligible S"
  shows "negligible (\<Union>\<F>)"
proof (cases "\<F> = {}")
  case False
  then show ?thesis
    by (metis from_nat_into range_from_nat_into assms negligible_Union_nat)
qed simp

lemma
  assumes S: "\<And>n. (S n) \<in> lmeasurable"
    and djointish: "pairwise (\<lambda>m n. negligible (S m \<inter> S n)) UNIV"
    and bo: "bounded (\<Union>n. S n)"
  shows measurable_countable_negligible_Union_bounded: "(\<Union>n. S n) \<in> lmeasurable"
  and   measure_countable_negligible_Union_bounded:    "(\<lambda>n. (measure lebesgue (S n))) sums measure lebesgue (\<Union>n. S n)" (is ?Sums)
proof -
  obtain a b where ab: "(\<Union>n. S n) \<subseteq> cbox a b"
    using bo bounded_subset_cbox_symmetric by metis
  then have B: "(\<Sum>k\<le>n. measure lebesgue (S k)) \<le> measure lebesgue (cbox a b)" for n
  proof -
    have "(\<Sum>k\<le>n. measure lebesgue (S k)) = measure lebesgue (UNION {..n} S)"
      using measure_negligible_finite_Union_image [OF _ _ pairwise_subset] djointish
      by (metis S finite_atMost subset_UNIV)
    also have "\<dots> \<le> measure lebesgue (cbox a b)"
      apply (rule measure_mono_fmeasurable)
      using ab S by force+
    finally show ?thesis .
  qed
  show "(\<Union>n. S n) \<in> lmeasurable"
    by (rule measurable_countable_negligible_Union [OF S djointish B])
  show ?Sums
    by (rule measure_countable_negligible_Union [OF S djointish B])
qed

lemma measure_countable_Union_approachable:
  assumes "countable \<D>" "e > 0" and measD: "\<And>d. d \<in> \<D> \<Longrightarrow> d \<in> lmeasurable"
      and B: "\<And>D'. \<lbrakk>D' \<subseteq> \<D>; finite D'\<rbrakk> \<Longrightarrow> measure lebesgue (\<Union>D') \<le> B"
    obtains D' where "D' \<subseteq> \<D>" "finite D'" "measure lebesgue (\<Union>\<D>) - e < measure lebesgue (\<Union>D')"
proof (cases "\<D> = {}")
  case True
  then show ?thesis
    by (simp add: \<open>e > 0\<close> that)
next
  case False
  let ?S = "\<lambda>n. \<Union>k \<le> n. from_nat_into \<D> k"
  have "(\<lambda>n. measure lebesgue (?S n)) \<longlonglongrightarrow> measure lebesgue (\<Union>n. ?S n)"
  proof (rule measure_nested_Union)
    show "?S n \<in> lmeasurable" for n
      by (simp add: False fmeasurable.finite_UN from_nat_into measD)
    show "measure lebesgue (?S n) \<le> B" for n
      by (metis (mono_tags, lifting) B False finite_atMost finite_imageI from_nat_into image_iff subsetI)
    show "?S n \<subseteq> ?S (Suc n)" for n
      by force
  qed
  then obtain N where N: "\<And>n. n \<ge> N \<Longrightarrow> dist (measure lebesgue (?S n)) (measure lebesgue (\<Union>n. ?S n)) < e"
    using metric_LIMSEQ_D \<open>e > 0\<close> by blast
  show ?thesis
  proof
    show "from_nat_into \<D> ` {..N} \<subseteq> \<D>"
      by (auto simp: False from_nat_into)
    have eq: "(\<Union>n. \<Union>k\<le>n. from_nat_into \<D> k) = (\<Union>\<D>)"
      using \<open>countable \<D>\<close> False
      by (auto intro: from_nat_into dest: from_nat_into_surj [OF \<open>countable \<D>\<close>])
    show "measure lebesgue (\<Union>\<D>) - e < measure lebesgue (UNION {..N} (from_nat_into \<D>))"
      using N [OF order_refl]
      by (auto simp: eq algebra_simps dist_norm)
  qed auto
qed


subsection\<open>Negligibility is a local property\<close>

lemma locally_negligible_alt:
    "negligible S \<longleftrightarrow> (\<forall>x \<in> S. \<exists>U. openin (subtopology euclidean S) U \<and> x \<in> U \<and> negligible U)"
     (is "_ = ?rhs")
proof
  assume "negligible S"
  then show ?rhs
    using openin_subtopology_self by blast
next
  assume ?rhs
  then obtain U where ope: "\<And>x. x \<in> S \<Longrightarrow> openin (subtopology euclidean S) (U x)"
    and cov: "\<And>x. x \<in> S \<Longrightarrow> x \<in> U x"
    and neg: "\<And>x. x \<in> S \<Longrightarrow> negligible (U x)"
    by metis
  obtain \<F> where "\<F> \<subseteq> U ` S" "countable \<F>" and eq: "\<Union>\<F> = UNION S U"
    using ope by (force intro: Lindelof_openin [of "U ` S" S])
  then have "negligible (\<Union>\<F>)"
    by (metis imageE neg negligible_countable_Union subset_eq)
  with eq have "negligible (UNION S U)"
    by metis
  moreover have "S \<subseteq> UNION S U"
    using cov by blast
  ultimately show "negligible S"
    using negligible_subset by blast
qed

lemma locally_negligible:
     "locally negligible S \<longleftrightarrow> negligible S"
  unfolding locally_def
  apply safe
   apply (meson negligible_subset openin_subtopology_self locally_negligible_alt)
  by (meson negligible_subset openin_imp_subset order_refl)


subsection\<open>Integral bounds\<close>

lemma set_integral_norm_bound:
  fixes f :: "_ \<Rightarrow> 'a :: {banach, second_countable_topology}"
  shows "set_integrable M k f \<Longrightarrow> norm (LINT x:k|M. f x) \<le> LINT x:k|M. norm (f x)"
  using integral_norm_bound[of M "\<lambda>x. indicator k x *\<^sub>R f x"] by (simp add: set_lebesgue_integral_def)

lemma set_integral_finite_UN_AE:
  fixes f :: "_ \<Rightarrow> _ :: {banach, second_countable_topology}"
  assumes "finite I"
    and ae: "\<And>i j. i \<in> I \<Longrightarrow> j \<in> I \<Longrightarrow> AE x in M. (x \<in> A i \<and> x \<in> A j) \<longrightarrow> i = j"
    and [measurable]: "\<And>i. i \<in> I \<Longrightarrow> A i \<in> sets M"
    and f: "\<And>i. i \<in> I \<Longrightarrow> set_integrable M (A i) f"
  shows "LINT x:(\<Union>i\<in>I. A i)|M. f x = (\<Sum>i\<in>I. LINT x:A i|M. f x)"
  using \<open>finite I\<close> order_refl[of I]
proof (induction I rule: finite_subset_induct')
  case (insert i I')
  have "AE x in M. (\<forall>j\<in>I'. x \<in> A i \<longrightarrow> x \<notin> A j)"
  proof (intro AE_ball_countable[THEN iffD2] ballI)
    fix j assume "j \<in> I'"
    with \<open>I' \<subseteq> I\<close> \<open>i \<notin> I'\<close> have "i \<noteq> j" "j \<in> I"
      by auto
    then show "AE x in M. x \<in> A i \<longrightarrow> x \<notin> A j"
      using ae[of i j] \<open>i \<in> I\<close> by auto
  qed (use \<open>finite I'\<close> in \<open>rule countable_finite\<close>)
  then have "AE x\<in>A i in M. \<forall>xa\<in>I'. x \<notin> A xa "
    by auto
  with insert.hyps insert.IH[symmetric]
  show ?case
    by (auto intro!: set_integral_Un_AE sets.finite_UN f set_integrable_UN)
qed (simp add: set_lebesgue_integral_def)

lemma set_integrable_norm:
  fixes f :: "'a \<Rightarrow> 'b::{banach, second_countable_topology}"
  assumes f: "set_integrable M k f" shows "set_integrable M k (\<lambda>x. norm (f x))"
  using integrable_norm f by (force simp add: set_integrable_def)
 
lemma absolutely_integrable_bounded_variation:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  assumes f: "f absolutely_integrable_on UNIV"
  obtains B where "\<forall>d. d division_of (\<Union>d) \<longrightarrow> sum (\<lambda>k. norm (integral k f)) d \<le> B"
proof (rule that[of "integral UNIV (\<lambda>x. norm (f x))"]; safe)
  fix d :: "'a set set" assume d: "d division_of \<Union>d"
  have *: "k \<in> d \<Longrightarrow> f absolutely_integrable_on k" for k
    using f[THEN set_integrable_subset, of k] division_ofD(2,4)[OF d, of k] by auto
  note d' = division_ofD[OF d]
  have "(\<Sum>k\<in>d. norm (integral k f)) = (\<Sum>k\<in>d. norm (LINT x:k|lebesgue. f x))"
    by (intro sum.cong refl arg_cong[where f=norm] set_lebesgue_integral_eq_integral(2)[symmetric] *)
  also have "\<dots> \<le> (\<Sum>k\<in>d. LINT x:k|lebesgue. norm (f x))"
    by (intro sum_mono set_integral_norm_bound *)
  also have "\<dots> = (\<Sum>k\<in>d. integral k (\<lambda>x. norm (f x)))"
    by (intro sum.cong refl set_lebesgue_integral_eq_integral(2) set_integrable_norm *)
  also have "\<dots> \<le> integral (\<Union>d) (\<lambda>x. norm (f x))"
    using integrable_on_subdivision[OF d] assms f unfolding absolutely_integrable_on_def
    by (subst integral_combine_division_topdown[OF _ d]) auto
  also have "\<dots> \<le> integral UNIV (\<lambda>x. norm (f x))"
    using integrable_on_subdivision[OF d] assms unfolding absolutely_integrable_on_def
    by (intro integral_subset_le) auto
  finally show "(\<Sum>k\<in>d. norm (integral k f)) \<le> integral UNIV (\<lambda>x. norm (f x))" .
qed

lemma absdiff_norm_less:
  assumes "sum (\<lambda>x. norm (f x - g x)) s < e"
    and "finite s"
  shows "\<bar>sum (\<lambda>x. norm(f x)) s - sum (\<lambda>x. norm(g x)) s\<bar> < e"
  unfolding sum_subtractf[symmetric]
  apply (rule le_less_trans[OF sum_abs])
  apply (rule le_less_trans[OF _ assms(1)])
  apply (rule sum_mono)
  apply (rule norm_triangle_ineq3)
  done

proposition bounded_variation_absolutely_integrable_interval:
  fixes f :: "'n::euclidean_space \<Rightarrow> 'm::euclidean_space"
  assumes f: "f integrable_on cbox a b"
    and *: "\<And>d. d division_of (cbox a b) \<Longrightarrow> sum (\<lambda>K. norm(integral K f)) d \<le> B"
  shows "f absolutely_integrable_on cbox a b"
proof -
  let ?f = "\<lambda>d. \<Sum>K\<in>d. norm (integral K f)" and ?D = "{d. d division_of (cbox a b)}"
  have D_1: "?D \<noteq> {}"
    by (rule elementary_interval[of a b]) auto
  have D_2: "bdd_above (?f`?D)"
    by (metis * mem_Collect_eq bdd_aboveI2)
  note D = D_1 D_2
  let ?S = "SUP x:?D. ?f x"
  have *: "\<exists>\<gamma>. gauge \<gamma> \<and>
             (\<forall>p. p tagged_division_of cbox a b \<and>
                  \<gamma> fine p \<longrightarrow>
                  norm ((\<Sum>(x,k) \<in> p. content k *\<^sub>R norm (f x)) - ?S) < e)"
    if e: "e > 0" for e
  proof -
    have "?S - e/2 < ?S" using \<open>e > 0\<close> by simp
    then obtain d where d: "d division_of (cbox a b)" "?S - e/2 < (\<Sum>k\<in>d. norm (integral k f))"
      unfolding less_cSUP_iff[OF D] by auto
    note d' = division_ofD[OF this(1)]

    have "\<exists>e>0. \<forall>i\<in>d. x \<notin> i \<longrightarrow> ball x e \<inter> i = {}" for x
    proof -
      have "\<exists>d'>0. \<forall>x'\<in>\<Union>{i \<in> d. x \<notin> i}. d' \<le> dist x x'"
      proof (rule separate_point_closed)
        show "closed (\<Union>{i \<in> d. x \<notin> i})"
          using d' by force
        show "x \<notin> \<Union>{i \<in> d. x \<notin> i}"
          by auto
      qed 
      then show ?thesis
        by force
    qed
    then obtain k where k: "\<And>x. 0 < k x" "\<And>i x. \<lbrakk>i \<in> d; x \<notin> i\<rbrakk> \<Longrightarrow> ball x (k x) \<inter> i = {}"
      by metis
    have "e/2 > 0"
      using e by auto
    with Henstock_lemma[OF f] 
    obtain \<gamma> where g: "gauge \<gamma>"
      "\<And>p. \<lbrakk>p tagged_partial_division_of cbox a b; \<gamma> fine p\<rbrakk> 
                \<Longrightarrow> (\<Sum>(x,k) \<in> p. norm (content k *\<^sub>R f x - integral k f)) < e/2"
      by (metis (no_types, lifting))      
    let ?g = "\<lambda>x. \<gamma> x \<inter> ball x (k x)"
    show ?thesis 
    proof (intro exI conjI allI impI)
      show "gauge ?g"
        using g(1) k(1) by (auto simp: gauge_def)
    next
      fix p
      assume "p tagged_division_of (cbox a b) \<and> ?g fine p"
      then have p: "p tagged_division_of cbox a b" "\<gamma> fine p" "(\<lambda>x. ball x (k x)) fine p"
        by (auto simp: fine_Int)
      note p' = tagged_division_ofD[OF p(1)]
      define p' where "p' = {(x,k) | x k. \<exists>i l. x \<in> i \<and> i \<in> d \<and> (x,l) \<in> p \<and> k = i \<inter> l}"
      have gp': "\<gamma> fine p'"
        using p(2) by (auto simp: p'_def fine_def)
      have p'': "p' tagged_division_of (cbox a b)"
      proof (rule tagged_division_ofI)
        show "finite p'"
        proof (rule finite_subset)
          show "p' \<subseteq> (\<lambda>(k, x, l). (x, k \<inter> l)) ` (d \<times> p)"
            by (force simp: p'_def image_iff)
          show "finite ((\<lambda>(k, x, l). (x, k \<inter> l)) ` (d \<times> p))"
            by (simp add: d'(1) p'(1))
        qed
      next
        fix x K
        assume "(x, K) \<in> p'"
        then have "\<exists>i l. x \<in> i \<and> i \<in> d \<and> (x, l) \<in> p \<and> K = i \<inter> l"
          unfolding p'_def by auto
        then obtain i l where il: "x \<in> i" "i \<in> d" "(x, l) \<in> p" "K = i \<inter> l" by blast
        show "x \<in> K" and "K \<subseteq> cbox a b"
          using p'(2-3)[OF il(3)] il by auto
        show "\<exists>a b. K = cbox a b"
          unfolding il using p'(4)[OF il(3)] d'(4)[OF il(2)] by (meson Int_interval)
      next
        fix x1 K1
        assume "(x1, K1) \<in> p'"
        then have "\<exists>i l. x1 \<in> i \<and> i \<in> d \<and> (x1, l) \<in> p \<and> K1 = i \<inter> l"
          unfolding p'_def by auto
        then obtain i1 l1 where il1: "x1 \<in> i1" "i1 \<in> d" "(x1, l1) \<in> p" "K1 = i1 \<inter> l1" by blast
        fix x2 K2
        assume "(x2,K2) \<in> p'"
        then have "\<exists>i l. x2 \<in> i \<and> i \<in> d \<and> (x2, l) \<in> p \<and> K2 = i \<inter> l"
          unfolding p'_def by auto
        then obtain i2 l2 where il2: "x2 \<in> i2" "i2 \<in> d" "(x2, l2) \<in> p" "K2 = i2 \<inter> l2" by blast
        assume "(x1, K1) \<noteq> (x2, K2)"
        then have "interior i1 \<inter> interior i2 = {} \<or> interior l1 \<inter> interior l2 = {}"
          using d'(5)[OF il1(2) il2(2)] p'(5)[OF il1(3) il2(3)]  by (auto simp: il1 il2)
        then show "interior K1 \<inter> interior K2 = {}"
          unfolding il1 il2 by auto
      next
        have *: "\<forall>(x, X) \<in> p'. X \<subseteq> cbox a b"
          unfolding p'_def using d' by blast
        have "y \<in> \<Union>{K. \<exists>x. (x, K) \<in> p'}" if y: "y \<in> cbox a b" for y
        proof -
          obtain x l where xl: "(x, l) \<in> p" "y \<in> l" 
            using y unfolding p'(6)[symmetric] by auto
          obtain i where i: "i \<in> d" "y \<in> i" 
            using y unfolding d'(6)[symmetric] by auto
          have "x \<in> i"
            using fineD[OF p(3) xl(1)] using k(2) i xl by auto
          then show ?thesis
            unfolding p'_def by (rule_tac X="i \<inter> l" in UnionI) (use i xl in auto)
        qed
        show "\<Union>{K. \<exists>x. (x, K) \<in> p'} = cbox a b"
        proof
          show "\<Union>{k. \<exists>x. (x, k) \<in> p'} \<subseteq> cbox a b"
            using * by auto
        next
          show "cbox a b \<subseteq> \<Union>{k. \<exists>x. (x, k) \<in> p'}"
          proof 
            fix y
            assume y: "y \<in> cbox a b"
            obtain x L where xl: "(x, L) \<in> p" "y \<in> L" 
              using y unfolding p'(6)[symmetric] by auto
            obtain I where i: "I \<in> d" "y \<in> I" 
              using y unfolding d'(6)[symmetric] by auto
            have "x \<in> I"
              using fineD[OF p(3) xl(1)] using k(2) i xl by auto
            then show "y \<in> \<Union>{k. \<exists>x. (x, k) \<in> p'}"
              apply (rule_tac X="I \<inter> L" in UnionI)
              using i xl by (auto simp: p'_def)
          qed
        qed
      qed

      then have sum_less_e2: "(\<Sum>(x,K) \<in> p'. norm (content K *\<^sub>R f x - integral K f)) < e/2"
        using g(2) gp' tagged_division_of_def by blast

      have "(x, I \<inter> L) \<in> p'" if x: "(x, L) \<in> p" "I \<in> d" and y: "y \<in> I" "y \<in> L"
        for x I L y
      proof -
        have "x \<in> I"
          using fineD[OF p(3) that(1)] k(2)[OF \<open>I \<in> d\<close>] y by auto
        with x have "(\<exists>i l. x \<in> i \<and> i \<in> d \<and> (x, l) \<in> p \<and> I \<inter> L = i \<inter> l)"
          by blast
        then have "(x, I \<inter> L) \<in> p'"
          by (simp add: p'_def)
        with y show ?thesis by auto
      qed
      moreover have "\<exists>y i l. (x, K) = (y, i \<inter> l) \<and> (y, l) \<in> p \<and> i \<in> d \<and> i \<inter> l \<noteq> {}"
        if xK: "(x,K) \<in> p'" for x K
      proof -
        obtain i l where il: "x \<in> i" "i \<in> d" "(x, l) \<in> p" "K = i \<inter> l" 
          using xK unfolding p'_def by auto
        then show ?thesis
          using p'(2) by fastforce
      qed
      ultimately have p'alt: "p' = {(x, I \<inter> L) | x I L. (x,L) \<in> p \<and> I \<in> d \<and> I \<inter> L \<noteq> {}}"
        by auto
      have sum_p': "(\<Sum>(x,K) \<in> p'. norm (integral K f)) = (\<Sum>k\<in>snd ` p'. norm (integral k f))"
        apply (subst sum.over_tagged_division_lemma[OF p'',of "\<lambda>k. norm (integral k f)"])
         apply (auto intro: integral_null simp: content_eq_0_interior)
        done
      have snd_p_div: "snd ` p division_of cbox a b"
        by (rule division_of_tagged_division[OF p(1)])
      note snd_p = division_ofD[OF snd_p_div]
      have fin_d_sndp: "finite (d \<times> snd ` p)"
        by (simp add: d'(1) snd_p(1))

      have *: "\<And>sni sni' sf sf'. \<lbrakk>\<bar>sf' - sni'\<bar> < e/2; ?S - e/2 < sni; sni' \<le> ?S;
                       sni \<le> sni'; sf' = sf\<rbrakk> \<Longrightarrow> \<bar>sf - ?S\<bar> < e"
        by arith
      show "norm ((\<Sum>(x,k) \<in> p. content k *\<^sub>R norm (f x)) - ?S) < e"
        unfolding real_norm_def
      proof (rule *)
        show "\<bar>(\<Sum>(x,K)\<in>p'. norm (content K *\<^sub>R f x)) - (\<Sum>(x,k)\<in>p'. norm (integral k f))\<bar> < e/2"
          using p'' sum_less_e2 unfolding split_def by (force intro!: absdiff_norm_less)
        show "(\<Sum>(x,k) \<in> p'. norm (integral k f)) \<le>?S"
          by (auto simp: sum_p' division_of_tagged_division[OF p''] D intro!: cSUP_upper)
        show "(\<Sum>k\<in>d. norm (integral k f)) \<le> (\<Sum>(x,k) \<in> p'. norm (integral k f))"
        proof -
          have *: "{k \<inter> l | k l. k \<in> d \<and> l \<in> snd ` p} = (\<lambda>(k,l). k \<inter> l) ` (d \<times> snd ` p)"
            by auto
          have "(\<Sum>K\<in>d. norm (integral K f)) \<le> (\<Sum>i\<in>d. \<Sum>l\<in>snd ` p. norm (integral (i \<inter> l) f))"
          proof (rule sum_mono)
            fix K assume k: "K \<in> d"
            from d'(4)[OF this] obtain u v where uv: "K = cbox u v" by metis
            define d' where "d' = {cbox u v \<inter> l |l. l \<in> snd ` p \<and>  cbox u v \<inter> l \<noteq> {}}"
            have uvab: "cbox u v \<subseteq> cbox a b"
              using d(1) k uv by blast
            have "d' division_of cbox u v"
              unfolding d'_def by (rule division_inter_1 [OF snd_p_div uvab])
            moreover then have "norm (\<Sum>i\<in>d'. integral i f) \<le> (\<Sum>k\<in>d'. norm (integral k f))"
              by (simp add: sum_norm_le)
            ultimately have "norm (integral K f) \<le> sum (\<lambda>k. norm (integral k f)) d'"
              apply (subst integral_combine_division_topdown[of _ _ d'])
                apply (auto simp: uv intro: integrable_on_subcbox[OF assms(1) uvab])
              done
            also have "\<dots> = (\<Sum>I\<in>{K \<inter> L |L. L \<in> snd ` p}. norm (integral I f))"
            proof -
              have *: "norm (integral I f) = 0"
                if "I \<in> {cbox u v \<inter> l |l. l \<in> snd ` p}"
                  "I \<notin> {cbox u v \<inter> l |l. l \<in> snd ` p \<and> cbox u v \<inter> l \<noteq> {}}" for I
                using that by auto
              show ?thesis
                apply (rule sum.mono_neutral_left)
                  apply (simp add: snd_p(1))
                unfolding d'_def uv using * by auto 
            qed
            also have "\<dots> = (\<Sum>l\<in>snd ` p. norm (integral (K \<inter> l) f))"
            proof -
              have *: "norm (integral (K \<inter> l) f) = 0"
                if "l \<in> snd ` p" "y \<in> snd ` p" "l \<noteq> y" "K \<inter> l = K \<inter> y" for l y
              proof -
                have "interior (K \<inter> l) \<subseteq> interior (l \<inter> y)"
                  by (metis Int_lower2 interior_mono le_inf_iff that(4))
                then have "interior (K \<inter> l) = {}"
                  by (simp add: snd_p(5) that) 
                moreover from d'(4)[OF k] snd_p(4)[OF that(1)] 
                obtain u1 v1 u2 v2
                  where uv: "K = cbox u1 u2" "l = cbox v1 v2" by metis
                ultimately show ?thesis
                  using that integral_null
                  unfolding uv Int_interval content_eq_0_interior
                  by (metis (mono_tags, lifting) norm_eq_zero)
              qed
              show ?thesis
                unfolding Setcompr_eq_image
                apply (rule sum.reindex_nontrivial [unfolded o_def])
                 apply (rule finite_imageI)
                 apply (rule p')
                using * by auto
            qed
            finally show "norm (integral K f) \<le> (\<Sum>l\<in>snd ` p. norm (integral (K \<inter> l) f))" .
          qed
          also have "\<dots> = (\<Sum>(i,l) \<in> d \<times> snd ` p. norm (integral (i\<inter>l) f))"
            by (simp add: sum.cartesian_product)
          also have "\<dots> = (\<Sum>x \<in> d \<times> snd ` p. norm (integral (case_prod (\<inter>) x) f))"
            by (force simp: split_def intro!: sum.cong)
          also have "\<dots> = (\<Sum>k\<in>{i \<inter> l |i l. i \<in> d \<and> l \<in> snd ` p}. norm (integral k f))"
          proof -
            have eq0: " (integral (l1 \<inter> k1) f) = 0"
              if "l1 \<inter> k1 = l2 \<inter> k2" "(l1, k1) \<noteq> (l2, k2)"
                "l1 \<in> d" "(j1,k1) \<in> p" "l2 \<in> d" "(j2,k2) \<in> p"
              for l1 l2 k1 k2 j1 j2
            proof -
              obtain u1 v1 u2 v2 where uv: "l1 = cbox u1 u2" "k1 = cbox v1 v2"
                using \<open>(j1, k1) \<in> p\<close> \<open>l1 \<in> d\<close> d'(4) p'(4) by blast
              have "l1 \<noteq> l2 \<or> k1 \<noteq> k2"
                using that by auto
              then have "interior k1 \<inter> interior k2 = {} \<or> interior l1 \<inter> interior l2 = {}"
                by (meson d'(5) old.prod.inject p'(5) that(3) that(4) that(5) that(6))
              moreover have "interior (l1 \<inter> k1) = interior (l2 \<inter> k2)"
                by (simp add: that(1))
              ultimately have "interior(l1 \<inter> k1) = {}"
                by auto
              then show ?thesis
                unfolding uv Int_interval content_eq_0_interior[symmetric] by auto
            qed
            show ?thesis
              unfolding *
              apply (rule sum.reindex_nontrivial [OF fin_d_sndp, symmetric, unfolded o_def])
              apply clarsimp
              by (metis eq0 fst_conv snd_conv)
          qed
          also have "\<dots> = (\<Sum>(x,k) \<in> p'. norm (integral k f))"
          proof -
            have 0: "integral (ia \<inter> snd (a, b)) f = 0"
              if "ia \<inter> snd (a, b) \<notin> snd ` p'" "ia \<in> d" "(a, b) \<in> p" for ia a b
            proof -
              have "ia \<inter> b = {}"
                using that unfolding p'alt image_iff Bex_def not_ex
                apply (erule_tac x="(a, ia \<inter> b)" in allE)
                apply auto
                done
              then show ?thesis by auto
            qed
            have 1: "\<exists>i l. snd (a, b) = i \<inter> l \<and> i \<in> d \<and> l \<in> snd ` p" if "(a, b) \<in> p'" for a b
              using that 
              apply (clarsimp simp: p'_def image_iff)
              by (metis (no_types, hide_lams) snd_conv)
            show ?thesis
              unfolding sum_p'
              apply (rule sum.mono_neutral_right)
                apply (metis * finite_imageI[OF fin_d_sndp])
              using 0 1 by auto
          qed
          finally show ?thesis .
        qed
        show "(\<Sum>(x,k) \<in> p'. norm (content k *\<^sub>R f x)) = (\<Sum>(x,k) \<in> p. content k *\<^sub>R norm (f x))"
        proof -
          let ?S = "{(x, i \<inter> l) |x i l. (x, l) \<in> p \<and> i \<in> d}"
          have *: "?S = (\<lambda>(xl,i). (fst xl, snd xl \<inter> i)) ` (p \<times> d)"
            by force
          have fin_pd: "finite (p \<times> d)"
            using finite_cartesian_product[OF p'(1) d'(1)] by metis
          have "(\<Sum>(x,k) \<in> p'. norm (content k *\<^sub>R f x)) = (\<Sum>(x,k) \<in> ?S. \<bar>content k\<bar> * norm (f x))"
            unfolding norm_scaleR
            apply (rule sum.mono_neutral_left)
              apply (subst *)
              apply (rule finite_imageI [OF fin_pd])
            unfolding p'alt apply auto
            by fastforce
          also have "\<dots> = (\<Sum>((x,l),i)\<in>p \<times> d. \<bar>content (l \<inter> i)\<bar> * norm (f x))"
          proof -
            have "\<bar>content (l1 \<inter> k1)\<bar> * norm (f x1) = 0"
              if "(x1, l1) \<in> p" "(x2, l2) \<in> p" "k1 \<in> d" "k2 \<in> d"
                "x1 = x2" "l1 \<inter> k1 = l2 \<inter> k2" "x1 \<noteq> x2 \<or> l1 \<noteq> l2 \<or> k1 \<noteq> k2"
              for x1 l1 k1 x2 l2 k2
            proof -
              obtain u1 v1 u2 v2 where uv: "k1 = cbox u1 u2" "l1 = cbox v1 v2"
                by (meson \<open>(x1, l1) \<in> p\<close> \<open>k1 \<in> d\<close> d(1) division_ofD(4) p'(4))
              have "l1 \<noteq> l2 \<or> k1 \<noteq> k2"
                using that by auto
              then have "interior k1 \<inter> interior k2 = {} \<or> interior l1 \<inter> interior l2 = {}"
                apply (rule disjE)
                using that p'(5) d'(5) by auto
              moreover have "interior (l1 \<inter> k1) = interior (l2 \<inter> k2)"
                unfolding that ..
              ultimately have "interior (l1 \<inter> k1) = {}"
                by auto
              then show "\<bar>content (l1 \<inter> k1)\<bar> * norm (f x1) = 0"
                unfolding uv Int_interval content_eq_0_interior[symmetric] by auto
            qed 
            then show ?thesis
              unfolding *
              apply (subst sum.reindex_nontrivial [OF fin_pd])
              unfolding split_paired_all o_def split_def prod.inject
               apply force+
              done
          qed
          also have "\<dots> = (\<Sum>(x,k) \<in> p. content k *\<^sub>R norm (f x))"
          proof -
            have sumeq: "(\<Sum>i\<in>d. content (l \<inter> i) * norm (f x)) = content l * norm (f x)"
              if "(x, l) \<in> p" for x l
            proof -
              note xl = p'(2-4)[OF that]
              then obtain u v where uv: "l = cbox u v" by blast
              have "(\<Sum>i\<in>d. \<bar>content (l \<inter> i)\<bar>) = (\<Sum>k\<in>d. content (k \<inter> cbox u v))"
                by (simp add: Int_commute uv)
              also have "\<dots> = sum content {k \<inter> cbox u v| k. k \<in> d}"
              proof -
                have eq0: "content (k \<inter> cbox u v) = 0"
                  if "k \<in> d" "y \<in> d" "k \<noteq> y" and eq: "k \<inter> cbox u v = y \<inter> cbox u v" for k y
                proof -
                  from d'(4)[OF that(1)] d'(4)[OF that(2)]
                  obtain \<alpha> \<beta> where \<alpha>: "k \<inter> cbox u v = cbox \<alpha> \<beta>"
                    by (meson Int_interval)
                  have "{} = interior ((k \<inter> y) \<inter> cbox u v)"
                    by (simp add: d'(5) that)
                  also have "\<dots> = interior (y \<inter> (k \<inter> cbox u v))"
                    by auto
                  also have "\<dots> = interior (k \<inter> cbox u v)"
                    unfolding eq by auto
                  finally show ?thesis
                    unfolding \<alpha> content_eq_0_interior ..
                qed
                then show ?thesis
                  unfolding Setcompr_eq_image
                  apply (rule sum.reindex_nontrivial [OF \<open>finite d\<close>, unfolded o_def, symmetric])
                  by auto
              qed
              also have "\<dots> = sum content {cbox u v \<inter> k |k. k \<in> d \<and> cbox u v \<inter> k \<noteq> {}}"
                apply (rule sum.mono_neutral_right)
                unfolding Setcompr_eq_image
                  apply (rule finite_imageI [OF \<open>finite d\<close>])
                 apply (fastforce simp: inf.commute)+
                done
              finally show "(\<Sum>i\<in>d. content (l \<inter> i) * norm (f x)) = content l * norm (f x)"
                unfolding sum_distrib_right[symmetric] real_scaleR_def
                apply (subst(asm) additive_content_division[OF division_inter_1[OF d(1)]])
                using xl(2)[unfolded uv] unfolding uv apply auto
                done
            qed
            show ?thesis
              by (subst sum_Sigma_product[symmetric]) (auto intro!: sumeq sum.cong p' d')
          qed
          finally show ?thesis .
        qed
      qed (rule d)
    qed 
  qed
  then show ?thesis
    using absolutely_integrable_onI [OF f has_integral_integrable] has_integral[of _ ?S]
    by blast
qed


lemma bounded_variation_absolutely_integrable:
  fixes f :: "'n::euclidean_space \<Rightarrow> 'm::euclidean_space"
  assumes "f integrable_on UNIV"
    and "\<forall>d. d division_of (\<Union>d) \<longrightarrow> sum (\<lambda>k. norm (integral k f)) d \<le> B"
  shows "f absolutely_integrable_on UNIV"
proof (rule absolutely_integrable_onI, fact)
  let ?f = "\<lambda>d. \<Sum>k\<in>d. norm (integral k f)" and ?D = "{d. d division_of  (\<Union>d)}"
  have D_1: "?D \<noteq> {}"
    by (rule elementary_interval) auto
  have D_2: "bdd_above (?f`?D)"
    by (intro bdd_aboveI2[where M=B] assms(2)[rule_format]) simp
  note D = D_1 D_2
  let ?S = "SUP d:?D. ?f d"
  have "\<And>a b. f integrable_on cbox a b"
    using assms(1) integrable_on_subcbox by blast
  then have f_int: "\<And>a b. f absolutely_integrable_on cbox a b"
    apply (rule bounded_variation_absolutely_integrable_interval[where B=B])
    using assms(2) apply blast
    done
  have "((\<lambda>x. norm (f x)) has_integral ?S) UNIV"
    apply (subst has_integral_alt')
    apply safe
  proof goal_cases
    case (1 a b)
    show ?case
      using f_int[of a b] unfolding absolutely_integrable_on_def by auto
  next
    case prems: (2 e)
    have "\<exists>y\<in>sum (\<lambda>k. norm (integral k f)) ` {d. d division_of \<Union>d}. \<not> y \<le> ?S - e"
    proof (rule ccontr)
      assume "\<not> ?thesis"
      then have "?S \<le> ?S - e"
        by (intro cSUP_least[OF D(1)]) auto
      then show False
        using prems by auto
    qed
    then obtain d K where ddiv: "d division_of \<Union>d" and "K = (\<Sum>k\<in>d. norm (integral k f))"
      "SUPREMUM {d. d division_of \<Union>d} (sum (\<lambda>k. norm (integral k f))) - e < K"
      by (auto simp add: image_iff not_le)
    then have d: "SUPREMUM {d. d division_of \<Union>d} (sum (\<lambda>k. norm (integral k f))) - e 
                  < (\<Sum>k\<in>d. norm (integral k f))"
      by auto
    note d'=division_ofD[OF ddiv]
    have "bounded (\<Union>d)"
      by (rule elementary_bounded,fact)
    from this[unfolded bounded_pos] obtain K where
       K: "0 < K" "\<forall>x\<in>\<Union>d. norm x \<le> K" by auto
    show ?case
    proof (intro conjI impI allI exI)
      fix a b :: 'n
      assume ab: "ball 0 (K + 1) \<subseteq> cbox a b"
      have *: "\<And>s s1. \<lbrakk>?S - e < s1; s1 \<le> s; s < ?S + e\<rbrakk> \<Longrightarrow> \<bar>s - ?S\<bar> < e"
        by arith
      show "norm (integral (cbox a b) (\<lambda>x. if x \<in> UNIV then norm (f x) else 0) - ?S) < e"
        unfolding real_norm_def
      proof (rule * [OF d])
        have "(\<Sum>k\<in>d. norm (integral k f)) \<le> sum (\<lambda>k. integral k (\<lambda>x. norm (f x))) d"
        proof (intro sum_mono)
          fix k assume "k \<in> d"
          with d'(4) f_int show "norm (integral k f) \<le> integral k (\<lambda>x. norm (f x))"
            by (force simp: absolutely_integrable_on_def integral_norm_bound_integral)
        qed
        also have "\<dots> = integral (\<Union>d) (\<lambda>x. norm (f x))"
          apply (rule integral_combine_division_bottomup[OF ddiv, symmetric])
          using absolutely_integrable_on_def d'(4) f_int by blast
        also have "\<dots> \<le> integral (cbox a b) (\<lambda>x. if x \<in> UNIV then norm (f x) else 0)"
        proof -
          have "\<Union>d \<subseteq> cbox a b"
            using K(2) ab by fastforce
          then show ?thesis
            using integrable_on_subdivision[OF ddiv] f_int[of a b] unfolding absolutely_integrable_on_def
            by (auto intro!: integral_subset_le)
        qed
        finally show "(\<Sum>k\<in>d. norm (integral k f))
                      \<le> integral (cbox a b) (\<lambda>x. if x \<in> UNIV then norm (f x) else 0)" .
      next
        have "e/2>0"
          using \<open>e > 0\<close> by auto
        moreover
        have f: "f integrable_on cbox a b" "(\<lambda>x. norm (f x)) integrable_on cbox a b"
          using f_int by (auto simp: absolutely_integrable_on_def)
        ultimately obtain d1 where "gauge d1"
           and d1: "\<And>p. \<lbrakk>p tagged_division_of (cbox a b); d1 fine p\<rbrakk> \<Longrightarrow>
            norm ((\<Sum>(x,k) \<in> p. content k *\<^sub>R norm (f x)) - integral (cbox a b) (\<lambda>x. norm (f x))) < e/2"
          unfolding has_integral_integral has_integral by meson
        obtain d2 where "gauge d2" 
          and d2: "\<And>p. \<lbrakk>p tagged_partial_division_of (cbox a b); d2 fine p\<rbrakk> \<Longrightarrow>
            (\<Sum>(x,k) \<in> p. norm (content k *\<^sub>R f x - integral k f)) < e/2"
          by (blast intro: Henstock_lemma [OF f(1) \<open>e/2>0\<close>])
        obtain p where
          p: "p tagged_division_of (cbox a b)" "d1 fine p" "d2 fine p"
          by (rule fine_division_exists [OF gauge_Int [OF \<open>gauge d1\<close> \<open>gauge d2\<close>], of a b])
            (auto simp add: fine_Int)
        have *: "\<And>sf sf' si di. \<lbrakk>sf' = sf; si \<le> ?S; \<bar>sf - si\<bar> < e/2;
                      \<bar>sf' - di\<bar> < e/2\<rbrakk> \<Longrightarrow> di < ?S + e"
          by arith
        have "integral (cbox a b) (\<lambda>x. norm (f x)) < ?S + e"
        proof (rule *)
          show "\<bar>(\<Sum>(x,k)\<in>p. norm (content k *\<^sub>R f x)) - (\<Sum>(x,k)\<in>p. norm (integral k f))\<bar> < e/2"
            unfolding split_def
            apply (rule absdiff_norm_less)
            using d2[of p] p(1,3) apply (auto simp: tagged_division_of_def split_def)
            done
          show "\<bar>(\<Sum>(x,k) \<in> p. content k *\<^sub>R norm (f x)) - integral (cbox a b) (\<lambda>x. norm(f x))\<bar> < e/2"
            using d1[OF p(1,2)] by (simp only: real_norm_def)
          show "(\<Sum>(x,k) \<in> p. content k *\<^sub>R norm (f x)) = (\<Sum>(x,k) \<in> p. norm (content k *\<^sub>R f x))"
            by (auto simp: split_paired_all sum.cong [OF refl])
          show "(\<Sum>(x,k) \<in> p. norm (integral k f)) \<le> ?S"
            using partial_division_of_tagged_division[of p "cbox a b"] p(1)
            apply (subst sum.over_tagged_division_lemma[OF p(1)])
            apply (auto simp: content_eq_0_interior tagged_partial_division_of_def intro!: cSUP_upper2 D)
            done
        qed
        then show "integral (cbox a b) (\<lambda>x. if x \<in> UNIV then norm (f x) else 0) < ?S + e"
          by simp
      qed
    qed (insert K, auto)
  qed
  then show "(\<lambda>x. norm (f x)) integrable_on UNIV"
    by blast
qed


subsection\<open>Outer and inner approximation of measurable sets by well-behaved sets.\<close>

proposition measurable_outer_intervals_bounded:
  assumes "S \<in> lmeasurable" "S \<subseteq> cbox a b" "e > 0"
  obtains \<D>
  where "countable \<D>"
        "\<And>K. K \<in> \<D> \<Longrightarrow> K \<subseteq> cbox a b \<and> K \<noteq> {} \<and> (\<exists>c d. K = cbox c d)"
        "pairwise (\<lambda>A B. interior A \<inter> interior B = {}) \<D>"
        "\<And>u v. cbox u v \<in> \<D> \<Longrightarrow> \<exists>n. \<forall>i \<in> Basis. v \<bullet> i - u \<bullet> i = (b \<bullet> i - a \<bullet> i)/2^n"
        "\<And>K. \<lbrakk>K \<in> \<D>; box a b \<noteq> {}\<rbrakk> \<Longrightarrow> interior K \<noteq> {}"
        "S \<subseteq> \<Union>\<D>" "\<Union>\<D> \<in> lmeasurable" "measure lebesgue (\<Union>\<D>) \<le> measure lebesgue S + e"
proof (cases "box a b = {}")
  case True
  show ?thesis
  proof (cases "cbox a b = {}")
    case True
    with assms have [simp]: "S = {}"
      by auto
    show ?thesis
    proof
      show "countable {}"
        by simp
    qed (use \<open>e > 0\<close> in auto)
  next
    case False
    show ?thesis
    proof
      show "countable {cbox a b}"
        by simp
      show "\<And>u v. cbox u v \<in> {cbox a b} \<Longrightarrow> \<exists>n. \<forall>i\<in>Basis. v \<bullet> i - u \<bullet> i = (b \<bullet> i - a \<bullet> i)/2 ^ n"
        using False by (force simp: eq_cbox intro: exI [where x=0])
      show "measure lebesgue (\<Union>{cbox a b}) \<le> measure lebesgue S + e"
        using assms by (simp add: sum_content.box_empty_imp [OF True])
    qed (use assms \<open>cbox a b \<noteq> {}\<close> in auto)
  qed
next
  case False
  let ?\<mu> = "measure lebesgue"
  have "S \<inter> cbox a b \<in> lmeasurable"
    using \<open>S \<in> lmeasurable\<close> by blast
  then have indS_int: "(indicator S has_integral (?\<mu> S)) (cbox a b)"
    by (metis integral_indicator \<open>S \<subseteq> cbox a b\<close> has_integral_integrable_integral inf.orderE integrable_on_indicator)
  with \<open>e > 0\<close> obtain \<gamma> where "gauge \<gamma>" and \<gamma>:
    "\<And>\<D>. \<lbrakk>\<D> tagged_division_of (cbox a b); \<gamma> fine \<D>\<rbrakk> \<Longrightarrow> norm ((\<Sum>(x,K)\<in>\<D>. content(K) *\<^sub>R indicator S x) - ?\<mu> S) < e"
    by (force simp: has_integral)
  have inteq: "integral (cbox a b) (indicat_real S) = integral UNIV (indicator S)"
    using assms by (metis has_integral_iff indS_int lmeasure_integral_UNIV)
  obtain \<D> where \<D>: "countable \<D>"  "\<Union>\<D> \<subseteq> cbox a b"
            and cbox: "\<And>K. K \<in> \<D> \<Longrightarrow> interior K \<noteq> {} \<and> (\<exists>c d. K = cbox c d)"
            and djointish: "pairwise (\<lambda>A B. interior A \<inter> interior B = {}) \<D>"
            and covered: "\<And>K. K \<in> \<D> \<Longrightarrow> \<exists>x \<in> S \<inter> K. K \<subseteq> \<gamma> x"
            and close: "\<And>u v. cbox u v \<in> \<D> \<Longrightarrow> \<exists>n. \<forall>i \<in> Basis. v\<bullet>i - u\<bullet>i = (b\<bullet>i - a\<bullet>i)/2^n"
            and covers: "S \<subseteq> \<Union>\<D>"
    using covering_lemma [of S a b \<gamma>] \<open>gauge \<gamma>\<close> \<open>box a b \<noteq> {}\<close> assms by force
  show ?thesis
  proof
    show "\<And>K. K \<in> \<D> \<Longrightarrow> K \<subseteq> cbox a b \<and> K \<noteq> {} \<and> (\<exists>c d. K = cbox c d)"
      by (meson Sup_le_iff \<D>(2) cbox interior_empty)
    have negl_int: "negligible(K \<inter> L)" if "K \<in> \<D>" "L \<in> \<D>" "K \<noteq> L" for K L
    proof -
      have "interior K \<inter> interior L = {}"
        using djointish pairwiseD that by fastforce
      moreover obtain u v x y where "K = cbox u v" "L = cbox x y"
        using cbox \<open>K \<in> \<D>\<close> \<open>L \<in> \<D>\<close> by blast
      ultimately show ?thesis
        by (simp add: Int_interval box_Int_box negligible_interval(1))
    qed
    have fincase: "\<Union>\<F> \<in> lmeasurable \<and> ?\<mu> (\<Union>\<F>) \<le> ?\<mu> S + e" if "finite \<F>" "\<F> \<subseteq> \<D>" for \<F>
    proof -
      obtain t where t: "\<And>K. K \<in> \<F> \<Longrightarrow> t K \<in> S \<inter> K \<and> K \<subseteq> \<gamma>(t K)"
        using covered \<open>\<F> \<subseteq> \<D>\<close> subsetD by metis
      have "\<forall>K \<in> \<F>. \<forall>L \<in> \<F>. K \<noteq> L \<longrightarrow> interior K \<inter> interior L = {}"
        using that djointish by (simp add: pairwise_def) (metis subsetD)
      with cbox that \<D> have \<F>div: "\<F> division_of (\<Union>\<F>)"
        by (fastforce simp: division_of_def dest: cbox)
      then have 1: "\<Union>\<F> \<in> lmeasurable"
        by blast
      have norme: "\<And>p. \<lbrakk>p tagged_division_of cbox a b; \<gamma> fine p\<rbrakk>
          \<Longrightarrow> norm ((\<Sum>(x,K)\<in>p. content K * indicator S x) - integral (cbox a b) (indicator S)) < e"
        by (auto simp: lmeasure_integral_UNIV assms inteq dest: \<gamma>)
      have "\<forall>x K y L. (x,K) \<in> (\<lambda>K. (t K,K)) ` \<F> \<and> (y,L) \<in> (\<lambda>K. (t K,K)) ` \<F> \<and> (x,K) \<noteq> (y,L) \<longrightarrow>             interior K \<inter> interior L = {}"
        using that djointish  by (clarsimp simp: pairwise_def) (metis subsetD)
      with that \<D> have tagged: "(\<lambda>K. (t K, K)) ` \<F> tagged_partial_division_of cbox a b"
        by (auto simp: tagged_partial_division_of_def dest: t cbox)
      have fine: "\<gamma> fine (\<lambda>K. (t K, K)) ` \<F>"
        using t by (auto simp: fine_def)
      have *: "y \<le> ?\<mu> S \<Longrightarrow> \<bar>x - y\<bar> \<le> e \<Longrightarrow> x \<le> ?\<mu> S + e" for x y
        by arith
      have "?\<mu> (\<Union>\<F>) \<le> ?\<mu> S + e"
      proof (rule *)
        have "(\<Sum>K\<in>\<F>. ?\<mu> (K \<inter> S)) = ?\<mu> (\<Union>C\<in>\<F>. C \<inter> S)"
          apply (rule measure_negligible_finite_Union_image [OF \<open>finite \<F>\<close>, symmetric])
          using \<F>div \<open>S \<in> lmeasurable\<close> apply blast
          unfolding pairwise_def
          by (metis inf.commute inf_sup_aci(3) negligible_Int subsetCE negl_int \<open>\<F> \<subseteq> \<D>\<close>)
        also have "\<dots> = ?\<mu> (\<Union>\<F> \<inter> S)"
          by simp
        also have "\<dots> \<le> ?\<mu> S"
          by (simp add: "1" \<open>S \<in> lmeasurable\<close> fmeasurableD measure_mono_fmeasurable sets.Int)
        finally show "(\<Sum>K\<in>\<F>. ?\<mu> (K \<inter> S)) \<le> ?\<mu> S" .
      next
        have "?\<mu> (\<Union>\<F>) = sum ?\<mu> \<F>"
          by (metis \<F>div content_division)
        also have "\<dots> = (\<Sum>K\<in>\<F>. content K)"
          using \<F>div by (force intro: sum.cong)
        also have "\<dots> = (\<Sum>x\<in>\<F>. content x * indicator S (t x))"
          using t by auto
        finally have eq1: "?\<mu> (\<Union>\<F>) = (\<Sum>x\<in>\<F>. content x * indicator S (t x))" .
        have eq2: "(\<Sum>K\<in>\<F>. ?\<mu> (K \<inter> S)) = (\<Sum>K\<in>\<F>. integral K (indicator S))"
          apply (rule sum.cong [OF refl])
          by (metis integral_indicator \<F>div \<open>S \<in> lmeasurable\<close> division_ofD(4) fmeasurable.Int inf.commute lmeasurable_cbox)
        have "\<bar>\<Sum>(x,K)\<in>(\<lambda>K. (t K, K)) ` \<F>. content K * indicator S x - integral K (indicator S)\<bar> \<le> e"
          using Henstock_lemma_part1 [of "indicator S::'a\<Rightarrow>real", OF _ \<open>e > 0\<close> \<open>gauge \<gamma>\<close> _ tagged fine]
            indS_int norme by auto
        then show "\<bar>?\<mu> (\<Union>\<F>) - (\<Sum>K\<in>\<F>. ?\<mu> (K \<inter> S))\<bar> \<le> e"
          by (simp add: eq1 eq2 comm_monoid_add_class.sum.reindex inj_on_def sum_subtractf)
      qed
      with 1 show ?thesis by blast
    qed
    have "\<Union>\<D> \<in> lmeasurable \<and> ?\<mu> (\<Union>\<D>) \<le> ?\<mu> S + e"
    proof (cases "finite \<D>")
      case True
      with fincase show ?thesis
        by blast
    next
      case False
      let ?T = "from_nat_into \<D>"
      have T: "bij_betw ?T UNIV \<D>"
        by (simp add: False \<D>(1) bij_betw_from_nat_into)
      have TM: "\<And>n. ?T n \<in> lmeasurable"
        by (metis False cbox finite.emptyI from_nat_into lmeasurable_cbox)
      have TN: "\<And>m n. m \<noteq> n \<Longrightarrow> negligible (?T m \<inter> ?T n)"
        by (simp add: False \<D>(1) from_nat_into infinite_imp_nonempty negl_int)
      have TB: "(\<Sum>k\<le>n. ?\<mu> (?T k)) \<le> ?\<mu> S + e" for n
      proof -
        have "(\<Sum>k\<le>n. ?\<mu> (?T k)) = ?\<mu> (UNION {..n} ?T)"
          by (simp add: pairwise_def TM TN measure_negligible_finite_Union_image)
        also have "?\<mu> (UNION {..n} ?T) \<le> ?\<mu> S + e"
          using fincase [of "?T ` {..n}"] T by (auto simp: bij_betw_def)
        finally show ?thesis .
      qed
      have "\<Union>\<D> \<in> lmeasurable"
        by (metis lmeasurable_compact T \<D>(2) bij_betw_def cbox compact_cbox countable_Un_Int(1) fmeasurableD fmeasurableI2 rangeI)
      moreover
      have "?\<mu> (\<Union>x. from_nat_into \<D> x) \<le> ?\<mu> S + e"
      proof (rule measure_countable_Union_le [OF TM])
        show "?\<mu> (\<Union>x\<le>n. from_nat_into \<D> x) \<le> ?\<mu> S + e" for n
          by (metis (mono_tags, lifting) False fincase finite.emptyI finite_atMost finite_imageI from_nat_into imageE subsetI)
      qed
      ultimately show ?thesis by (metis T bij_betw_def)
    qed
    then show "\<Union>\<D> \<in> lmeasurable" "measure lebesgue (\<Union>\<D>) \<le> ?\<mu> S + e" by blast+
  qed (use \<D> cbox djointish close covers in auto)
qed


subsection\<open>Transformation of measure by linear maps\<close>

lemma measurable_linear_image_interval:
   "linear f \<Longrightarrow> f ` (cbox a b) \<in> lmeasurable"
  by (metis bounded_linear_image linear_linear bounded_cbox closure_bounded_linear_image closure_cbox compact_closure lmeasurable_compact)

proposition measure_linear_sufficient:
  fixes f :: "'n::euclidean_space \<Rightarrow> 'n"
  assumes "linear f" and S: "S \<in> lmeasurable"
    and im: "\<And>a b. measure lebesgue (f ` (cbox a b)) = m * measure lebesgue (cbox a b)"
  shows "f ` S \<in> lmeasurable \<and> m * measure lebesgue S = measure lebesgue (f ` S)"
  using le_less_linear [of 0 m]
proof
  assume "m < 0"
  then show ?thesis
    using im [of 0 One] by auto
next
  assume "m \<ge> 0"
  let ?\<mu> = "measure lebesgue"
  show ?thesis
  proof (cases "inj f")
    case False
    then have "?\<mu> (f ` S) = 0"
      using \<open>linear f\<close> negligible_imp_measure0 negligible_linear_singular_image by blast
    then have "m * ?\<mu> (cbox 0 (One)) = 0"
      by (metis False \<open>linear f\<close> cbox_borel content_unit im measure_completion negligible_imp_measure0 negligible_linear_singular_image sets_lborel)
    then show ?thesis
      using \<open>linear f\<close> negligible_linear_singular_image negligible_imp_measure0 False
      by (auto simp: lmeasurable_iff_has_integral negligible_UNIV)
  next
    case True
    then obtain h where "linear h" and hf: "\<And>x. h (f x) = x" and fh: "\<And>x. f (h x) = x"
      using \<open>linear f\<close> linear_injective_isomorphism by blast
    have fBS: "(f ` S) \<in> lmeasurable \<and> m * ?\<mu> S = ?\<mu> (f ` S)"
      if "bounded S" "S \<in> lmeasurable" for S
    proof -
      obtain a b where "S \<subseteq> cbox a b"
        using \<open>bounded S\<close> bounded_subset_cbox_symmetric by metis
      have fUD: "(f ` \<Union>\<D>) \<in> lmeasurable \<and> ?\<mu> (f ` \<Union>\<D>) = (m * ?\<mu> (\<Union>\<D>))"
        if "countable \<D>"
          and cbox: "\<And>K. K \<in> \<D> \<Longrightarrow> K \<subseteq> cbox a b \<and> K \<noteq> {} \<and> (\<exists>c d. K = cbox c d)"
          and intint: "pairwise (\<lambda>A B. interior A \<inter> interior B = {}) \<D>"
        for \<D>
      proof -
        have conv: "\<And>K. K \<in> \<D> \<Longrightarrow> convex K"
          using cbox convex_box(1) by blast
        have neg: "negligible (g ` K \<inter> g ` L)" if "linear g" "K \<in> \<D>" "L \<in> \<D>" "K \<noteq> L"
          for K L and g :: "'n\<Rightarrow>'n"
        proof (cases "inj g")
          case True
          have "negligible (frontier(g ` K \<inter> g ` L) \<union> interior(g ` K \<inter> g ` L))"
          proof (rule negligible_Un)
            show "negligible (frontier (g ` K \<inter> g ` L))"
              by (simp add: negligible_convex_frontier convex_Int conv convex_linear_image that)
          next
            have "\<forall>p N. pairwise p N = (\<forall>Na. (Na::'n set) \<in> N \<longrightarrow> (\<forall>Nb. Nb \<in> N \<and> Na \<noteq> Nb \<longrightarrow> p Na Nb))"
              by (metis pairwise_def)
            then have "interior K \<inter> interior L = {}"
              using intint that(2) that(3) that(4) by presburger
            then show "negligible (interior (g ` K \<inter> g ` L))"
              by (metis True empty_imp_negligible image_Int image_empty interior_Int interior_injective_linear_image that(1))
          qed
          moreover have "g ` K \<inter> g ` L \<subseteq> frontier (g ` K \<inter> g ` L) \<union> interior (g ` K \<inter> g ` L)"
            apply (auto simp: frontier_def)
            using closure_subset contra_subsetD by fastforce+
          ultimately show ?thesis
            by (rule negligible_subset)
        next
          case False
          then show ?thesis
            by (simp add: negligible_Int negligible_linear_singular_image \<open>linear g\<close>)
        qed
        have negf: "negligible ((f ` K) \<inter> (f ` L))"
        and negid: "negligible (K \<inter> L)" if "K \<in> \<D>" "L \<in> \<D>" "K \<noteq> L" for K L
          using neg [OF \<open>linear f\<close>] neg [OF linear_id] that by auto
        show ?thesis
        proof (cases "finite \<D>")
          case True
          then have "?\<mu> (\<Union>x\<in>\<D>. f ` x) = (\<Sum>x\<in>\<D>. ?\<mu> (f ` x))"
            using \<open>linear f\<close> cbox measurable_linear_image_interval negf
            by (blast intro: measure_negligible_finite_Union_image [unfolded pairwise_def])
          also have "\<dots> = (\<Sum>k\<in>\<D>. m * ?\<mu> k)"
            by (metis (no_types, lifting) cbox im sum.cong)
          also have "\<dots> = m * ?\<mu> (\<Union>\<D>)"
            unfolding sum_distrib_left [symmetric]
            by (metis True cbox lmeasurable_cbox measure_negligible_finite_Union [unfolded pairwise_def] negid)
          finally show ?thesis
            by (metis True \<open>linear f\<close> cbox image_Union fmeasurable.finite_UN measurable_linear_image_interval)
        next
          case False
          with \<open>countable \<D>\<close> obtain X :: "nat \<Rightarrow> 'n set" where S: "bij_betw X UNIV \<D>"
            using bij_betw_from_nat_into by blast
          then have eq: "(\<Union>\<D>) = (\<Union>n. X n)" "(f ` \<Union>\<D>) = (\<Union>n. f ` X n)"
            by (auto simp: bij_betw_def)
          have meas: "\<And>K. K \<in> \<D> \<Longrightarrow> K \<in> lmeasurable"
            using cbox by blast
          with S have 1: "\<And>n. X n \<in> lmeasurable"
            by (auto simp: bij_betw_def)
          have 2: "pairwise (\<lambda>m n. negligible (X m \<inter> X n)) UNIV"
            using S unfolding bij_betw_def pairwise_def by (metis injD negid range_eqI)
          have "bounded (\<Union>\<D>)"
            by (meson Sup_least bounded_cbox bounded_subset cbox)
          then have 3: "bounded (\<Union>n. X n)"
            using S unfolding bij_betw_def by blast
          have "(\<Union>n. X n) \<in> lmeasurable"
            by (rule measurable_countable_negligible_Union_bounded [OF 1 2 3])
          with S have f1: "\<And>n. f ` (X n) \<in> lmeasurable"
            unfolding bij_betw_def by (metis assms(1) cbox measurable_linear_image_interval rangeI)
          have f2: "pairwise (\<lambda>m n. negligible (f ` (X m) \<inter> f ` (X n))) UNIV"
            using S unfolding bij_betw_def pairwise_def by (metis injD negf rangeI)
          have "bounded (\<Union>\<D>)"
            by (meson Sup_least bounded_cbox bounded_subset cbox)
          then have f3: "bounded (\<Union>n. f ` X n)"
            using S unfolding bij_betw_def
            by (metis bounded_linear_image linear_linear assms(1) image_Union range_composition)
          have "(\<lambda>n. ?\<mu> (X n)) sums ?\<mu> (\<Union>n. X n)"
            by (rule measure_countable_negligible_Union_bounded [OF 1 2 3])
          have meq: "?\<mu> (\<Union>n. f ` X n) = m * ?\<mu> (UNION UNIV X)"
          proof (rule sums_unique2 [OF measure_countable_negligible_Union_bounded [OF f1 f2 f3]])
            have m: "\<And>n. ?\<mu> (f ` X n) = (m * ?\<mu> (X n))"
              using S unfolding bij_betw_def by (metis cbox im rangeI)
            show "(\<lambda>n. ?\<mu> (f ` X n)) sums (m * ?\<mu> (UNION UNIV X))"
              unfolding m
              using measure_countable_negligible_Union_bounded [OF 1 2 3] sums_mult by blast
          qed
          show ?thesis
            using measurable_countable_negligible_Union_bounded [OF f1 f2 f3] meq
            by (auto simp: eq [symmetric])
        qed
      qed
      show ?thesis
        unfolding completion.fmeasurable_measure_inner_outer_le
      proof (intro conjI allI impI)
        fix e :: real
        assume "e > 0"
        have 1: "cbox a b - S \<in> lmeasurable"
          by (simp add: fmeasurable.Diff that)
        have 2: "0 < e / (1 + \<bar>m\<bar>)"
          using \<open>e > 0\<close> by (simp add: divide_simps abs_add_one_gt_zero)
        obtain \<D>
          where "countable \<D>"
            and cbox: "\<And>K. K \<in> \<D> \<Longrightarrow> K \<subseteq> cbox a b \<and> K \<noteq> {} \<and> (\<exists>c d. K = cbox c d)"
            and intdisj: "pairwise (\<lambda>A B. interior A \<inter> interior B = {}) \<D>"
            and DD: "cbox a b - S \<subseteq> \<Union>\<D>" "\<Union>\<D> \<in> lmeasurable"
            and le: "?\<mu> (\<Union>\<D>) \<le> ?\<mu> (cbox a b - S) + e/(1 + \<bar>m\<bar>)"
          by (rule measurable_outer_intervals_bounded [of "cbox a b - S" a b "e/(1 + \<bar>m\<bar>)"]; use 1 2 pairwise_def in force)
        have meq: "?\<mu> (cbox a b - S) = ?\<mu> (cbox a b) - ?\<mu> S"
          by (simp add: measurable_measure_Diff \<open>S \<subseteq> cbox a b\<close> fmeasurableD that(2))
        show "\<exists>T \<in> lmeasurable. T \<subseteq> f ` S \<and> m * ?\<mu> S - e \<le> ?\<mu> T"
        proof (intro bexI conjI)
          show "f ` (cbox a b) - f ` (\<Union>\<D>) \<subseteq> f ` S"
            using \<open>cbox a b - S \<subseteq> \<Union>\<D>\<close> by force
          have "m * ?\<mu> S - e \<le> m * (?\<mu> S - e / (1 + \<bar>m\<bar>))"
            using \<open>m \<ge> 0\<close> \<open>e > 0\<close> by (simp add: field_simps)
          also have "\<dots> \<le> ?\<mu> (f ` cbox a b) - ?\<mu> (f ` (\<Union>\<D>))"
            using le \<open>m \<ge> 0\<close> \<open>e > 0\<close>
            apply (simp add: im fUD [OF \<open>countable \<D>\<close> cbox intdisj] right_diff_distrib [symmetric])
            apply (rule mult_left_mono; simp add: algebra_simps meq)
            done
          also have "\<dots> = ?\<mu> (f ` cbox a b - f ` \<Union>\<D>)"
            apply (rule measurable_measure_Diff [symmetric])
            apply (simp add: assms(1) measurable_linear_image_interval)
            apply (simp add: \<open>countable \<D>\<close> cbox fUD fmeasurableD intdisj)
             apply (simp add: Sup_le_iff cbox image_mono)
            done
          finally show "m * ?\<mu> S - e \<le> ?\<mu> (f ` cbox a b - f ` \<Union>\<D>)" .
          show "f ` cbox a b - f ` \<Union>\<D> \<in> lmeasurable"
            by (simp add: fUD \<open>countable \<D>\<close> \<open>linear f\<close> cbox fmeasurable.Diff intdisj measurable_linear_image_interval)
        qed
      next
        fix e :: real
        assume "e > 0"
        have em: "0 < e / (1 + \<bar>m\<bar>)"
          using \<open>e > 0\<close> by (simp add: divide_simps abs_add_one_gt_zero)
        obtain \<D>
          where "countable \<D>"
            and cbox: "\<And>K. K \<in> \<D> \<Longrightarrow> K \<subseteq> cbox a b \<and> K \<noteq> {} \<and> (\<exists>c d. K = cbox c d)"
            and intdisj: "pairwise (\<lambda>A B. interior A \<inter> interior B = {}) \<D>"
            and DD: "S \<subseteq> \<Union>\<D>" "\<Union>\<D> \<in> lmeasurable"
            and le: "?\<mu> (\<Union>\<D>) \<le> ?\<mu> S + e/(1 + \<bar>m\<bar>)"
          by (rule measurable_outer_intervals_bounded [of S a b "e/(1 + \<bar>m\<bar>)"]; use \<open>S \<in> lmeasurable\<close> \<open>S \<subseteq> cbox a b\<close> em in force)
        show "\<exists>U \<in> lmeasurable. f ` S \<subseteq> U \<and> ?\<mu> U \<le> m * ?\<mu> S + e"
        proof (intro bexI conjI)
          show "f ` S \<subseteq> f ` (\<Union>\<D>)"
            by (simp add: DD(1) image_mono)
          have "?\<mu> (f ` \<Union>\<D>) \<le> m * (?\<mu> S + e / (1 + \<bar>m\<bar>))"
            using \<open>m \<ge> 0\<close> le mult_left_mono
            by (auto simp: fUD \<open>countable \<D>\<close> \<open>linear f\<close> cbox fmeasurable.Diff intdisj measurable_linear_image_interval)
          also have "\<dots> \<le> m * ?\<mu> S + e"
            using \<open>m \<ge> 0\<close> \<open>e > 0\<close> by (simp add: fUD [OF \<open>countable \<D>\<close> cbox intdisj] field_simps)
          finally show "?\<mu> (f ` \<Union>\<D>) \<le> m * ?\<mu> S + e" .
          show "f ` \<Union>\<D> \<in> lmeasurable"
            by (simp add: \<open>countable \<D>\<close> cbox fUD intdisj)
        qed
      qed
    qed
    show ?thesis
      unfolding has_measure_limit_iff
    proof (intro allI impI)
      fix e :: real
      assume "e > 0"
      obtain B where "B > 0" and B:
        "\<And>a b. ball 0 B \<subseteq> cbox a b \<Longrightarrow> \<bar>?\<mu> (S \<inter> cbox a b) - ?\<mu> S\<bar> < e / (1 + \<bar>m\<bar>)"
        using has_measure_limit [OF S] \<open>e > 0\<close> by (metis abs_add_one_gt_zero zero_less_divide_iff)
      obtain c d::'n where cd: "ball 0 B \<subseteq> cbox c d"
        by (metis bounded_subset_cbox_symmetric bounded_ball)
      with B have less: "\<bar>?\<mu> (S \<inter> cbox c d) - ?\<mu> S\<bar> < e / (1 + \<bar>m\<bar>)" .
      obtain D where "D > 0" and D: "cbox c d \<subseteq> ball 0 D"
        by (metis bounded_cbox bounded_subset_ballD)
      obtain C where "C > 0" and C: "\<And>x. norm (f x) \<le> C * norm x"
        using linear_bounded_pos \<open>linear f\<close> by blast
      have "f ` S \<inter> cbox a b \<in> lmeasurable \<and>
            \<bar>?\<mu> (f ` S \<inter> cbox a b) - m * ?\<mu> S\<bar> < e"
        if "ball 0 (D*C) \<subseteq> cbox a b" for a b
      proof -
        have "bounded (S \<inter> h ` cbox a b)"
          by (simp add: bounded_linear_image linear_linear \<open>linear h\<close> bounded_Int)
        moreover have Shab: "S \<inter> h ` cbox a b \<in> lmeasurable"
          by (simp add: S \<open>linear h\<close> fmeasurable.Int measurable_linear_image_interval)
        moreover have fim: "f ` (S \<inter> h ` (cbox a b)) = (f ` S) \<inter> cbox a b"
          by (auto simp: hf rev_image_eqI fh)
        ultimately have 1: "(f ` S) \<inter> cbox a b \<in> lmeasurable"
              and 2: "m * ?\<mu> (S \<inter> h ` cbox a b) = ?\<mu> ((f ` S) \<inter> cbox a b)"
          using fBS [of "S \<inter> (h ` (cbox a b))"] by auto
        have *: "\<lbrakk>\<bar>z - m\<bar> < e; z \<le> w; w \<le> m\<rbrakk> \<Longrightarrow> \<bar>w - m\<bar> \<le> e"
          for w z m and e::real by auto
        have meas_adiff: "\<bar>?\<mu> (S \<inter> h ` cbox a b) - ?\<mu> S\<bar> \<le> e / (1 + \<bar>m\<bar>)"
        proof (rule * [OF less])
          show "?\<mu> (S \<inter> cbox c d) \<le> ?\<mu> (S \<inter> h ` cbox a b)"
          proof (rule measure_mono_fmeasurable [OF _ _ Shab])
            have "f ` ball 0 D \<subseteq> ball 0 (C * D)"
              using C \<open>C > 0\<close>
              apply (clarsimp simp: algebra_simps)
              by (meson le_less_trans linordered_comm_semiring_strict_class.comm_mult_strict_left_mono)
            then have "f ` ball 0 D \<subseteq> cbox a b"
              by (metis mult.commute order_trans that)
            have "ball 0 D \<subseteq> h ` cbox a b"
              by (metis \<open>f ` ball 0 D \<subseteq> cbox a b\<close> hf image_subset_iff subsetI)
            then show "S \<inter> cbox c d \<subseteq> S \<inter> h ` cbox a b"
              using D by blast
          next
            show "S \<inter> cbox c d \<in> sets lebesgue"
              using S fmeasurable_cbox by blast
          qed
        next
          show "?\<mu> (S \<inter> h ` cbox a b) \<le> ?\<mu> S"
            by (simp add: S Shab fmeasurableD measure_mono_fmeasurable)
        qed
        have "\<bar>?\<mu> (f ` S \<inter> cbox a b) - m * ?\<mu> S\<bar> \<le> m * e / (1 + \<bar>m\<bar>)"
        proof -
          have mm: "\<bar>m\<bar> = m"
            by (simp add: \<open>0 \<le> m\<close>)
          then have "\<bar>?\<mu> S - ?\<mu> (S \<inter> h ` cbox a b)\<bar> * m \<le> e / (1 + m) * m"
            by (metis (no_types) \<open>0 \<le> m\<close> meas_adiff abs_minus_commute mult_right_mono)
          moreover have "\<forall>r. \<bar>r * m\<bar> = m * \<bar>r\<bar>"
            by (metis \<open>0 \<le> m\<close> abs_mult_pos mult.commute)
          ultimately show ?thesis
            apply (simp add: 2 [symmetric])
            by (metis (no_types) abs_minus_commute mult.commute right_diff_distrib' mm)
        qed
        also have "\<dots> < e"
          using \<open>e > 0\<close> by (auto simp: divide_simps)
        finally have "\<bar>?\<mu> (f ` S \<inter> cbox a b) - m * ?\<mu> S\<bar> < e" .
        with 1 show ?thesis by auto
      qed
      then show "\<exists>B>0. \<forall>a b. ball 0 B \<subseteq> cbox a b \<longrightarrow>
                         f ` S \<inter> cbox a b \<in> lmeasurable \<and>
                         \<bar>?\<mu> (f ` S \<inter> cbox a b) - m * ?\<mu> S\<bar> < e"
        using \<open>C>0\<close> \<open>D>0\<close> by (metis mult_zero_left real_mult_less_iff1)
    qed
  qed
qed


subsection\<open>Lemmas about absolute integrability\<close>

text\<open>FIXME Redundant!\<close>
lemma absolutely_integrable_add[intro]:
  fixes f g :: "'n::euclidean_space \<Rightarrow> 'm::euclidean_space"
  shows "f absolutely_integrable_on s \<Longrightarrow> g absolutely_integrable_on s \<Longrightarrow> (\<lambda>x. f x + g x) absolutely_integrable_on s"
  by (rule set_integral_add)

text\<open>FIXME Redundant!\<close>
lemma absolutely_integrable_diff[intro]:
  fixes f g :: "'n::euclidean_space \<Rightarrow> 'm::euclidean_space"
  shows "f absolutely_integrable_on s \<Longrightarrow> g absolutely_integrable_on s \<Longrightarrow> (\<lambda>x. f x - g x) absolutely_integrable_on s"
  by (rule set_integral_diff)

lemma absolutely_integrable_linear:
  fixes f :: "'m::euclidean_space \<Rightarrow> 'n::euclidean_space"
    and h :: "'n::euclidean_space \<Rightarrow> 'p::euclidean_space"
  shows "f absolutely_integrable_on s \<Longrightarrow> bounded_linear h \<Longrightarrow> (h \<circ> f) absolutely_integrable_on s"
  using integrable_bounded_linear[of h lebesgue "\<lambda>x. indicator s x *\<^sub>R f x"]
  by (simp add: linear_simps[of h] set_integrable_def)

lemma absolutely_integrable_sum:
  fixes f :: "'a \<Rightarrow> 'n::euclidean_space \<Rightarrow> 'm::euclidean_space"
  assumes "finite T" and "\<And>a. a \<in> T \<Longrightarrow> (f a) absolutely_integrable_on S"
  shows "(\<lambda>x. sum (\<lambda>a. f a x) T) absolutely_integrable_on S"
  using assms by induction auto

lemma absolutely_integrable_integrable_bound:
  fixes f :: "'n::euclidean_space \<Rightarrow> 'm::euclidean_space"
  assumes le: "\<And>x. x\<in>S \<Longrightarrow> norm (f x) \<le> g x" and f: "f integrable_on S" and g: "g integrable_on S"
  shows "f absolutely_integrable_on S"
    unfolding set_integrable_def
proof (rule Bochner_Integration.integrable_bound)
  have "g absolutely_integrable_on S"
    unfolding absolutely_integrable_on_def
  proof
    show "(\<lambda>x. norm (g x)) integrable_on S"
      using le norm_ge_zero[of "f _"]
      by (intro integrable_spike_finite[OF _ _ g, of "{}"])
         (auto intro!: abs_of_nonneg intro: order_trans simp del: norm_ge_zero)
  qed fact
  then show "integrable lebesgue (\<lambda>x. indicat_real S x *\<^sub>R g x)"
    by (simp add: set_integrable_def)
  show "(\<lambda>x. indicat_real S x *\<^sub>R f x) \<in> borel_measurable lebesgue"
    using f by (auto intro: has_integral_implies_lebesgue_measurable simp: integrable_on_def)
qed (use le in \<open>force intro!: always_eventually split: split_indicator\<close>)

lemma absolutely_integrable_continuous:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  shows "continuous_on (cbox a b) f \<Longrightarrow> f absolutely_integrable_on cbox a b"
  using absolutely_integrable_integrable_bound
  by (simp add: absolutely_integrable_on_def continuous_on_norm integrable_continuous)


subsection \<open>Componentwise\<close>

proposition absolutely_integrable_componentwise_iff:
  shows "f absolutely_integrable_on A \<longleftrightarrow> (\<forall>b\<in>Basis. (\<lambda>x. f x \<bullet> b) absolutely_integrable_on A)"
proof -
  have *: "(\<lambda>x. norm (f x)) integrable_on A \<longleftrightarrow> (\<forall>b\<in>Basis. (\<lambda>x. norm (f x \<bullet> b)) integrable_on A)"
          if "f integrable_on A"
  proof -
    have 1: "\<And>i. \<lbrakk>(\<lambda>x. norm (f x)) integrable_on A; i \<in> Basis\<rbrakk>
                 \<Longrightarrow> (\<lambda>x. f x \<bullet> i) absolutely_integrable_on A"
      apply (rule absolutely_integrable_integrable_bound [where g = "\<lambda>x. norm(f x)"])
      using Basis_le_norm integrable_component that apply fastforce+
      done
    have 2: "\<forall>i\<in>Basis. (\<lambda>x. \<bar>f x \<bullet> i\<bar>) integrable_on A \<Longrightarrow> f absolutely_integrable_on A"
      apply (rule absolutely_integrable_integrable_bound [where g = "\<lambda>x. \<Sum>i\<in>Basis. norm (f x \<bullet> i)"])
      using norm_le_l1 that apply (force intro: integrable_sum)+
      done
    show ?thesis
      apply auto
       apply (metis (full_types) absolutely_integrable_on_def set_integrable_abs 1)
      apply (metis (full_types) absolutely_integrable_on_def 2)
      done
  qed
  show ?thesis
    unfolding absolutely_integrable_on_def
    by (simp add:  integrable_componentwise_iff [symmetric] ball_conj_distrib * cong: conj_cong)
qed

lemma absolutely_integrable_componentwise:
  shows "(\<And>b. b \<in> Basis \<Longrightarrow> (\<lambda>x. f x \<bullet> b) absolutely_integrable_on A) \<Longrightarrow> f absolutely_integrable_on A"
  using absolutely_integrable_componentwise_iff by blast

lemma absolutely_integrable_component:
  "f absolutely_integrable_on A \<Longrightarrow> (\<lambda>x. f x \<bullet> (b :: 'b :: euclidean_space)) absolutely_integrable_on A"
  by (drule absolutely_integrable_linear[OF _ bounded_linear_inner_left[of b]]) (simp add: o_def)


lemma absolutely_integrable_scaleR_left:
  fixes f :: "'n::euclidean_space \<Rightarrow> 'm::euclidean_space"
    assumes "f absolutely_integrable_on S"
  shows "(\<lambda>x. c *\<^sub>R f x) absolutely_integrable_on S"
proof -
  have "(\<lambda>x. c *\<^sub>R x) o f absolutely_integrable_on S"
    apply (rule absolutely_integrable_linear [OF assms])
    by (simp add: bounded_linear_scaleR_right)
  then show ?thesis
    using assms by blast
qed

lemma absolutely_integrable_scaleR_right:
  assumes "f absolutely_integrable_on S"
  shows "(\<lambda>x. f x *\<^sub>R c) absolutely_integrable_on S"
  using assms by blast

lemma absolutely_integrable_norm:
  fixes f :: "'a :: euclidean_space \<Rightarrow> 'b :: euclidean_space"
  assumes "f absolutely_integrable_on S"
  shows "(norm o f) absolutely_integrable_on S"
  using assms by (simp add: absolutely_integrable_on_def o_def)

lemma absolutely_integrable_abs:
  fixes f :: "'a :: euclidean_space \<Rightarrow> 'b :: euclidean_space"
  assumes "f absolutely_integrable_on S"
  shows "(\<lambda>x. \<Sum>i\<in>Basis. \<bar>f x \<bullet> i\<bar> *\<^sub>R i) absolutely_integrable_on S"
        (is "?g absolutely_integrable_on S")
proof -
  have eq: "?g =
        (\<lambda>x. \<Sum>i\<in>Basis. ((\<lambda>y. \<Sum>j\<in>Basis. if j = i then y *\<^sub>R j else 0) \<circ>
               (\<lambda>x. norm(\<Sum>j\<in>Basis. if j = i then (x \<bullet> i) *\<^sub>R j else 0)) \<circ> f) x)"
    by (simp add: sum.delta)
  have *: "(\<lambda>y. \<Sum>j\<in>Basis. if j = i then y *\<^sub>R j else 0) \<circ>
           (\<lambda>x. norm (\<Sum>j\<in>Basis. if j = i then (x \<bullet> i) *\<^sub>R j else 0)) \<circ> f 
           absolutely_integrable_on S" 
        if "i \<in> Basis" for i
  proof -
    have "bounded_linear (\<lambda>y. \<Sum>j\<in>Basis. if j = i then y *\<^sub>R j else 0)"
      by (simp add: linear_linear algebra_simps linearI)
    moreover have "(\<lambda>x. norm (\<Sum>j\<in>Basis. if j = i then (x \<bullet> i) *\<^sub>R j else 0)) \<circ> f 
                   absolutely_integrable_on S"
      unfolding o_def
      apply (rule absolutely_integrable_norm [unfolded o_def])
      using assms \<open>i \<in> Basis\<close>
      apply (auto simp: algebra_simps dest: absolutely_integrable_component[where b=i])
      done
    ultimately show ?thesis
      by (subst comp_assoc) (blast intro: absolutely_integrable_linear)
  qed
  show ?thesis
    apply (rule ssubst [OF eq])
    apply (rule absolutely_integrable_sum)
     apply (force simp: intro!: *)+
    done
qed

lemma abs_absolutely_integrableI_1:
  fixes f :: "'a :: euclidean_space \<Rightarrow> real"
  assumes f: "f integrable_on A" and "(\<lambda>x. \<bar>f x\<bar>) integrable_on A"
  shows "f absolutely_integrable_on A"
  by (rule absolutely_integrable_integrable_bound [OF _ assms]) auto

  
lemma abs_absolutely_integrableI:
  assumes f: "f integrable_on S" and fcomp: "(\<lambda>x. \<Sum>i\<in>Basis. \<bar>f x \<bullet> i\<bar> *\<^sub>R i) integrable_on S"
  shows "f absolutely_integrable_on S"
proof -
  have "(\<lambda>x. (f x \<bullet> i) *\<^sub>R i) absolutely_integrable_on S" if "i \<in> Basis" for i
  proof -
    have "(\<lambda>x. \<bar>f x \<bullet> i\<bar>) integrable_on S" 
      using assms integrable_component [OF fcomp, where y=i] that by simp
    then have "(\<lambda>x. f x \<bullet> i) absolutely_integrable_on S"
      using abs_absolutely_integrableI_1 f integrable_component by blast
    then show ?thesis
      by (rule absolutely_integrable_scaleR_right)
  qed
  then have "(\<lambda>x. \<Sum>i\<in>Basis. (f x \<bullet> i) *\<^sub>R i) absolutely_integrable_on S"
    by (simp add: absolutely_integrable_sum)
  then show ?thesis
    by (simp add: euclidean_representation)
qed

    
lemma absolutely_integrable_abs_iff:
   "f absolutely_integrable_on S \<longleftrightarrow>
    f integrable_on S \<and> (\<lambda>x. \<Sum>i\<in>Basis. \<bar>f x \<bullet> i\<bar> *\<^sub>R i) integrable_on S"
    (is "?lhs = ?rhs")
proof
  assume ?lhs then show ?rhs
    using absolutely_integrable_abs absolutely_integrable_on_def by blast
next
  assume ?rhs 
  moreover
  have "(\<lambda>x. if x \<in> S then \<Sum>i\<in>Basis. \<bar>f x \<bullet> i\<bar> *\<^sub>R i else 0) = (\<lambda>x. \<Sum>i\<in>Basis. \<bar>(if x \<in> S then f x else 0) \<bullet> i\<bar> *\<^sub>R i)"
    by force
  ultimately show ?lhs
    by (simp only: absolutely_integrable_restrict_UNIV [of S, symmetric] integrable_restrict_UNIV [of S, symmetric] abs_absolutely_integrableI)
qed

lemma absolutely_integrable_max:
  fixes f :: "'n::euclidean_space \<Rightarrow> 'm::euclidean_space"
  assumes "f absolutely_integrable_on S" "g absolutely_integrable_on S"
   shows "(\<lambda>x. \<Sum>i\<in>Basis. max (f x \<bullet> i) (g x \<bullet> i) *\<^sub>R i)
            absolutely_integrable_on S"
proof -
  have "(\<lambda>x. \<Sum>i\<in>Basis. max (f x \<bullet> i) (g x \<bullet> i) *\<^sub>R i) = 
        (\<lambda>x. (1/2) *\<^sub>R (f x + g x + (\<Sum>i\<in>Basis. \<bar>f x \<bullet> i - g x \<bullet> i\<bar> *\<^sub>R i)))"
  proof (rule ext)
    fix x
    have "(\<Sum>i\<in>Basis. max (f x \<bullet> i) (g x \<bullet> i) *\<^sub>R i) = (\<Sum>i\<in>Basis. ((f x \<bullet> i + g x \<bullet> i + \<bar>f x \<bullet> i - g x \<bullet> i\<bar>) / 2) *\<^sub>R i)"
      by (force intro: sum.cong)
    also have "... = (1 / 2) *\<^sub>R (\<Sum>i\<in>Basis. (f x \<bullet> i + g x \<bullet> i + \<bar>f x \<bullet> i - g x \<bullet> i\<bar>) *\<^sub>R i)"
      by (simp add: scaleR_right.sum)
    also have "... = (1 / 2) *\<^sub>R (f x + g x + (\<Sum>i\<in>Basis. \<bar>f x \<bullet> i - g x \<bullet> i\<bar> *\<^sub>R i))"
      by (simp add: sum.distrib algebra_simps euclidean_representation)
    finally
    show "(\<Sum>i\<in>Basis. max (f x \<bullet> i) (g x \<bullet> i) *\<^sub>R i) =
         (1 / 2) *\<^sub>R (f x + g x + (\<Sum>i\<in>Basis. \<bar>f x \<bullet> i - g x \<bullet> i\<bar> *\<^sub>R i))" .
  qed
  moreover have "(\<lambda>x. (1 / 2) *\<^sub>R (f x + g x + (\<Sum>i\<in>Basis. \<bar>f x \<bullet> i - g x \<bullet> i\<bar> *\<^sub>R i))) 
                 absolutely_integrable_on S"
    apply (intro absolutely_integrable_add absolutely_integrable_scaleR_left assms)
    using absolutely_integrable_abs [OF absolutely_integrable_diff [OF assms]]
    apply (simp add: algebra_simps)
    done
  ultimately show ?thesis by metis
qed
  
corollary absolutely_integrable_max_1:
  fixes f :: "'n::euclidean_space \<Rightarrow> real"
  assumes "f absolutely_integrable_on S" "g absolutely_integrable_on S"
   shows "(\<lambda>x. max (f x) (g x)) absolutely_integrable_on S"
  using absolutely_integrable_max [OF assms] by simp

lemma absolutely_integrable_min:
  fixes f :: "'n::euclidean_space \<Rightarrow> 'm::euclidean_space"
  assumes "f absolutely_integrable_on S" "g absolutely_integrable_on S"
   shows "(\<lambda>x. \<Sum>i\<in>Basis. min (f x \<bullet> i) (g x \<bullet> i) *\<^sub>R i)
            absolutely_integrable_on S"
proof -
  have "(\<lambda>x. \<Sum>i\<in>Basis. min (f x \<bullet> i) (g x \<bullet> i) *\<^sub>R i) = 
        (\<lambda>x. (1/2) *\<^sub>R (f x + g x - (\<Sum>i\<in>Basis. \<bar>f x \<bullet> i - g x \<bullet> i\<bar> *\<^sub>R i)))"
  proof (rule ext)
    fix x
    have "(\<Sum>i\<in>Basis. min (f x \<bullet> i) (g x \<bullet> i) *\<^sub>R i) = (\<Sum>i\<in>Basis. ((f x \<bullet> i + g x \<bullet> i - \<bar>f x \<bullet> i - g x \<bullet> i\<bar>) / 2) *\<^sub>R i)"
      by (force intro: sum.cong)
    also have "... = (1 / 2) *\<^sub>R (\<Sum>i\<in>Basis. (f x \<bullet> i + g x \<bullet> i - \<bar>f x \<bullet> i - g x \<bullet> i\<bar>) *\<^sub>R i)"
      by (simp add: scaleR_right.sum)
    also have "... = (1 / 2) *\<^sub>R (f x + g x - (\<Sum>i\<in>Basis. \<bar>f x \<bullet> i - g x \<bullet> i\<bar> *\<^sub>R i))"
      by (simp add: sum.distrib sum_subtractf algebra_simps euclidean_representation)
    finally
    show "(\<Sum>i\<in>Basis. min (f x \<bullet> i) (g x \<bullet> i) *\<^sub>R i) =
         (1 / 2) *\<^sub>R (f x + g x - (\<Sum>i\<in>Basis. \<bar>f x \<bullet> i - g x \<bullet> i\<bar> *\<^sub>R i))" .
  qed
  moreover have "(\<lambda>x. (1 / 2) *\<^sub>R (f x + g x - (\<Sum>i\<in>Basis. \<bar>f x \<bullet> i - g x \<bullet> i\<bar> *\<^sub>R i))) 
                 absolutely_integrable_on S"
    apply (intro absolutely_integrable_add absolutely_integrable_diff absolutely_integrable_scaleR_left assms)
    using absolutely_integrable_abs [OF absolutely_integrable_diff [OF assms]]
    apply (simp add: algebra_simps)
    done
  ultimately show ?thesis by metis
qed
  
corollary absolutely_integrable_min_1:
  fixes f :: "'n::euclidean_space \<Rightarrow> real"
  assumes "f absolutely_integrable_on S" "g absolutely_integrable_on S"
   shows "(\<lambda>x. min (f x) (g x)) absolutely_integrable_on S"
  using absolutely_integrable_min [OF assms] by simp

lemma nonnegative_absolutely_integrable:
  fixes f :: "'a :: euclidean_space \<Rightarrow> 'b :: euclidean_space"
  assumes "f integrable_on A" and comp: "\<And>x b. \<lbrakk>x \<in> A; b \<in> Basis\<rbrakk> \<Longrightarrow> 0 \<le> f x \<bullet> b"
  shows "f absolutely_integrable_on A"
proof -
  have "(\<lambda>x. (f x \<bullet> i) *\<^sub>R i) absolutely_integrable_on A" if "i \<in> Basis" for i
  proof -
    have "(\<lambda>x. f x \<bullet> i) integrable_on A" 
      by (simp add: assms(1) integrable_component)
    then have "(\<lambda>x. f x \<bullet> i) absolutely_integrable_on A"
      by (metis that comp nonnegative_absolutely_integrable_1)
    then show ?thesis
      by (rule absolutely_integrable_scaleR_right)
  qed
  then have "(\<lambda>x. \<Sum>i\<in>Basis. (f x \<bullet> i) *\<^sub>R i) absolutely_integrable_on A"
    by (simp add: absolutely_integrable_sum)
  then show ?thesis
    by (simp add: euclidean_representation)
qed
  
lemma absolutely_integrable_component_ubound:
  fixes f :: "'a :: euclidean_space \<Rightarrow> 'b :: euclidean_space"
  assumes f: "f integrable_on A" and g: "g absolutely_integrable_on A"
      and comp: "\<And>x b. \<lbrakk>x \<in> A; b \<in> Basis\<rbrakk> \<Longrightarrow> f x \<bullet> b \<le> g x \<bullet> b"
  shows "f absolutely_integrable_on A"
proof -
  have "(\<lambda>x. g x - (g x - f x)) absolutely_integrable_on A"
    apply (rule absolutely_integrable_diff [OF g nonnegative_absolutely_integrable])
    using Henstock_Kurzweil_Integration.integrable_diff absolutely_integrable_on_def f g apply blast
    by (simp add: comp inner_diff_left)
  then show ?thesis
    by simp
qed

lemma absolutely_integrable_component_lbound:
  fixes f :: "'a :: euclidean_space \<Rightarrow> 'b :: euclidean_space"
  assumes f: "f absolutely_integrable_on A" and g: "g integrable_on A"
      and comp: "\<And>x b. \<lbrakk>x \<in> A; b \<in> Basis\<rbrakk> \<Longrightarrow> f x \<bullet> b \<le> g x \<bullet> b"
  shows "g absolutely_integrable_on A"
proof -
  have "(\<lambda>x. f x + (g x - f x)) absolutely_integrable_on A"
    apply (rule absolutely_integrable_add [OF f nonnegative_absolutely_integrable])
    using Henstock_Kurzweil_Integration.integrable_diff absolutely_integrable_on_def f g apply blast
    by (simp add: comp inner_diff_left)
  then show ?thesis
    by simp
qed

lemma integrable_on_1_iff:
  fixes f :: "'a::euclidean_space \<Rightarrow> real^1"
  shows "f integrable_on S \<longleftrightarrow> (\<lambda>x. f x $ 1) integrable_on S"
  by (auto simp: integrable_componentwise_iff [of f] Basis_vec_def cart_eq_inner_axis)

lemma integral_on_1_eq:
  fixes f :: "'a::euclidean_space \<Rightarrow> real^1"
  shows "integral S f = vec (integral S (\<lambda>x. f x $ 1))"
by (cases "f integrable_on S") (simp_all add: integrable_on_1_iff vec_eq_iff not_integrable_integral)

lemma absolutely_integrable_on_1_iff:
  fixes f :: "'a::euclidean_space \<Rightarrow> real^1"
  shows "f absolutely_integrable_on S \<longleftrightarrow> (\<lambda>x. f x $ 1) absolutely_integrable_on S"
  unfolding absolutely_integrable_on_def
  by (auto simp: integrable_on_1_iff norm_real)

lemma absolutely_integrable_absolutely_integrable_lbound:
  fixes f :: "'m::euclidean_space \<Rightarrow> real"
  assumes f: "f integrable_on S" and g: "g absolutely_integrable_on S"
    and *: "\<And>x. x \<in> S \<Longrightarrow> g x \<le> f x"
  shows "f absolutely_integrable_on S"
  by (rule absolutely_integrable_component_lbound [OF g f]) (simp add: *)

lemma absolutely_integrable_absolutely_integrable_ubound:
  fixes f :: "'m::euclidean_space \<Rightarrow> real"
  assumes fg: "f integrable_on S" "g absolutely_integrable_on S"
    and *: "\<And>x. x \<in> S \<Longrightarrow> f x \<le> g x"
  shows "f absolutely_integrable_on S"
  by (rule absolutely_integrable_component_ubound [OF fg]) (simp add: *)

lemma has_integral_vec1_I_cbox:
  fixes f :: "real^1 \<Rightarrow> 'a::real_normed_vector"
  assumes "(f has_integral y) (cbox a b)"
  shows "((f \<circ> vec) has_integral y) {a$1..b$1}"
proof -
  have "((\<lambda>x. f(vec x)) has_integral (1 / 1) *\<^sub>R y) ((\<lambda>x. x $ 1) ` cbox a b)"
  proof (rule has_integral_twiddle)
    show "\<exists>w z::real^1. vec ` cbox u v = cbox w z"
         "content (vec ` cbox u v :: (real^1) set) = 1 * content (cbox u v)" for u v
      unfolding vec_cbox_1_eq
      by (auto simp: content_cbox_if_cart interval_eq_empty_cart)
    show "\<exists>w z. (\<lambda>x. x $ 1) ` cbox u v = cbox w z" for u v :: "real^1"
      using vec_nth_cbox_1_eq by blast
  qed (auto simp: continuous_vec assms)
  then show ?thesis
    by (simp add: o_def)
qed

lemma has_integral_vec1_I:
  fixes f :: "real^1 \<Rightarrow> 'a::real_normed_vector"
  assumes "(f has_integral y) S"
  shows "(f \<circ> vec has_integral y) ((\<lambda>x. x $ 1) ` S)"
proof -
  have *: "\<exists>z. ((\<lambda>x. if x \<in> (\<lambda>x. x $ 1) ` S then (f \<circ> vec) x else 0) has_integral z) {a..b} \<and> norm (z - y) < e"
    if int: "\<And>a b. ball 0 B \<subseteq> cbox a b \<Longrightarrow>
                    (\<exists>z. ((\<lambda>x. if x \<in> S then f x else 0) has_integral z) (cbox a b) \<and> norm (z - y) < e)"
      and B: "ball 0 B \<subseteq> {a..b}" for e B a b
  proof -
    have [simp]: "(\<exists>y\<in>S. x = y $ 1) \<longleftrightarrow> vec x \<in> S" for x
      by force
    have B': "ball (0::real^1) B \<subseteq> cbox (vec a) (vec b)"
      using B by (simp add: Basis_vec_def cart_eq_inner_axis [symmetric] mem_box norm_real subset_iff)
    show ?thesis
      using int [OF B'] by (auto simp: image_iff o_def cong: if_cong dest!: has_integral_vec1_I_cbox)
  qed
  show ?thesis
    using assms 
    apply (subst has_integral_alt)
    apply (subst (asm) has_integral_alt)
    apply (simp add: has_integral_vec1_I_cbox split: if_split_asm)
    apply (metis vector_one_nth)
    apply (erule all_forward imp_forward asm_rl ex_forward conj_forward)+
    apply (blast intro!: *)
    done
qed

lemma has_integral_vec1_nth_cbox:
  fixes f :: "real \<Rightarrow> 'a::real_normed_vector"
  assumes "(f has_integral y) {a..b}"
  shows "((\<lambda>x::real^1. f(x$1)) has_integral y) (cbox (vec a) (vec b))"
proof -
  have "((\<lambda>x::real^1. f(x$1)) has_integral (1 / 1) *\<^sub>R y) (vec ` cbox a b)"
  proof (rule has_integral_twiddle)
    show "\<exists>w z::real. (\<lambda>x. x $ 1) ` cbox u v = cbox w z"
         "content ((\<lambda>x. x $ 1) ` cbox u v) = 1 * content (cbox u v)" for u v::"real^1"
      unfolding vec_cbox_1_eq by (auto simp: content_cbox_if_cart interval_eq_empty_cart)
    show "\<exists>w z::real^1. vec ` cbox u v = cbox w z" for u v :: "real"
      using vec_cbox_1_eq by auto
  qed (auto simp: continuous_vec assms)
  then show ?thesis
    using vec_cbox_1_eq by auto
qed

lemma has_integral_vec1_D_cbox:
  fixes f :: "real^1 \<Rightarrow> 'a::real_normed_vector"
  assumes "((f \<circ> vec) has_integral y) {a$1..b$1}"
  shows "(f has_integral y) (cbox a b)"
  by (metis (mono_tags, lifting) assms comp_apply has_integral_eq has_integral_vec1_nth_cbox vector_one_nth)

lemma has_integral_vec1_D:
  fixes f :: "real^1 \<Rightarrow> 'a::real_normed_vector"
  assumes "((f \<circ> vec) has_integral y) ((\<lambda>x. x $ 1) ` S)"
  shows "(f has_integral y) S"
proof -
  have *: "\<exists>z. ((\<lambda>x. if x \<in> S then f x else 0) has_integral z) (cbox a b) \<and> norm (z - y) < e"
    if int: "\<And>a b. ball 0 B \<subseteq> {a..b} \<Longrightarrow>
                             (\<exists>z. ((\<lambda>x. if x \<in> (\<lambda>x. x $ 1) ` S then (f \<circ> vec) x else 0) has_integral z) {a..b} \<and> norm (z - y) < e)"
      and B: "ball 0 B \<subseteq> cbox a b" for e B and a b::"real^1"
  proof -
    have B': "ball 0 B \<subseteq> {a$1..b$1}"
      using B
      apply (simp add: subset_iff Basis_vec_def cart_eq_inner_axis [symmetric] mem_box)
      apply (metis (full_types) norm_real vec_component)
      done
    have eq: "(\<lambda>x. if vec x \<in> S then f (vec x) else 0) = (\<lambda>x. if x \<in> S then f x else 0) \<circ> vec"
      by force
    have [simp]: "(\<exists>y\<in>S. x = y $ 1) \<longleftrightarrow> vec x \<in> S" for x
      by force
    show ?thesis
      using int [OF B'] by (auto simp: image_iff eq cong: if_cong dest!: has_integral_vec1_D_cbox)
qed
  show ?thesis
    using assms
    apply (subst has_integral_alt)
    apply (subst (asm) has_integral_alt)
    apply (simp add: has_integral_vec1_D_cbox eq_cbox split: if_split_asm, blast)
    apply (intro conjI impI)
     apply (metis vector_one_nth)
    apply (erule thin_rl)
    apply (erule all_forward imp_forward asm_rl ex_forward conj_forward)+
    using * apply blast
    done
qed


lemma integral_vec1_eq:
  fixes f :: "real^1 \<Rightarrow> 'a::real_normed_vector"
  shows "integral S f = integral ((\<lambda>x. x $ 1) ` S) (f \<circ> vec)"
  using has_integral_vec1_I [of f] has_integral_vec1_D [of f]
  by (metis has_integral_iff not_integrable_integral)

lemma absolutely_integrable_drop:
  fixes f :: "real^1 \<Rightarrow> 'b::euclidean_space"
  shows "f absolutely_integrable_on S \<longleftrightarrow> (f \<circ> vec) absolutely_integrable_on (\<lambda>x. x $ 1) ` S"
  unfolding absolutely_integrable_on_def integrable_on_def
proof safe
  fix y r
  assume "(f has_integral y) S" "((\<lambda>x. norm (f x)) has_integral r) S"
  then show "\<exists>y. (f \<circ> vec has_integral y) ((\<lambda>x. x $ 1) ` S)"
            "\<exists>y. ((\<lambda>x. norm ((f \<circ> vec) x)) has_integral y) ((\<lambda>x. x $ 1) ` S)"
    by (force simp: o_def dest!: has_integral_vec1_I)+
next
  fix y :: "'b" and r :: "real"
  assume "(f \<circ> vec has_integral y) ((\<lambda>x. x $ 1) ` S)"
         "((\<lambda>x. norm ((f \<circ> vec) x)) has_integral r) ((\<lambda>x. x $ 1) ` S)"
  then show "\<exists>y. (f has_integral y) S"  "\<exists>y. ((\<lambda>x. norm (f x)) has_integral y) S"
    by (force simp: o_def intro: has_integral_vec1_D)+
qed

subsection \<open>Dominated convergence\<close>

lemma dominated_convergence:
  fixes f :: "nat \<Rightarrow> 'n::euclidean_space \<Rightarrow> 'm::euclidean_space"
  assumes f: "\<And>k. (f k) integrable_on S" and h: "h integrable_on S"
    and le: "\<And>k x. x \<in> S \<Longrightarrow> norm (f k x) \<le> h x"
    and conv: "\<forall>x \<in> S. (\<lambda>k. f k x) \<longlonglongrightarrow> g x"
  shows "g integrable_on S" "(\<lambda>k. integral S (f k)) \<longlonglongrightarrow> integral S g"
proof -
  have 3: "h absolutely_integrable_on S"
    unfolding absolutely_integrable_on_def
  proof
    show "(\<lambda>x. norm (h x)) integrable_on S"
    proof (intro integrable_spike_finite[OF _ _ h, of "{}"] ballI)
      fix x assume "x \<in> S - {}" then show "norm (h x) = h x"
        by (metis Diff_empty abs_of_nonneg bot_set_def le norm_ge_zero order_trans real_norm_def)
    qed auto
  qed fact
  have 2: "set_borel_measurable lebesgue S (f k)" for k
    unfolding set_borel_measurable_def
    using f by (auto intro: has_integral_implies_lebesgue_measurable simp: integrable_on_def)
  then have 1: "set_borel_measurable lebesgue S g"
    unfolding set_borel_measurable_def
    by (rule borel_measurable_LIMSEQ_metric) (use conv in \<open>auto split: split_indicator\<close>)
  have 4: "AE x in lebesgue. (\<lambda>i. indicator S x *\<^sub>R f i x) \<longlonglongrightarrow> indicator S x *\<^sub>R g x"
    "AE x in lebesgue. norm (indicator S x *\<^sub>R f k x) \<le> indicator S x *\<^sub>R h x" for k
    using conv le by (auto intro!: always_eventually split: split_indicator)
  have g: "g absolutely_integrable_on S"
    using 1 2 3 4 unfolding set_borel_measurable_def set_integrable_def    
    by (rule integrable_dominated_convergence)
  then show "g integrable_on S"
    by (auto simp: absolutely_integrable_on_def)
  have "(\<lambda>k. (LINT x:S|lebesgue. f k x)) \<longlonglongrightarrow> (LINT x:S|lebesgue. g x)"
    unfolding set_borel_measurable_def set_lebesgue_integral_def
    using 1 2 3 4 unfolding set_borel_measurable_def set_lebesgue_integral_def set_integrable_def
    by (rule integral_dominated_convergence)
  then show "(\<lambda>k. integral S (f k)) \<longlonglongrightarrow> integral S g"
    using g absolutely_integrable_integrable_bound[OF le f h]
    by (subst (asm) (1 2) set_lebesgue_integral_eq_integral) auto
qed

lemma has_integral_dominated_convergence:
  fixes f :: "nat \<Rightarrow> 'n::euclidean_space \<Rightarrow> 'm::euclidean_space"
  assumes "\<And>k. (f k has_integral y k) S" "h integrable_on S"
    "\<And>k. \<forall>x\<in>S. norm (f k x) \<le> h x" "\<forall>x\<in>S. (\<lambda>k. f k x) \<longlonglongrightarrow> g x"
    and x: "y \<longlonglongrightarrow> x"
  shows "(g has_integral x) S"
proof -
  have int_f: "\<And>k. (f k) integrable_on S"
    using assms by (auto simp: integrable_on_def)
  have "(g has_integral (integral S g)) S"
    by (metis assms(2-4) dominated_convergence(1) has_integral_integral int_f)
  moreover have "integral S g = x"
  proof (rule LIMSEQ_unique)
    show "(\<lambda>i. integral S (f i)) \<longlonglongrightarrow> x"
      using integral_unique[OF assms(1)] x by simp
    show "(\<lambda>i. integral S (f i)) \<longlonglongrightarrow> integral S g"
      by (metis assms(2) assms(3) assms(4) dominated_convergence(2) int_f)
  qed
  ultimately show ?thesis
    by simp
qed

lemma dominated_convergence_integrable_1:
  fixes f :: "nat \<Rightarrow> 'n::euclidean_space \<Rightarrow> real"
  assumes f: "\<And>k. f k absolutely_integrable_on S"
    and h: "h integrable_on S"
    and normg: "\<And>x. x \<in> S \<Longrightarrow> norm(g x) \<le> (h x)"
    and lim: "\<And>x. x \<in> S \<Longrightarrow> (\<lambda>k. f k x) \<longlonglongrightarrow> g x"
 shows "g integrable_on S"
proof -
  have habs: "h absolutely_integrable_on S"
    using h normg nonnegative_absolutely_integrable_1 norm_ge_zero order_trans by blast
  let ?f = "\<lambda>n x. (min (max (- h x) (f n x)) (h x))"
  have h0: "h x \<ge> 0" if "x \<in> S" for x
    using normg that by force
  have leh: "norm (?f k x) \<le> h x" if "x \<in> S" for k x
    using h0 that by force
  have limf: "(\<lambda>k. ?f k x) \<longlonglongrightarrow> g x" if "x \<in> S" for x
  proof -
    have "\<And>e y. \<bar>f y x - g x\<bar> < e \<Longrightarrow> \<bar>min (max (- h x) (f y x)) (h x) - g x\<bar> < e"
      using h0 [OF that] normg [OF that] by simp
    then show ?thesis
      using lim [OF that] by (auto simp add: tendsto_iff dist_norm elim!: eventually_mono)
  qed
  show ?thesis
  proof (rule dominated_convergence [of ?f S h g])
    have "(\<lambda>x. - h x) absolutely_integrable_on S"
      using habs unfolding set_integrable_def by auto
    then show "?f k integrable_on S" for k
      by (intro set_lebesgue_integral_eq_integral absolutely_integrable_min_1 absolutely_integrable_max_1 f habs)
  qed (use assms leh limf in auto)
qed

lemma dominated_convergence_integrable:
  fixes f :: "nat \<Rightarrow> 'n::euclidean_space \<Rightarrow> 'm::euclidean_space"
  assumes f: "\<And>k. f k absolutely_integrable_on S"
    and h: "h integrable_on S"
    and normg: "\<And>x. x \<in> S \<Longrightarrow> norm(g x) \<le> (h x)"
    and lim: "\<And>x. x \<in> S \<Longrightarrow> (\<lambda>k. f k x) \<longlonglongrightarrow> g x"
  shows "g integrable_on S"
  using f
  unfolding integrable_componentwise_iff [of g] absolutely_integrable_componentwise_iff [where f = "f k" for k]
proof clarify
  fix b :: "'m"
  assume fb [rule_format]: "\<And>k. \<forall>b\<in>Basis. (\<lambda>x. f k x \<bullet> b) absolutely_integrable_on S" and b: "b \<in> Basis"
  show "(\<lambda>x. g x \<bullet> b) integrable_on S"
  proof (rule dominated_convergence_integrable_1 [OF fb h])
    fix x 
    assume "x \<in> S"
    show "norm (g x \<bullet> b) \<le> h x"
      using norm_nth_le \<open>x \<in> S\<close> b normg order.trans by blast
    show "(\<lambda>k. f k x \<bullet> b) \<longlonglongrightarrow> g x \<bullet> b"
      using \<open>x \<in> S\<close> b lim tendsto_componentwise_iff by fastforce
  qed (use b in auto)
qed

lemma dominated_convergence_absolutely_integrable:
  fixes f :: "nat \<Rightarrow> 'n::euclidean_space \<Rightarrow> 'm::euclidean_space"
  assumes f: "\<And>k. f k absolutely_integrable_on S"
    and h: "h integrable_on S"
    and normg: "\<And>x. x \<in> S \<Longrightarrow> norm(g x) \<le> (h x)"
    and lim: "\<And>x. x \<in> S \<Longrightarrow> (\<lambda>k. f k x) \<longlonglongrightarrow> g x"
  shows "g absolutely_integrable_on S"
proof -
  have "g integrable_on S"
    by (rule dominated_convergence_integrable [OF assms])
  with assms show ?thesis
    by (blast intro:  absolutely_integrable_integrable_bound [where g=h])
qed


proposition integral_countable_UN:
  fixes f :: "real^'m \<Rightarrow> real^'n"
  assumes f: "f absolutely_integrable_on (\<Union>(range s))"
    and s: "\<And>m. s m \<in> sets lebesgue"
  shows "\<And>n. f absolutely_integrable_on (\<Union>m\<le>n. s m)"
    and "(\<lambda>n. integral (\<Union>m\<le>n. s m) f) \<longlonglongrightarrow> integral (UNION UNIV s) f" (is "?F \<longlonglongrightarrow> ?I")
proof -
  show fU: "f absolutely_integrable_on (\<Union>m\<le>n. s m)" for n
    using assms by (blast intro: set_integrable_subset [OF f])
  have fint: "f integrable_on (\<Union> (range s))"
    using absolutely_integrable_on_def f by blast
  let ?h = "\<lambda>x. if x \<in> UNION UNIV s then norm(f x) else 0"
  have "(\<lambda>n. integral UNIV (\<lambda>x. if x \<in> (\<Union>m\<le>n. s m) then f x else 0))
        \<longlonglongrightarrow> integral UNIV (\<lambda>x. if x \<in> UNION UNIV s then f x else 0)"
  proof (rule dominated_convergence)
    show "(\<lambda>x. if x \<in> (\<Union>m\<le>n. s m) then f x else 0) integrable_on UNIV" for n
      unfolding integrable_restrict_UNIV
      using fU absolutely_integrable_on_def by blast
    show "(\<lambda>x. if x \<in> UNION UNIV s then norm(f x) else 0) integrable_on UNIV"
      by (metis (no_types) absolutely_integrable_on_def f integrable_restrict_UNIV)
    show "\<forall>x\<in>UNIV.
         (\<lambda>n. if x \<in> (\<Union>m\<le>n. s m) then f x else 0)
         \<longlonglongrightarrow> (if x \<in> UNION UNIV s then f x else 0)"
      by (force intro: Lim_eventually eventually_sequentiallyI)
  qed auto
  then show "?F \<longlonglongrightarrow> ?I"
    by (simp only: integral_restrict_UNIV)
qed


subsection \<open>Fundamental Theorem of Calculus for the Lebesgue integral\<close>

text \<open>

For the positive integral we replace continuity with Borel-measurability.

\<close>

lemma                                                                                          
  fixes f :: "real \<Rightarrow> real"
  assumes [measurable]: "f \<in> borel_measurable borel"
  assumes f: "\<And>x. x \<in> {a..b} \<Longrightarrow> DERIV F x :> f x" "\<And>x. x \<in> {a..b} \<Longrightarrow> 0 \<le> f x" and "a \<le> b"
  shows nn_integral_FTC_Icc: "(\<integral>\<^sup>+x. ennreal (f x) * indicator {a .. b} x \<partial>lborel) = F b - F a" (is ?nn)
    and has_bochner_integral_FTC_Icc_nonneg:
      "has_bochner_integral lborel (\<lambda>x. f x * indicator {a .. b} x) (F b - F a)" (is ?has)
    and integral_FTC_Icc_nonneg: "(\<integral>x. f x * indicator {a .. b} x \<partial>lborel) = F b - F a" (is ?eq)
    and integrable_FTC_Icc_nonneg: "integrable lborel (\<lambda>x. f x * indicator {a .. b} x)" (is ?int)
proof -
  have *: "(\<lambda>x. f x * indicator {a..b} x) \<in> borel_measurable borel" "\<And>x. 0 \<le> f x * indicator {a..b} x"
    using f(2) by (auto split: split_indicator)

  have F_mono: "a \<le> x \<Longrightarrow> x \<le> y \<Longrightarrow> y \<le> b\<Longrightarrow> F x \<le> F y" for x y
    using f by (intro DERIV_nonneg_imp_nondecreasing[of x y F]) (auto intro: order_trans)

  have "(f has_integral F b - F a) {a..b}"
    by (intro fundamental_theorem_of_calculus)
       (auto simp: has_field_derivative_iff_has_vector_derivative[symmetric]
             intro: has_field_derivative_subset[OF f(1)] \<open>a \<le> b\<close>)
  then have i: "((\<lambda>x. f x * indicator {a .. b} x) has_integral F b - F a) UNIV"
    unfolding indicator_def if_distrib[where f="\<lambda>x. a * x" for a]
    by (simp cong del: if_weak_cong del: atLeastAtMost_iff)
  then have nn: "(\<integral>\<^sup>+x. f x * indicator {a .. b} x \<partial>lborel) = F b - F a"
    by (rule nn_integral_has_integral_lborel[OF *])
  then show ?has
    by (rule has_bochner_integral_nn_integral[rotated 3]) (simp_all add: * F_mono \<open>a \<le> b\<close>)
  then show ?eq ?int
    unfolding has_bochner_integral_iff by auto
  show ?nn
    by (subst nn[symmetric])
       (auto intro!: nn_integral_cong simp add: ennreal_mult f split: split_indicator)
qed

lemma
  fixes f :: "real \<Rightarrow> 'a :: euclidean_space"
  assumes "a \<le> b"
  assumes "\<And>x. a \<le> x \<Longrightarrow> x \<le> b \<Longrightarrow> (F has_vector_derivative f x) (at x within {a .. b})"
  assumes cont: "continuous_on {a .. b} f"
  shows has_bochner_integral_FTC_Icc:
      "has_bochner_integral lborel (\<lambda>x. indicator {a .. b} x *\<^sub>R f x) (F b - F a)" (is ?has)
    and integral_FTC_Icc: "(\<integral>x. indicator {a .. b} x *\<^sub>R f x \<partial>lborel) = F b - F a" (is ?eq)
proof -
  let ?f = "\<lambda>x. indicator {a .. b} x *\<^sub>R f x"
  have int: "integrable lborel ?f"
    using borel_integrable_compact[OF _ cont] by auto
  have "(f has_integral F b - F a) {a..b}"
    using assms(1,2) by (intro fundamental_theorem_of_calculus) auto
  moreover
  have "(f has_integral integral\<^sup>L lborel ?f) {a..b}"
    using has_integral_integral_lborel[OF int]
    unfolding indicator_def if_distrib[where f="\<lambda>x. x *\<^sub>R a" for a]
    by (simp cong del: if_weak_cong del: atLeastAtMost_iff)
  ultimately show ?eq
    by (auto dest: has_integral_unique)
  then show ?has
    using int by (auto simp: has_bochner_integral_iff)
qed

lemma
  fixes f :: "real \<Rightarrow> real"
  assumes "a \<le> b"
  assumes deriv: "\<And>x. a \<le> x \<Longrightarrow> x \<le> b \<Longrightarrow> DERIV F x :> f x"
  assumes cont: "\<And>x. a \<le> x \<Longrightarrow> x \<le> b \<Longrightarrow> isCont f x"
  shows has_bochner_integral_FTC_Icc_real:
      "has_bochner_integral lborel (\<lambda>x. f x * indicator {a .. b} x) (F b - F a)" (is ?has)
    and integral_FTC_Icc_real: "(\<integral>x. f x * indicator {a .. b} x \<partial>lborel) = F b - F a" (is ?eq)
proof -
  have 1: "\<And>x. a \<le> x \<Longrightarrow> x \<le> b \<Longrightarrow> (F has_vector_derivative f x) (at x within {a .. b})"
    unfolding has_field_derivative_iff_has_vector_derivative[symmetric]
    using deriv by (auto intro: DERIV_subset)
  have 2: "continuous_on {a .. b} f"
    using cont by (intro continuous_at_imp_continuous_on) auto
  show ?has ?eq
    using has_bochner_integral_FTC_Icc[OF \<open>a \<le> b\<close> 1 2] integral_FTC_Icc[OF \<open>a \<le> b\<close> 1 2]
    by (auto simp: mult.commute)
qed

lemma nn_integral_FTC_atLeast:
  fixes f :: "real \<Rightarrow> real"
  assumes f_borel: "f \<in> borel_measurable borel"
  assumes f: "\<And>x. a \<le> x \<Longrightarrow> DERIV F x :> f x"
  assumes nonneg: "\<And>x. a \<le> x \<Longrightarrow> 0 \<le> f x"
  assumes lim: "(F \<longlongrightarrow> T) at_top"
  shows "(\<integral>\<^sup>+x. ennreal (f x) * indicator {a ..} x \<partial>lborel) = T - F a"
proof -
  let ?f = "\<lambda>(i::nat) (x::real). ennreal (f x) * indicator {a..a + real i} x"
  let ?fR = "\<lambda>x. ennreal (f x) * indicator {a ..} x"

  have F_mono: "a \<le> x \<Longrightarrow> x \<le> y \<Longrightarrow> F x \<le> F y" for x y
    using f nonneg by (intro DERIV_nonneg_imp_nondecreasing[of x y F]) (auto intro: order_trans)
  then have F_le_T: "a \<le> x \<Longrightarrow> F x \<le> T" for x
    by (intro tendsto_lowerbound[OF lim])
       (auto simp: eventually_at_top_linorder)

  have "(SUP i::nat. ?f i x) = ?fR x" for x
  proof (rule LIMSEQ_unique[OF LIMSEQ_SUP])
    obtain n where "x - a < real n"
      using reals_Archimedean2[of "x - a"] ..
    then have "eventually (\<lambda>n. ?f n x = ?fR x) sequentially"
      by (auto intro!: eventually_sequentiallyI[where c=n] split: split_indicator)
    then show "(\<lambda>n. ?f n x) \<longlonglongrightarrow> ?fR x"
      by (rule Lim_eventually)
  qed (auto simp: nonneg incseq_def le_fun_def split: split_indicator)
  then have "integral\<^sup>N lborel ?fR = (\<integral>\<^sup>+ x. (SUP i::nat. ?f i x) \<partial>lborel)"
    by simp
  also have "\<dots> = (SUP i::nat. (\<integral>\<^sup>+ x. ?f i x \<partial>lborel))"
  proof (rule nn_integral_monotone_convergence_SUP)
    show "incseq ?f"
      using nonneg by (auto simp: incseq_def le_fun_def split: split_indicator)
    show "\<And>i. (?f i) \<in> borel_measurable lborel"
      using f_borel by auto
  qed
  also have "\<dots> = (SUP i::nat. ennreal (F (a + real i) - F a))"
    by (subst nn_integral_FTC_Icc[OF f_borel f nonneg]) auto
  also have "\<dots> = T - F a"
  proof (rule LIMSEQ_unique[OF LIMSEQ_SUP])
    have "(\<lambda>x. F (a + real x)) \<longlonglongrightarrow> T"
      apply (rule filterlim_compose[OF lim filterlim_tendsto_add_at_top])
      apply (rule LIMSEQ_const_iff[THEN iffD2, OF refl])
      apply (rule filterlim_real_sequentially)
      done
    then show "(\<lambda>n. ennreal (F (a + real n) - F a)) \<longlonglongrightarrow> ennreal (T - F a)"
      by (simp add: F_mono F_le_T tendsto_diff)
  qed (auto simp: incseq_def intro!: ennreal_le_iff[THEN iffD2] F_mono)
  finally show ?thesis .
qed

lemma integral_power:
  "a \<le> b \<Longrightarrow> (\<integral>x. x^k * indicator {a..b} x \<partial>lborel) = (b^Suc k - a^Suc k) / Suc k"
proof (subst integral_FTC_Icc_real)
  fix x show "DERIV (\<lambda>x. x^Suc k / Suc k) x :> x^k"
    by (intro derivative_eq_intros) auto
qed (auto simp: field_simps simp del: of_nat_Suc)

subsection \<open>Integration by parts\<close>

lemma integral_by_parts_integrable:
  fixes f g F G::"real \<Rightarrow> real"
  assumes "a \<le> b"
  assumes cont_f[intro]: "!!x. a \<le>x \<Longrightarrow> x\<le>b \<Longrightarrow> isCont f x"
  assumes cont_g[intro]: "!!x. a \<le>x \<Longrightarrow> x\<le>b \<Longrightarrow> isCont g x"
  assumes [intro]: "!!x. DERIV F x :> f x"
  assumes [intro]: "!!x. DERIV G x :> g x"
  shows  "integrable lborel (\<lambda>x.((F x) * (g x) + (f x) * (G x)) * indicator {a .. b} x)"
  by (auto intro!: borel_integrable_atLeastAtMost continuous_intros) (auto intro!: DERIV_isCont)

lemma integral_by_parts:
  fixes f g F G::"real \<Rightarrow> real"
  assumes [arith]: "a \<le> b"
  assumes cont_f[intro]: "!!x. a \<le>x \<Longrightarrow> x\<le>b \<Longrightarrow> isCont f x"
  assumes cont_g[intro]: "!!x. a \<le>x \<Longrightarrow> x\<le>b \<Longrightarrow> isCont g x"
  assumes [intro]: "!!x. DERIV F x :> f x"
  assumes [intro]: "!!x. DERIV G x :> g x"
  shows "(\<integral>x. (F x * g x) * indicator {a .. b} x \<partial>lborel)
            =  F b * G b - F a * G a - \<integral>x. (f x * G x) * indicator {a .. b} x \<partial>lborel"
proof-
  have 0: "(\<integral>x. (F x * g x + f x * G x) * indicator {a .. b} x \<partial>lborel) = F b * G b - F a * G a"
    by (rule integral_FTC_Icc_real, auto intro!: derivative_eq_intros continuous_intros)
      (auto intro!: DERIV_isCont)

  have "(\<integral>x. (F x * g x + f x * G x) * indicator {a .. b} x \<partial>lborel) =
    (\<integral>x. (F x * g x) * indicator {a .. b} x \<partial>lborel) + \<integral>x. (f x * G x) * indicator {a .. b} x \<partial>lborel"
    apply (subst Bochner_Integration.integral_add[symmetric])
    apply (auto intro!: borel_integrable_atLeastAtMost continuous_intros)
    by (auto intro!: DERIV_isCont Bochner_Integration.integral_cong split: split_indicator)

  thus ?thesis using 0 by auto
qed

lemma integral_by_parts':
  fixes f g F G::"real \<Rightarrow> real"
  assumes "a \<le> b"
  assumes "!!x. a \<le>x \<Longrightarrow> x\<le>b \<Longrightarrow> isCont f x"
  assumes "!!x. a \<le>x \<Longrightarrow> x\<le>b \<Longrightarrow> isCont g x"
  assumes "!!x. DERIV F x :> f x"
  assumes "!!x. DERIV G x :> g x"
  shows "(\<integral>x. indicator {a .. b} x *\<^sub>R (F x * g x) \<partial>lborel)
            =  F b * G b - F a * G a - \<integral>x. indicator {a .. b} x *\<^sub>R (f x * G x) \<partial>lborel"
  using integral_by_parts[OF assms] by (simp add: ac_simps)

lemma has_bochner_integral_even_function:
  fixes f :: "real \<Rightarrow> 'a :: {banach, second_countable_topology}"
  assumes f: "has_bochner_integral lborel (\<lambda>x. indicator {0..} x *\<^sub>R f x) x"
  assumes even: "\<And>x. f (- x) = f x"
  shows "has_bochner_integral lborel f (2 *\<^sub>R x)"
proof -
  have indicator: "\<And>x::real. indicator {..0} (- x) = indicator {0..} x"
    by (auto split: split_indicator)
  have "has_bochner_integral lborel (\<lambda>x. indicator {.. 0} x *\<^sub>R f x) x"
    by (subst lborel_has_bochner_integral_real_affine_iff[where c="-1" and t=0])
       (auto simp: indicator even f)
  with f have "has_bochner_integral lborel (\<lambda>x. indicator {0..} x *\<^sub>R f x + indicator {.. 0} x *\<^sub>R f x) (x + x)"
    by (rule has_bochner_integral_add)
  then have "has_bochner_integral lborel f (x + x)"
    by (rule has_bochner_integral_discrete_difference[where X="{0}", THEN iffD1, rotated 4])
       (auto split: split_indicator)
  then show ?thesis
    by (simp add: scaleR_2)
qed

lemma has_bochner_integral_odd_function:
  fixes f :: "real \<Rightarrow> 'a :: {banach, second_countable_topology}"
  assumes f: "has_bochner_integral lborel (\<lambda>x. indicator {0..} x *\<^sub>R f x) x"
  assumes odd: "\<And>x. f (- x) = - f x"
  shows "has_bochner_integral lborel f 0"
proof -
  have indicator: "\<And>x::real. indicator {..0} (- x) = indicator {0..} x"
    by (auto split: split_indicator)
  have "has_bochner_integral lborel (\<lambda>x. - indicator {.. 0} x *\<^sub>R f x) x"
    by (subst lborel_has_bochner_integral_real_affine_iff[where c="-1" and t=0])
       (auto simp: indicator odd f)
  from has_bochner_integral_minus[OF this]
  have "has_bochner_integral lborel (\<lambda>x. indicator {.. 0} x *\<^sub>R f x) (- x)"
    by simp
  with f have "has_bochner_integral lborel (\<lambda>x. indicator {0..} x *\<^sub>R f x + indicator {.. 0} x *\<^sub>R f x) (x + - x)"
    by (rule has_bochner_integral_add)
  then have "has_bochner_integral lborel f (x + - x)"
    by (rule has_bochner_integral_discrete_difference[where X="{0}", THEN iffD1, rotated 4])
       (auto split: split_indicator)
  then show ?thesis
    by simp
qed

lemma has_integral_0_closure_imp_0:
  fixes f :: "'a::euclidean_space \<Rightarrow> real"
  assumes f: "continuous_on (closure S) f"
    and nonneg_interior: "\<And>x. x \<in> S \<Longrightarrow> 0 \<le> f x"
    and pos: "0 < emeasure lborel S"
    and finite: "emeasure lborel S < \<infinity>"
    and regular: "emeasure lborel (closure S) = emeasure lborel S"
    and opn: "open S"
  assumes int: "(f has_integral 0) (closure S)"
  assumes x: "x \<in> closure S"
  shows "f x = 0"
proof -
  have zero: "emeasure lborel (frontier S) = 0"
    using finite closure_subset regular
    unfolding frontier_def
    by (subst emeasure_Diff) (auto simp: frontier_def interior_open \<open>open S\<close> )
  have nonneg: "0 \<le> f x" if "x \<in> closure S" for x
    using continuous_ge_on_closure[OF f that nonneg_interior] by simp
  have "0 = integral (closure S) f"
    by (blast intro: int sym)
  also
  note intl = has_integral_integrable[OF int]
  have af: "f absolutely_integrable_on (closure S)"
    using nonneg
    by (intro absolutely_integrable_onI intl integrable_eq[OF intl]) simp
  then have "integral (closure S) f = set_lebesgue_integral lebesgue (closure S) f"
    by (intro set_lebesgue_integral_eq_integral(2)[symmetric])
  also have "\<dots> = 0 \<longleftrightarrow> (AE x in lebesgue. indicator (closure S) x *\<^sub>R f x = 0)"
    unfolding set_lebesgue_integral_def
  proof (rule integral_nonneg_eq_0_iff_AE)
    show "integrable lebesgue (\<lambda>x. indicat_real (closure S) x *\<^sub>R f x)"
      by (metis af set_integrable_def)
  qed (use nonneg in \<open>auto simp: indicator_def\<close>)
  also have "\<dots> \<longleftrightarrow> (AE x in lebesgue. x \<in> {x. x \<in> closure S \<longrightarrow> f x = 0})"
    by (auto simp: indicator_def)
  finally have "(AE x in lebesgue. x \<in> {x. x \<in> closure S \<longrightarrow> f x = 0})" by simp
  moreover have "(AE x in lebesgue. x \<in> - frontier S)"
    using zero
    by (auto simp: eventually_ae_filter null_sets_def intro!: exI[where x="frontier S"])
  ultimately have ae: "AE x \<in> S in lebesgue. x \<in> {x \<in> closure S. f x = 0}" (is ?th)
    by eventually_elim (use closure_subset in \<open>auto simp: \<close>)
  have "closed {0::real}" by simp
  with continuous_on_closed_vimage[OF closed_closure, of S f] f
  have "closed (f -` {0} \<inter> closure S)" by blast
  then have "closed {x \<in> closure S. f x = 0}" by (auto simp: vimage_def Int_def conj_commute)
  with \<open>open S\<close> have "x \<in> {x \<in> closure S. f x = 0}" if "x \<in> S" for x using ae that
    by (rule mem_closed_if_AE_lebesgue_open)
  then have "f x = 0" if "x \<in> S" for x using that by auto
  from continuous_constant_on_closure[OF f this \<open>x \<in> closure S\<close>]
  show "f x = 0" .
qed

lemma has_integral_0_cbox_imp_0:
  fixes f :: "'a::euclidean_space \<Rightarrow> real"
  assumes f: "continuous_on (cbox a b) f"
    and nonneg_interior: "\<And>x. x \<in> box a b \<Longrightarrow> 0 \<le> f x"
  assumes int: "(f has_integral 0) (cbox a b)"
  assumes ne: "box a b \<noteq> {}"
  assumes x: "x \<in> cbox a b"
  shows "f x = 0"
proof -
  have "0 < emeasure lborel (box a b)"
    using ne x unfolding emeasure_lborel_box_eq
    by (force intro!: prod_pos simp: mem_box algebra_simps)
  then show ?thesis using assms
    by (intro has_integral_0_closure_imp_0[of "box a b" f x])
      (auto simp: emeasure_lborel_box_eq emeasure_lborel_cbox_eq algebra_simps mem_box)
qed

subsection\<open>Various common equivalent forms of function measurability\<close>

lemma indicator_sum_eq:
  fixes m::real and f :: "'a \<Rightarrow> real"
  assumes "\<bar>m\<bar> \<le> 2 ^ (2*n)" "m/2^n \<le> f x" "f x < (m+1)/2^n" "m \<in> \<int>"
  shows   "(\<Sum>k::real | k \<in> \<int> \<and> \<bar>k\<bar> \<le> 2 ^ (2*n).
            k/2^n * indicator {y. k/2^n \<le> f y \<and> f y < (k+1)/2^n} x)  = m/2^n"
          (is "sum ?f ?S = _")
proof -
  have "sum ?f ?S = sum (\<lambda>k. k/2^n * indicator {y. k/2^n \<le> f y \<and> f y < (k+1)/2^n} x) {m}"
  proof (rule comm_monoid_add_class.sum.mono_neutral_right)
    show "finite ?S"
      by (rule finite_abs_int_segment)
    show "{m} \<subseteq> {k \<in> \<int>. \<bar>k\<bar> \<le> 2 ^ (2*n)}"
      using assms by auto
    show "\<forall>i\<in>{k \<in> \<int>. \<bar>k\<bar> \<le> 2 ^ (2*n)} - {m}. ?f i = 0"
      using assms by (auto simp: indicator_def Ints_def abs_le_iff divide_simps)
  qed
  also have "\<dots> = m/2^n"
    using assms by (auto simp: indicator_def not_less)
  finally show ?thesis .
qed

lemma measurable_on_sf_limit_lemma1:
  fixes f :: "'a::euclidean_space \<Rightarrow> real"
  assumes "\<And>a b. {x \<in> S. a \<le> f x \<and> f x < b} \<in> sets (lebesgue_on S)"
  obtains g where "\<And>n. g n \<in> borel_measurable (lebesgue_on S)"
                  "\<And>n. finite(range (g n))"
                  "\<And>x. (\<lambda>n. g n x) \<longlonglongrightarrow> f x"
proof
  show "(\<lambda>x. sum (\<lambda>k::real. k/2^n * indicator {y. k/2^n \<le> f y \<and> f y < (k+1)/2^n} x)
                 {k \<in> \<int>. \<bar>k\<bar> \<le> 2 ^ (2*n)}) \<in> borel_measurable (lebesgue_on S)"
        (is "?g \<in> _")  for n
  proof -
    have "\<And>k. \<lbrakk>k \<in> \<int>; \<bar>k\<bar> \<le> 2 ^ (2*n)\<rbrakk>
         \<Longrightarrow> Measurable.pred (lebesgue_on S) (\<lambda>x. k / (2^n) \<le> f x \<and> f x < (k+1) / (2^n))"
      using assms by (force simp: pred_def space_restrict_space)
    then show ?thesis
      by (simp add: field_class.field_divide_inverse)
  qed
  show "finite (range (?g n))" for n
  proof -
    have "range (?g n) \<subseteq> (\<lambda>k. k/2^n) ` {k \<in> \<int>. \<bar>k\<bar> \<le> 2 ^ (2*n)}"
    proof clarify
      fix x
      show "?g n x  \<in> (\<lambda>k. k/2^n) ` {k \<in> \<int>. \<bar>k\<bar> \<le> 2 ^ (2*n)}"
      proof (cases "\<exists>k::real. k \<in> \<int> \<and> \<bar>k\<bar> \<le> 2 ^ (2*n) \<and> k/2^n \<le> (f x) \<and> (f x) < (k+1)/2^n")
        case True
        then show ?thesis
          apply clarify
          by (subst indicator_sum_eq) auto
      next
        case False
        then have "?g n x = 0" by auto
        then show ?thesis by force
      qed
    qed
    moreover have "finite ((\<lambda>k::real. (k/2^n)) ` {k \<in> \<int>. \<bar>k\<bar> \<le> 2 ^ (2*n)})"
      by (simp add: finite_abs_int_segment)
    ultimately show ?thesis
      using finite_subset by blast
  qed
  show "(\<lambda>n. ?g n x) \<longlonglongrightarrow> f x" for x
  proof (rule LIMSEQ_I)
    fix e::real
    assume "e > 0"
    obtain N1 where N1: "\<bar>f x\<bar> < 2 ^ N1"
      using real_arch_pow by fastforce
    obtain N2 where N2: "(1/2) ^ N2 < e"
      using real_arch_pow_inv \<open>e > 0\<close> by force
    have "norm (?g n x - f x) < e" if n: "n \<ge> max N1 N2" for n
    proof -
      define m where "m \<equiv> floor(2^n * (f x))"
      have "1 \<le> \<bar>2^n\<bar> * e"
        using n N2 \<open>e > 0\<close> less_eq_real_def less_le_trans by (fastforce simp add: divide_simps)
      then have *: "\<lbrakk>x \<le> y; y < x + 1\<rbrakk> \<Longrightarrow> abs(x - y) < \<bar>2^n\<bar> * e" for x y::real
        by linarith
      have "\<bar>2^n\<bar> * \<bar>m/2^n - f x\<bar> = \<bar>2^n * (m/2^n - f x)\<bar>"
        by (simp add: abs_mult)
      also have "\<dots> = \<bar>real_of_int \<lfloor>2^n * f x\<rfloor> - f x * 2^n\<bar>"
        by (simp add: algebra_simps m_def)
      also have "\<dots> < \<bar>2^n\<bar> * e"
        by (rule *; simp add: mult.commute)
      finally have "\<bar>2^n\<bar> * \<bar>m/2^n - f x\<bar> < \<bar>2^n\<bar> * e" .
      then have me: "\<bar>m/2^n - f x\<bar> < e"
        by simp
      have "\<bar>real_of_int m\<bar> \<le> 2 ^ (2*n)"
      proof (cases "f x < 0")
        case True
        then have "-\<lfloor>f x\<rfloor> \<le> \<lfloor>(2::real) ^ N1\<rfloor>"
          using N1 le_floor_iff minus_le_iff by fastforce
        with n True have "\<bar>real_of_int\<lfloor>f x\<rfloor>\<bar> \<le> 2 ^ N1"
          by linarith
        also have "\<dots> \<le> 2^n"
          using n by (simp add: m_def)
        finally have "\<bar>real_of_int \<lfloor>f x\<rfloor>\<bar> * 2^n \<le> 2^n * 2^n"
          by simp
        moreover
        have "\<bar>real_of_int \<lfloor>2^n * f x\<rfloor>\<bar> \<le> \<bar>real_of_int \<lfloor>f x\<rfloor>\<bar> * 2^n"
        proof -
          have "\<bar>real_of_int \<lfloor>2^n * f x\<rfloor>\<bar> = - (real_of_int \<lfloor>2^n * f x\<rfloor>)"
            using True by (simp add: abs_if mult_less_0_iff)
          also have "\<dots> \<le> - (real_of_int (\<lfloor>(2::real) ^ n\<rfloor> * \<lfloor>f x\<rfloor>))"
            using le_mult_floor_Ints [of "(2::real)^n"] by simp
          also have "\<dots> \<le> \<bar>real_of_int \<lfloor>f x\<rfloor>\<bar> * 2^n"
            using True
            by simp
          finally show ?thesis .
        qed
        ultimately show ?thesis
          by (metis (no_types, hide_lams) m_def order_trans power2_eq_square power_even_eq)
      next
        case False
        with n N1 have "f x \<le> 2^n"
          by (simp add: not_less) (meson less_eq_real_def one_le_numeral order_trans power_increasing)
        moreover have "0 \<le> m"
          using False m_def by force
        ultimately show ?thesis
          by (metis abs_of_nonneg floor_mono le_floor_iff m_def of_int_0_le_iff power2_eq_square power_mult real_mult_le_cancel_iff1 zero_less_numeral mult.commute zero_less_power)
      qed
      then have "?g n x = m/2^n"
        by (rule indicator_sum_eq) (auto simp: m_def mult.commute divide_simps)
      then have "norm (?g n x - f x) = norm (m/2^n - f x)"
        by simp
      also have "\<dots> < e"
        by (simp add: me)
      finally show ?thesis .
    qed
    then show "\<exists>no. \<forall>n\<ge>no. norm (?g n x - f x) < e"
      by blast
  qed
qed


lemma borel_measurable_vimage_halfspace_component_lt:
     "f \<in> borel_measurable (lebesgue_on S) \<longleftrightarrow>
      (\<forall>a i. i \<in> Basis \<longrightarrow> {x \<in> S. f x \<bullet> i < a} \<in> sets (lebesgue_on S))"
  apply (rule trans [OF borel_measurable_iff_halfspace_less])
  apply (fastforce simp add: space_restrict_space)
  done

lemma borel_measurable_simple_function_limit:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  shows "f \<in> borel_measurable (lebesgue_on S) \<longleftrightarrow>
         (\<exists>g. (\<forall>n. (g n) \<in> borel_measurable (lebesgue_on S)) \<and>
              (\<forall>n. finite (range (g n))) \<and> (\<forall>x. (\<lambda>n. g n x) \<longlonglongrightarrow> f x))"
proof -
  have "\<exists>g. (\<forall>n. (g n) \<in> borel_measurable (lebesgue_on S)) \<and>
            (\<forall>n. finite (range (g n))) \<and> (\<forall>x. (\<lambda>n. g n x) \<longlonglongrightarrow> f x)"
       if f: "\<And>a i. i \<in> Basis \<Longrightarrow> {x \<in> S. f x \<bullet> i < a} \<in> sets (lebesgue_on S)"
  proof -
    have "\<exists>g. (\<forall>n. (g n) \<in> borel_measurable (lebesgue_on S)) \<and>
                  (\<forall>n. finite(image (g n) UNIV)) \<and>
                  (\<forall>x. ((\<lambda>n. g n x) \<longlonglongrightarrow> f x \<bullet> i))" if "i \<in> Basis" for i
    proof (rule measurable_on_sf_limit_lemma1 [of S "\<lambda>x. f x \<bullet> i"])
      show "{x \<in> S. a \<le> f x \<bullet> i \<and> f x \<bullet> i < b} \<in> sets (lebesgue_on S)" for a b
      proof -
        have "{x \<in> S. a \<le> f x \<bullet> i \<and> f x \<bullet> i < b} = {x \<in> S. f x \<bullet> i < b} - {x \<in> S. a > f x \<bullet> i}"
          by auto
        also have "\<dots> \<in> sets (lebesgue_on S)"
          using f that by blast
        finally show ?thesis .
      qed
    qed blast
    then obtain g where g:
          "\<And>i n. i \<in> Basis \<Longrightarrow> g i n \<in> borel_measurable (lebesgue_on S)"
          "\<And>i n. i \<in> Basis \<Longrightarrow> finite(range (g i n))"
          "\<And>i x. i \<in> Basis \<Longrightarrow> ((\<lambda>n. g i n x) \<longlonglongrightarrow> f x \<bullet> i)"
      by metis
    show ?thesis
    proof (intro conjI allI exI)
      show "(\<lambda>x. \<Sum>i\<in>Basis. g i n x *\<^sub>R i) \<in> borel_measurable (lebesgue_on S)" for n
        by (intro borel_measurable_sum borel_measurable_scaleR) (auto intro: g)
      show "finite (range (\<lambda>x. \<Sum>i\<in>Basis. g i n x *\<^sub>R i))" for n
      proof -
        have "range (\<lambda>x. \<Sum>i\<in>Basis. g i n x *\<^sub>R i) \<subseteq> (\<lambda>h. \<Sum>i\<in>Basis. h i *\<^sub>R i) ` PiE Basis (\<lambda>i. range (g i n))"
        proof clarify
          fix x
          show "(\<Sum>i\<in>Basis. g i n x *\<^sub>R i) \<in> (\<lambda>h. \<Sum>i\<in>Basis. h i *\<^sub>R i) ` (\<Pi>\<^sub>E i\<in>Basis. range (g i n))"
            by (rule_tac x="\<lambda>i\<in>Basis. g i n x" in image_eqI) auto
        qed
        moreover have "finite(PiE Basis (\<lambda>i. range (g i n)))"
          by (simp add: g finite_PiE)
        ultimately show ?thesis
          by (metis (mono_tags, lifting) finite_surj)
      qed
      show "(\<lambda>n. \<Sum>i\<in>Basis. g i n x *\<^sub>R i) \<longlonglongrightarrow> f x" for x
      proof -
        have "(\<lambda>n. \<Sum>i\<in>Basis. g i n x *\<^sub>R i) \<longlonglongrightarrow> (\<Sum>i\<in>Basis. (f x \<bullet> i) *\<^sub>R i)"
          by (auto intro!: tendsto_sum tendsto_scaleR g)
        moreover have "(\<Sum>i\<in>Basis. (f x \<bullet> i) *\<^sub>R i) = f x"
          using euclidean_representation by blast
        ultimately show ?thesis
          by metis
      qed
    qed
  qed
  moreover have "f \<in> borel_measurable (lebesgue_on S)"
              if meas_g: "\<And>n. g n \<in> borel_measurable (lebesgue_on S)"
                 and fin: "\<And>n. finite (range (g n))"
                 and to_f: "\<And>x. (\<lambda>n. g n x) \<longlonglongrightarrow> f x" for  g
    by (rule borel_measurable_LIMSEQ_metric [OF meas_g to_f])
  ultimately show ?thesis
    using borel_measurable_vimage_halfspace_component_lt by blast
qed

lemma borel_measurable_vimage_halfspace_component_ge:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  shows "f \<in> borel_measurable (lebesgue_on S) \<longleftrightarrow>
         (\<forall>a i. i \<in> Basis \<longrightarrow> {x \<in> S. f x \<bullet> i \<ge> a} \<in> sets (lebesgue_on S))"
  apply (rule trans [OF borel_measurable_iff_halfspace_ge])
  apply (fastforce simp add: space_restrict_space)
  done

lemma borel_measurable_vimage_halfspace_component_gt:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  shows "f \<in> borel_measurable (lebesgue_on S) \<longleftrightarrow>
         (\<forall>a i. i \<in> Basis \<longrightarrow> {x \<in> S. f x \<bullet> i > a} \<in> sets (lebesgue_on S))"
  apply (rule trans [OF borel_measurable_iff_halfspace_greater])
  apply (fastforce simp add: space_restrict_space)
  done

lemma borel_measurable_vimage_halfspace_component_le:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  shows "f \<in> borel_measurable (lebesgue_on S) \<longleftrightarrow>
         (\<forall>a i. i \<in> Basis \<longrightarrow> {x \<in> S. f x \<bullet> i \<le> a} \<in> sets (lebesgue_on S))"
  apply (rule trans [OF borel_measurable_iff_halfspace_le])
  apply (fastforce simp add: space_restrict_space)
  done

lemma
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  shows borel_measurable_vimage_open_interval:
         "f \<in> borel_measurable (lebesgue_on S) \<longleftrightarrow>
         (\<forall>a b. {x \<in> S. f x \<in> box a b} \<in> sets (lebesgue_on S))" (is ?thesis1)
   and borel_measurable_vimage_open:
         "f \<in> borel_measurable (lebesgue_on S) \<longleftrightarrow>
         (\<forall>T. open T \<longrightarrow> {x \<in> S. f x \<in> T} \<in> sets (lebesgue_on S))" (is ?thesis2)
proof -
  have "{x \<in> S. f x \<in> box a b} \<in> sets (lebesgue_on S)" if "f \<in> borel_measurable (lebesgue_on S)" for a b
  proof -
    have "S = S \<inter> space lebesgue"
      by simp
    then have "S \<inter> (f -` box a b) \<in> sets (lebesgue_on S)"
      by (metis (no_types) box_borel in_borel_measurable_borel inf_sup_aci(1) space_restrict_space that)
    then show ?thesis
      by (simp add: Collect_conj_eq vimage_def)
  qed
  moreover
  have "{x \<in> S. f x \<in> T} \<in> sets (lebesgue_on S)"
       if T: "\<And>a b. {x \<in> S. f x \<in> box a b} \<in> sets (lebesgue_on S)" "open T" for T
  proof -
    obtain \<D> where "countable \<D>" and \<D>: "\<And>X. X \<in> \<D> \<Longrightarrow> \<exists>a b. X = box a b" "\<Union>\<D> = T"
      using open_countable_Union_open_box that \<open>open T\<close> by metis
    then have eq: "{x \<in> S. f x \<in> T} = (\<Union>U \<in> \<D>. {x \<in> S. f x \<in> U})"
      by blast
    have "{x \<in> S. f x \<in> U} \<in> sets (lebesgue_on S)" if "U \<in> \<D>" for U
      using that T \<D> by blast
    then show ?thesis
      by (auto simp: eq intro: Sigma_Algebra.sets.countable_UN' [OF \<open>countable \<D>\<close>])
  qed
  moreover
  have eq: "{x \<in> S. f x \<bullet> i < a} = {x \<in> S. f x \<in> {y. y \<bullet> i < a}}" for i a
    by auto
  have "f \<in> borel_measurable (lebesgue_on S)"
    if "\<And>T. open T \<Longrightarrow> {x \<in> S. f x \<in> T} \<in> sets (lebesgue_on S)"
    by (metis (no_types) eq borel_measurable_vimage_halfspace_component_lt open_halfspace_component_lt that)
  ultimately show "?thesis1" "?thesis2"
    by blast+
qed


lemma borel_measurable_vimage_closed:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  shows "f \<in> borel_measurable (lebesgue_on S) \<longleftrightarrow>
         (\<forall>T. closed T \<longrightarrow> {x \<in> S. f x \<in> T} \<in> sets (lebesgue_on S))"
        (is "?lhs = ?rhs")
proof -
  have eq: "{x \<in> S. f x \<in> T} = S - {x \<in> S. f x \<in> (- T)}" for T
    by auto
  show ?thesis
    apply (simp add: borel_measurable_vimage_open, safe)
     apply (simp_all (no_asm) add: eq)
     apply (intro sets.Diff sets_lebesgue_on_refl, force simp: closed_open)
    apply (intro sets.Diff sets_lebesgue_on_refl, force simp: open_closed)
    done
qed

lemma borel_measurable_vimage_closed_interval:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  shows "f \<in> borel_measurable (lebesgue_on S) \<longleftrightarrow>
         (\<forall>a b. {x \<in> S. f x \<in> cbox a b} \<in> sets (lebesgue_on S))"
        (is "?lhs = ?rhs")
proof
  assume ?lhs then show ?rhs
    using borel_measurable_vimage_closed by blast
next
  assume RHS: ?rhs
  have "{x \<in> S. f x \<in> T} \<in> sets (lebesgue_on S)" if "open T" for T
  proof -
    obtain \<D> where "countable \<D>" and \<D>: "\<D> \<subseteq> Pow T" "\<And>X. X \<in> \<D> \<Longrightarrow> \<exists>a b. X = cbox a b" "\<Union>\<D> = T"
      using open_countable_Union_open_cbox that \<open>open T\<close> by metis
    then have eq: "{x \<in> S. f x \<in> T} = (\<Union>U \<in> \<D>. {x \<in> S. f x \<in> U})"
      by blast
    have "{x \<in> S. f x \<in> U} \<in> sets (lebesgue_on S)" if "U \<in> \<D>" for U
      using that \<D> by (metis RHS)
    then show ?thesis
      by (auto simp: eq intro: Sigma_Algebra.sets.countable_UN' [OF \<open>countable \<D>\<close>])
  qed
  then show ?lhs
    by (simp add: borel_measurable_vimage_open)
qed

lemma borel_measurable_UNIV_eq: "borel_measurable (lebesgue_on UNIV) = borel_measurable lebesgue"
  by auto

lemma borel_measurable_vimage_borel:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  shows "f \<in> borel_measurable (lebesgue_on S) \<longleftrightarrow>
         (\<forall>T. T \<in> sets borel \<longrightarrow> {x \<in> S. f x \<in> T} \<in> sets (lebesgue_on S))"
        (is "?lhs = ?rhs")
proof
  assume f: ?lhs
  then show ?rhs
    using measurable_sets [OF f]
      by (simp add: Collect_conj_eq inf_sup_aci(1) space_restrict_space vimage_def)
qed (simp add: borel_measurable_vimage_open_interval)

lemma lebesgue_measurable_vimage_borel:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  assumes "f \<in> borel_measurable lebesgue" "T \<in> sets borel"
  shows "{x. f x \<in> T} \<in> sets lebesgue"
  using assms borel_measurable_vimage_borel [of f UNIV] by auto

lemma borel_measurable_If_I:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  assumes f: "f \<in> borel_measurable (lebesgue_on S)" and S: "S \<in> sets lebesgue"
  shows "(\<lambda>x. if x \<in> S then f x else 0) \<in> borel_measurable lebesgue"
proof -
  have eq: "{x. x \<notin> S} \<union> {x. f x \<in> Y} = {x. x \<notin> S} \<union> {x. f x \<in> Y} \<inter> S" for Y
    by blast
  show ?thesis
  using f S
  apply (simp add: vimage_def in_borel_measurable_borel Ball_def)
  apply (elim all_forward imp_forward asm_rl)
  apply (simp only: Collect_conj_eq Collect_disj_eq imp_conv_disj eq)
  apply (auto simp: Compl_eq [symmetric] Compl_in_sets_lebesgue sets_restrict_space_iff)
  done
qed

lemma borel_measurable_If_D:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  assumes "(\<lambda>x. if x \<in> S then f x else 0) \<in> borel_measurable lebesgue"
  shows "f \<in> borel_measurable (lebesgue_on S)"
  using assms
  apply (simp add: in_borel_measurable_borel Ball_def)
  apply (elim all_forward imp_forward asm_rl)
  apply (force simp: space_restrict_space sets_restrict_space image_iff intro: rev_bexI)
  done

lemma borel_measurable_UNIV:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  assumes "S \<in> sets lebesgue"
  shows "(\<lambda>x. if x \<in> S then f x else 0) \<in> borel_measurable lebesgue \<longleftrightarrow> f \<in> borel_measurable (lebesgue_on S)"
  using assms borel_measurable_If_D borel_measurable_If_I by blast

lemma borel_measurable_lebesgue_preimage_borel:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  shows "f \<in> borel_measurable lebesgue \<longleftrightarrow>
         (\<forall>T. T \<in> sets borel \<longrightarrow> {x. f x \<in> T} \<in> sets lebesgue)"
  apply (intro iffI allI impI lebesgue_measurable_vimage_borel)
    apply (auto simp: in_borel_measurable_borel vimage_def)
  done

subsection\<open>More results on integrability\<close>

lemma integrable_on_all_intervals_UNIV:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::banach"
  assumes intf: "\<And>a b. f integrable_on cbox a b"
    and normf: "\<And>x. norm(f x) \<le> g x" and g: "g integrable_on UNIV"
  shows "f integrable_on UNIV"
proof -
have intg: "(\<forall>a b. g integrable_on cbox a b)"
    and gle_e: "\<forall>e>0. \<exists>B>0. \<forall>a b c d.
                    ball 0 B \<subseteq> cbox a b \<and> cbox a b \<subseteq> cbox c d \<longrightarrow>
                    \<bar>integral (cbox a b) g - integral (cbox c d) g\<bar>
                    < e"
    using g
    by (auto simp: integrable_alt_subset [of _ UNIV] intf)
  have le: "norm (integral (cbox a b) f - integral (cbox c d) f) \<le> \<bar>integral (cbox a b) g - integral (cbox c d) g\<bar>"
    if "cbox a b \<subseteq> cbox c d" for a b c d
  proof -
    have "norm (integral (cbox a b) f - integral (cbox c d) f) = norm (integral (cbox c d - cbox a b) f)"
      using intf that by (simp add: norm_minus_commute integral_setdiff)
    also have "\<dots> \<le> integral (cbox c d - cbox a b) g"
    proof (rule integral_norm_bound_integral [OF _ _ normf])
      show "f integrable_on cbox c d - cbox a b" "g integrable_on cbox c d - cbox a b"
        by (meson integrable_integral integrable_setdiff intf intg negligible_setdiff that)+
    qed
    also have "\<dots> = integral (cbox c d) g - integral (cbox a b) g"
      using intg that by (simp add: integral_setdiff)
    also have "\<dots> \<le> \<bar>integral (cbox a b) g - integral (cbox c d) g\<bar>"
      by simp
    finally show ?thesis .
  qed
  show ?thesis
    using gle_e
    apply (simp add: integrable_alt_subset [of _ UNIV] intf)
    apply (erule imp_forward all_forward ex_forward asm_rl)+
    by (meson not_less order_trans le)
qed

lemma integrable_on_all_intervals_integrable_bound:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::banach"
  assumes intf: "\<And>a b. (\<lambda>x. if x \<in> S then f x else 0) integrable_on cbox a b"
    and normf: "\<And>x. x \<in> S \<Longrightarrow> norm(f x) \<le> g x" and g: "g integrable_on S"
  shows "f integrable_on S"
  using integrable_on_all_intervals_UNIV [OF intf, of "(\<lambda>x. if x \<in> S then g x else 0)"]
  by (simp add: g integrable_restrict_UNIV normf)

lemma measurable_bounded_lemma:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  assumes f: "f \<in> borel_measurable lebesgue" and g: "g integrable_on cbox a b"
    and normf: "\<And>x. x \<in> cbox a b \<Longrightarrow> norm(f x) \<le> g x"
  shows "f integrable_on cbox a b"
proof -
  have "g absolutely_integrable_on cbox a b"
    by (metis (full_types) add_increasing g le_add_same_cancel1 nonnegative_absolutely_integrable_1 norm_ge_zero normf)
  then have "integrable (lebesgue_on (cbox a b)) g"
    by (simp add: integrable_restrict_space set_integrable_def)
  then have "integrable (lebesgue_on (cbox a b)) f"
  proof (rule Bochner_Integration.integrable_bound)
    show "AE x in lebesgue_on (cbox a b). norm (f x) \<le> norm (g x)"
      by (rule AE_I2) (auto intro: normf order_trans)
  qed (simp add: f measurable_restrict_space1)
  then show ?thesis
    by (simp add: integrable_on_lebesgue_on)
qed

proposition measurable_bounded_by_integrable_imp_integrable:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  assumes f: "f \<in> borel_measurable (lebesgue_on S)" and g: "g integrable_on S"
    and normf: "\<And>x. x \<in> S \<Longrightarrow> norm(f x) \<le> g x" and S: "S \<in> sets lebesgue"
  shows "f integrable_on S"
proof (rule integrable_on_all_intervals_integrable_bound [OF _ normf g])
  show "(\<lambda>x. if x \<in> S then f x else 0) integrable_on cbox a b" for a b
  proof (rule measurable_bounded_lemma)
    show "(\<lambda>x. if x \<in> S then f x else 0) \<in> borel_measurable lebesgue"
      by (simp add: S borel_measurable_UNIV f)
    show "(\<lambda>x. if x \<in> S then g x else 0) integrable_on cbox a b"
      by (simp add: g integrable_altD(1))
    show "norm (if x \<in> S then f x else 0) \<le> (if x \<in> S then g x else 0)" for x
      using normf by simp
  qed
qed

subsection\<open> Relation between Borel measurability and integrability.\<close>

lemma integrable_imp_measurable_weak:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  assumes "S \<in> sets lebesgue" "f integrable_on S"
  shows "f \<in> borel_measurable (lebesgue_on S)"
  by (metis (mono_tags, lifting) assms has_integral_implies_lebesgue_measurable borel_measurable_restrict_space_iff integrable_on_def sets.Int_space_eq2)

lemma integrable_imp_measurable:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  assumes "f integrable_on S"
  shows "f \<in> borel_measurable (lebesgue_on S)"
proof -
  have "(UNIV::'a set) \<in> sets lborel"
    by simp
  then show ?thesis
    using assms borel_measurable_If_D borel_measurable_UNIV_eq integrable_imp_measurable_weak integrable_restrict_UNIV by blast
qed

proposition negligible_differentiable_vimage:
  fixes f :: "'a \<Rightarrow> 'a::euclidean_space"
  assumes "negligible T"
    and f': "\<And>x. x \<in> S \<Longrightarrow> inj(f' x)"
    and derf: "\<And>x. x \<in> S \<Longrightarrow> (f has_derivative f' x) (at x within S)"
  shows "negligible {x \<in> S. f x \<in> T}"
proof -
  define U where
    "U \<equiv> \<lambda>n::nat. {x \<in> S. \<forall>y. y \<in> S \<and> norm(y - x) < 1/n
                     \<longrightarrow> norm(y - x) \<le> n * norm(f y - f x)}"
  have "negligible {x \<in> U n. f x \<in> T}" if "n > 0" for n
  proof (subst locally_negligible_alt, clarify)
    fix a
    assume a: "a \<in> U n" and fa: "f a \<in> T"
    define V where "V \<equiv> {x. x \<in> U n \<and> f x \<in> T} \<inter> ball a (1 / n / 2)"
    show "\<exists>V. openin (subtopology euclidean {x \<in> U n. f x \<in> T}) V \<and> a \<in> V \<and> negligible V"
    proof (intro exI conjI)
      have noxy: "norm(x - y) \<le> n * norm(f x - f y)" if "x \<in> V" "y \<in> V" for x y
        using that unfolding U_def V_def mem_Collect_eq Int_iff mem_ball dist_norm
        by (meson norm_triangle_half_r)
      then have "inj_on f V"
        by (force simp: inj_on_def)
      then obtain g where g: "\<And>x. x \<in> V \<Longrightarrow> g(f x) = x"
        by (metis inv_into_f_f)
      have "\<exists>T' B. open T' \<and> f x \<in> T' \<and>
                   (\<forall>y\<in>f ` V \<inter> T \<inter> T'. norm (g y - g (f x)) \<le> B * norm (y - f x))"
        if "f x \<in> T" "x \<in> V" for x
        apply (rule_tac x = "ball (f x) 1" in exI)
        using that noxy by (force simp: g)
      then have "negligible (g ` (f ` V \<inter> T))"
        by (force simp: \<open>negligible T\<close> negligible_Int intro!: negligible_locally_Lipschitz_image)
      moreover have "V \<subseteq> g ` (f ` V \<inter> T)"
        by (force simp: g image_iff V_def)
      ultimately show "negligible V"
        by (rule negligible_subset)
    qed (use a fa V_def that in auto)
  qed
  with negligible_countable_Union have "negligible (\<Union>n \<in> {0<..}. {x. x \<in> U n \<and> f x \<in> T})"
    by auto
  moreover have "{x \<in> S. f x \<in> T} \<subseteq> (\<Union>n \<in> {0<..}. {x. x \<in> U n \<and> f x \<in> T})"
  proof clarsimp
    fix x
    assume "x \<in> S" and "f x \<in> T"
    then obtain inj: "inj(f' x)" and der: "(f has_derivative f' x) (at x within S)"
      using assms by metis
    moreover have "linear(f' x)"
      and eps: "\<And>\<epsilon>. \<epsilon> > 0 \<Longrightarrow> \<exists>\<delta>>0. \<forall>y\<in>S. norm (y - x) < \<delta> \<longrightarrow>
                      norm (f y - f x - f' x (y - x)) \<le> \<epsilon> * norm (y - x)"
      using der by (auto simp: has_derivative_within_alt linear_linear)
    ultimately obtain g where "linear g" and g: "g \<circ> f' x = id"
      using linear_injective_left_inverse by metis
    then obtain B where "B > 0" and B: "\<And>z. B * norm z \<le> norm(f' x z)"
      using linear_invertible_bounded_below_pos \<open>linear (f' x)\<close> by blast
    then obtain i where "i \<noteq> 0" and i: "1 / real i < B"
      by (metis (full_types) inverse_eq_divide real_arch_invD)
    then obtain \<delta> where "\<delta> > 0"
         and \<delta>: "\<And>y. \<lbrakk>y\<in>S; norm (y - x) < \<delta>\<rbrakk> \<Longrightarrow>
                  norm (f y - f x - f' x (y - x)) \<le> (B - 1 / real i) * norm (y - x)"
      using eps [of "B - 1/i"] by auto
    then obtain j where "j \<noteq> 0" and j: "inverse (real j) < \<delta>"
      using real_arch_inverse by blast
    have "norm (y - x)/(max i j) \<le> norm (f y - f x)"
      if "y \<in> S" and less: "norm (y - x) < 1 / (max i j)" for y
    proof -
      have "1 / real (max i j) < \<delta>"
        using j \<open>j \<noteq> 0\<close> \<open>0 < \<delta>\<close>
        by (auto simp: divide_simps max_mult_distrib_left of_nat_max)
    then have "norm (y - x) < \<delta>"
      using less by linarith
    with \<delta> \<open>y \<in> S\<close> have le: "norm (f y - f x - f' x (y - x)) \<le> B * norm (y - x) - norm (y - x)/i"
      by (auto simp: algebra_simps)
    have *: "\<lbrakk>norm(f - f' - y) \<le> b - c; b \<le> norm y; d \<le> c\<rbrakk> \<Longrightarrow> d \<le> norm(f - f')"
      for b c d and y f f'::'a
      using norm_triangle_ineq3 [of "f - f'" y] by simp
    show ?thesis
      apply (rule * [OF le B])
      using \<open>i \<noteq> 0\<close> \<open>j \<noteq> 0\<close> by (simp add: divide_simps max_mult_distrib_left of_nat_max less_max_iff_disj)
  qed
  with \<open>x \<in> S\<close> \<open>i \<noteq> 0\<close> \<open>j \<noteq> 0\<close> show "\<exists>n\<in>{0<..}. x \<in> U n"
    by (rule_tac x="max i j" in bexI) (auto simp: field_simps U_def less_max_iff_disj)
qed
  ultimately show ?thesis
    by (rule negligible_subset)
qed

lemma absolutely_integrable_Un:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  assumes S: "f absolutely_integrable_on S" and T: "f absolutely_integrable_on T"
  shows "f absolutely_integrable_on (S \<union> T)"
proof -
  have [simp]: "{x. (if x \<in> A then f x else 0) \<noteq> 0} = {x \<in> A. f x \<noteq> 0}" for A
    by auto
  let ?ST = "{x \<in> S. f x \<noteq> 0} \<inter> {x \<in> T. f x \<noteq> 0}"
  have "?ST \<in> sets lebesgue"
  proof (rule Sigma_Algebra.sets.Int)
    have "f integrable_on S"
      using S absolutely_integrable_on_def by blast
    then have "(\<lambda>x. if x \<in> S then f x else 0) integrable_on UNIV"
      by (simp add: integrable_restrict_UNIV)
    then have borel: "(\<lambda>x. if x \<in> S then f x else 0) \<in> borel_measurable (lebesgue_on UNIV)"
      using integrable_imp_measurable borel_measurable_UNIV_eq by blast
    then show "{x \<in> S. f x \<noteq> 0} \<in> sets lebesgue"
      unfolding borel_measurable_vimage_open
      by (rule allE [where x = "-{0}"]) auto
  next
    have "f integrable_on T"
      using T absolutely_integrable_on_def by blast
    then have "(\<lambda>x. if x \<in> T then f x else 0) integrable_on UNIV"
      by (simp add: integrable_restrict_UNIV)
    then have borel: "(\<lambda>x. if x \<in> T then f x else 0) \<in> borel_measurable (lebesgue_on UNIV)"
      using integrable_imp_measurable borel_measurable_UNIV_eq by blast
    then show "{x \<in> T. f x \<noteq> 0} \<in> sets lebesgue"
      unfolding borel_measurable_vimage_open
      by (rule allE [where x = "-{0}"]) auto
  qed
  then have "f absolutely_integrable_on ?ST"
    by (rule set_integrable_subset [OF S]) auto
  then have Int: "(\<lambda>x. if x \<in> ?ST then f x else 0) absolutely_integrable_on UNIV"
    using absolutely_integrable_restrict_UNIV by blast
  have "(\<lambda>x. if x \<in> S then f x else 0) absolutely_integrable_on UNIV"
       "(\<lambda>x. if x \<in> T then f x else 0) absolutely_integrable_on UNIV"
    using S T absolutely_integrable_restrict_UNIV by blast+
  then have "(\<lambda>x. (if x \<in> S then f x else 0) + (if x \<in> T then f x else 0)) absolutely_integrable_on UNIV"
    by (rule absolutely_integrable_add)
  then have "(\<lambda>x. ((if x \<in> S then f x else 0) + (if x \<in> T then f x else 0)) - (if x \<in> ?ST then f x else 0)) absolutely_integrable_on UNIV"
    using Int by (rule absolutely_integrable_diff)
  then have "(\<lambda>x. if x \<in> S \<union> T then f x else 0) absolutely_integrable_on UNIV"
    by (rule absolutely_integrable_spike) (auto intro: empty_imp_negligible)
  then show ?thesis
    unfolding absolutely_integrable_restrict_UNIV .
qed




subsubsection\<open>Differentiability of inverse function (most basic form)\<close>

proposition has_derivative_inverse_within:
  fixes f :: "'a::real_normed_vector \<Rightarrow> 'b::euclidean_space"
  assumes der_f: "(f has_derivative f') (at a within S)"
    and cont_g: "continuous (at (f a) within f ` S) g"
    and "a \<in> S" "linear g'" and id: "g' \<circ> f' = id"
    and gf: "\<And>x. x \<in> S \<Longrightarrow> g(f x) = x"
  shows "(g has_derivative g') (at (f a) within f ` S)"
proof -
  have [simp]: "g' (f' x) = x" for x
    by (simp add: local.id pointfree_idE)
  have "bounded_linear f'"
    and f': "\<And>e. e>0 \<Longrightarrow> \<exists>d>0. \<forall>y\<in>S. norm (y - a) < d \<longrightarrow>
                        norm (f y - f a - f' (y - a)) \<le> e * norm (y - a)"
    using der_f by (auto simp: has_derivative_within_alt)
  obtain C where "C > 0" and C: "\<And>x. norm (g' x) \<le> C * norm x"
    using linear_bounded_pos [OF \<open>linear g'\<close>] by metis
  obtain B k where "B > 0" "k > 0"
    and Bk: "\<And>x. \<lbrakk>x \<in> S; norm(f x - f a) < k\<rbrakk> \<Longrightarrow> norm(x - a) \<le> B * norm(f x - f a)"
  proof -
    obtain B where "B > 0" and B: "\<And>x. B * norm x \<le> norm (f' x)"
      using linear_inj_bounded_below_pos [of f'] \<open>linear g'\<close> id der_f has_derivative_linear
        linear_invertible_bounded_below_pos by blast
    then obtain d where "d>0"
      and d: "\<And>y. \<lbrakk>y \<in> S; norm (y - a) < d\<rbrakk> \<Longrightarrow>
                    norm (f y - f a - f' (y - a)) \<le> B / 2 * norm (y - a)"
      using f' [of "B/2"] by auto
    then obtain e where "e > 0"
      and e: "\<And>x. \<lbrakk>x \<in> S; norm (f x - f a) < e\<rbrakk> \<Longrightarrow> norm (g (f x) - g (f a)) < d"
      using cont_g by (auto simp: continuous_within_eps_delta dist_norm)
    show thesis
    proof
      show "2/B > 0"
        using \<open>B > 0\<close> by simp
      show "norm (x - a) \<le> 2 / B * norm (f x - f a)"
        if "x \<in> S" "norm (f x - f a) < e" for x
      proof -
        have xa: "norm (x - a) < d"
          using e [OF that] gf by (simp add: \<open>a \<in> S\<close> that)
        have *: "\<lbrakk>norm(y - f') \<le> B / 2 * norm x; B * norm x \<le> norm f'\<rbrakk>
                 \<Longrightarrow> norm y \<ge> B / 2 * norm x" for y f'::'b and x::'a
          using norm_triangle_ineq3 [of y f'] by linarith
        show ?thesis
          using * [OF d [OF \<open>x \<in> S\<close> xa] B] \<open>B > 0\<close> by (simp add: field_simps)
      qed
    qed (use \<open>e > 0\<close> in auto)
  qed
  show ?thesis
    unfolding has_derivative_within_alt
  proof (intro conjI impI allI)
    show "bounded_linear g'"
      using \<open>linear g'\<close> by (simp add: linear_linear)
  next
    fix e :: "real"
    assume "e > 0"
    then obtain d where "d>0"
      and d: "\<And>y. \<lbrakk>y \<in> S; norm (y - a) < d\<rbrakk> \<Longrightarrow>
                    norm (f y - f a - f' (y - a)) \<le> e / (B * C) * norm (y - a)"
      using f' [of "e / (B * C)"] \<open>B > 0\<close> \<open>C > 0\<close> by auto
    have "norm (x - a - g' (f x - f a)) \<le> e * norm (f x - f a)"
      if "x \<in> S" and lt_k: "norm (f x - f a) < k" and lt_dB: "norm (f x - f a) < d/B" for x
    proof -
      have "norm (x - a) \<le> B * norm(f x - f a)"
        using Bk lt_k \<open>x \<in> S\<close> by blast
      also have "\<dots> < d"
        by (metis \<open>0 < B\<close> lt_dB mult.commute pos_less_divide_eq)
      finally have lt_d: "norm (x - a) < d" .
      have "norm (x - a - g' (f x - f a)) \<le> norm(g'(f x - f a - (f' (x - a))))"
        by (simp add: linear_diff [OF \<open>linear g'\<close>] norm_minus_commute)
      also have "\<dots> \<le> C * norm (f x - f a - f' (x - a))"
        using C by blast
      also have "\<dots> \<le> e * norm (f x - f a)"
      proof -
        have "norm (f x - f a - f' (x - a)) \<le> e / (B * C) * norm (x - a)"
          using d [OF \<open>x \<in> S\<close> lt_d] .
        also have "\<dots> \<le> (norm (f x - f a) * e) / C"
          using \<open>B > 0\<close> \<open>C > 0\<close> \<open>e > 0\<close> by (simp add: field_simps Bk lt_k \<open>x \<in> S\<close>)
        finally show ?thesis
          using \<open>C > 0\<close> by (simp add: field_simps)
      qed
    finally show ?thesis .
    qed
    then show "\<exists>d>0. \<forall>y\<in>f ` S.
               norm (y - f a) < d \<longrightarrow>
               norm (g y - g (f a) - g' (y - f a)) \<le> e * norm (y - f a)"
      apply (rule_tac x="min k (d / B)" in exI)
      using \<open>k > 0\<close> \<open>B > 0\<close> \<open>d > 0\<close> \<open>a \<in> S\<close> by (auto simp: gf)
  qed
qed

end
